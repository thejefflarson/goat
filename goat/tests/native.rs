//! A Rust embedder's view: compile against a `HostInterface`, then run the
//! module through the native drivers.
#![cfg(feature = "native")]

use goat::native::{Boundary, Event, Host, HostValue, Interactive, SceneSink, run_to_end};
use goat::{HostInterface, compile};

#[derive(Default)]
struct Synth {
    beeps: Vec<f64>,
}

impl Host for Synth {
    fn signature(&self, module: &str, name: &str) -> Option<(Vec<Boundary>, Boundary)> {
        match (module, name) {
            ("synth", "beep") => Some((vec![Boundary::Number], Boundary::Unit)),
            ("synth", "volume") => Some((vec![], Boundary::Number)),
            _ => None,
        }
    }

    fn call(&mut self, _: &str, name: &str, args: &[HostValue]) -> Result<HostValue, String> {
        match (name, args) {
            ("beep", [HostValue::Number(pitch)]) => {
                self.beeps.push(*pitch);
                Ok(HostValue::Unit)
            }
            ("volume", []) => Ok(HostValue::Number(0.5)),
            _ => Err(format!("bad call to synth.{name}")),
        }
    }
}

fn synth_interface() -> HostInterface {
    HostInterface::with_stdlib(
        "beep = foreign \"synth\" \"beep\" (Number) -> Unit\n\
         volume = foreign \"synth\" \"volume\" () -> Number\n",
    )
}

#[test]
fn a_run_once_program_prints_and_calls_the_host() {
    let wasm = compile(
        "print(\"hello\"); beep(volume() * 8); print(1 + 2)",
        &synth_interface(),
    )
    .expect("compiles");
    let finished = run_to_end(&wasm, Synth::default()).expect("runs");
    assert_eq!(finished.printed, ["hello", "3"]);
    assert_eq!(finished.host.beeps, [4.0]);
    assert_eq!(finished.result, Ok(0));
}

#[test]
fn a_trap_keeps_the_output_and_names_the_message() {
    let wasm = compile(
        "print(\"before\"); trap(\"boom\")",
        &HostInterface::with_stdlib(""),
    )
    .expect("compiles");
    let finished = run_to_end(&wasm, goat::native::NoHost).expect("instantiates");
    assert_eq!(finished.printed, ["before"]);
    assert_eq!(finished.result.unwrap_err().message, "boom");
}

type Line = ((f64, f64), (f64, f64), String);

#[derive(Debug, Default, PartialEq)]
struct Frames {
    frames: usize,
    lines: Vec<Line>,
    vertices: usize,
}

impl SceneSink for Frames {
    fn begin(&mut self) {
        self.frames += 1;
    }

    fn end(&mut self) {}

    fn line(&mut self, from: (f64, f64), to: (f64, f64), color: &str) {
        self.lines.push((from, to, color.to_string()));
    }

    fn polyline_begin(&mut self, _: &str) {}

    fn vertex(&mut self, _: f64, _: f64) {
        self.vertices += 1;
    }

    fn polyline_end(&mut self) {}
}

fn interactive(source: &str) -> Interactive<Frames> {
    let wasm = goat::compile_turtle(source).expect("compiles");
    Interactive::new(&wasm, Frames::default()).expect("starts")
}

const EXAMPLE: &str = include_str!("../../examples/interactive.goat");

#[test]
fn an_interactive_program_draws_frames_for_the_events_it_handles() {
    let mut program = interactive(EXAMPLE);
    let mut subscriptions = program.subscriptions().to_vec();
    subscriptions.sort();
    assert_eq!(subscriptions, ["KeyDown", "Tick"]);

    assert!(program.send(&Event::KeyDown("ArrowRight".into())).unwrap());
    assert!(program.send(&Event::Tick(16.0)).unwrap());
    program.draw().unwrap();
    assert!(program.send(&Event::KeyDown("ArrowUp".into())).unwrap());
    program.draw().unwrap();

    let (frames, live) = program.finish().expect("tears down");
    assert_eq!(live, 0, "leaked");
    assert_eq!(frames.frames, 2);
    assert_eq!(
        frames.lines,
        [
            ((0.0, 0.0), (10.0, 0.0), "red".to_string()),
            ((0.0, 0.0), (10.0, -10.0), "red".to_string()),
        ]
    );
    assert_eq!(frames.vertices, 6);
}

#[test]
fn an_event_the_program_does_not_handle_is_ignored() {
    let mut program = interactive(EXAMPLE);
    let ignored = Event::PointerDown { x: 1.0, y: 2.0 };
    assert!(!program.send(&ignored).unwrap());
    program.draw().unwrap();
    let (frames, live) = program.finish().unwrap();
    assert_eq!((frames.frames, live), (1, 0));
}

const SPINNING: &str = r#"
init = {n: 0}
spin = program(n) do if n < 0 then n else spin(n + 1) done done
update = program(model, event) do
  match event do Tick(dt) then {n: spin(0)} done
done
draw = program(model) do [] done
"#;

#[test]
fn a_runaway_update_traps_as_stuck_and_stops_the_program() {
    let mut program = interactive(SPINNING);
    let error = program.send(&Event::Tick(16.0)).unwrap_err();
    assert!(error.contains("looks stuck"), "{error}");
    assert!(program.draw().is_err());
    assert!(program.send(&Event::Tick(16.0)).is_err());
    let frames = program.into_sink();
    assert_eq!(frames.frames, 0);
}

#[test]
fn a_color_outside_the_allowlist_traps_the_draw() {
    let source = r#"
init = {n: 0}
update = program(model, event) do match event do Tick(dt) then model done done
draw = program(model) do [Line({x1: 0, y1: 0, x2: 1, y2: 1, color: "red; drop"})] done
"#;
    let mut program = interactive(source);
    let error = program.draw().unwrap_err();
    assert!(error.contains("not a color name"), "{error}");
}
