//! A Rust embedder's view: compile against a `HostInterface`, then run the
//! module through the native drivers.
#![cfg(feature = "native")]

use goat::native::{
    Boundary, Event, Host, HostValue, Interactive, Reloaded, SceneSink, run_to_end,
    run_to_end_within,
};
use goat::{HostInterface, compile};
use std::time::{Duration, Instant};

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

const SPIN: &str = "spin = program(n) do if n < 0 then n else spin(n + 1) done done\nspin(0)";

#[test]
fn a_run_once_program_that_never_ends_is_stopped_by_its_timeout() {
    let wasm = compile(SPIN, &HostInterface::with_stdlib("")).expect("compiles");
    let started = Instant::now();
    let finished = run_to_end_within(
        &wasm,
        goat::native::NoHost,
        Some(Duration::from_millis(100)),
    )
    .expect("instantiates");
    let message = finished.result.unwrap_err().message;
    assert!(message.contains("looks stuck"), "{message}");
    assert!(started.elapsed() < Duration::from_secs(10));
}

#[test]
fn a_timeout_does_not_disturb_a_program_that_finishes_in_time() {
    let wasm = compile("print(1 + 2)", &HostInterface::with_stdlib("")).expect("compiles");
    let finished = run_to_end_within(&wasm, goat::native::NoHost, Some(Duration::from_secs(60)))
        .expect("runs");
    assert_eq!(finished.printed, ["3"]);
    assert_eq!(finished.result, Ok(0));
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

/// Long enough that no ordinary call is near it; the runaway tests wait it out.
const RUNAWAY_LIMIT: Duration = Duration::from_millis(500);

fn interactive(source: &str) -> Interactive<Frames> {
    let wasm = goat::compile_turtle(source).expect("compiles");
    Interactive::with_timeout(&wasm, Frames::default(), RUNAWAY_LIMIT).expect("starts")
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

fn reloadable(source: &str) -> Vec<u8> {
    goat::compile_reloadable(source, &HostInterface::turtle()).expect("compiles")
}

fn live(source: &str) -> Interactive<Frames> {
    Interactive::with_timeout(&reloadable(source), Frames::default(), RUNAWAY_LIMIT)
        .expect("starts")
}

/// A model of a number, a string and a list, all on the heap. `step` is the
/// logic a reload can change without touching the model's layout; `extra` is a
/// model field that does.
fn counter(start: i32, step: i32, extra: &str) -> String {
    format!(
        r#"
init = {{x: {start}, color: "red", trail: [{{x: 0, y: 0}}, {{x: 5, y: 5}}]{extra}}}
update = program(model, event) do
  match event do
    Tick(dt) then {{...model, x: model.x + {step}, trail: Link({{x: model.x, y: 1}}, model.trail)}}
  done
done
draw = program(model) do
  [Line({{x1: 0, y1: 0, x2: model.x, y2: 0, color: model.color}}), Polyline({{points: model.trail, color: model.color}})]
done
"#
    )
}

fn tick(program: &mut Interactive<Frames>, times: usize) {
    for _ in 0..times {
        assert!(program.send(&Event::Tick(16.0)).unwrap());
    }
}

fn line_to(x: f64) -> Line {
    ((0.0, 0.0), (x, 0.0), "red".to_string())
}

#[test]
fn a_reload_with_the_same_model_layout_keeps_the_model_and_swaps_the_logic() {
    let mut program = live(&counter(0, 1, ""));
    tick(&mut program, 3);
    program.draw().unwrap();

    let reloaded = program.reload(&reloadable(&counter(100, 10, "")));
    assert_eq!(reloaded, Ok(Reloaded::Kept));
    tick(&mut program, 1);
    program.draw().unwrap();

    let (frames, live) = program.finish().expect("tears down");
    assert_eq!(live, 0, "leaked");
    assert_eq!(frames.lines, [line_to(3.0), line_to(13.0)]);
    // The two-point trail grew by one point per tick, across the reload.
    assert_eq!(frames.vertices, 5 + 6);
}

#[test]
fn a_reload_that_changes_the_model_layout_starts_over_from_the_new_init() {
    let mut program = live(&counter(0, 1, ""));
    tick(&mut program, 3);

    let reloaded = program.reload(&reloadable(&counter(7, 1, ", z: 0")));
    assert_eq!(reloaded, Ok(Reloaded::Reset));
    program.draw().unwrap();
    tick(&mut program, 1);
    program.draw().unwrap();

    let (frames, live) = program.finish().expect("tears down");
    assert_eq!(live, 0, "leaked");
    assert_eq!(frames.lines, [line_to(7.0), line_to(8.0)]);
    assert_eq!(frames.vertices, 2 + 3);
}

#[test]
fn nothing_leaks_across_many_reloads_of_either_kind() {
    let mut program = live(&counter(0, 1, ""));
    for round in 0..6 {
        tick(&mut program, 2);
        program.draw().unwrap();
        let extra = if round % 3 == 2 { ", z: 0" } else { "" };
        program
            .reload(&reloadable(&counter(0, round + 1, extra)))
            .unwrap();
    }
    program.draw().unwrap();
    let (_, live) = program.finish().expect("tears down");
    assert_eq!(live, 0, "leaked");
}

#[test]
fn a_reload_can_change_which_events_the_program_handles() {
    let ticks = counter(0, 1, "");
    let pointer = ticks.replace("Tick(dt)", "PointerDown(at)");
    let mut program = live(&ticks);
    assert_eq!(program.subscriptions(), ["Tick"]);
    assert_eq!(program.reload(&reloadable(&pointer)), Ok(Reloaded::Kept));
    assert_eq!(program.subscriptions(), ["PointerDown"]);
    assert!(!program.send(&Event::Tick(16.0)).unwrap());
    assert!(
        program
            .send(&Event::PointerDown { x: 1.0, y: 2.0 })
            .unwrap()
    );
    assert_eq!(program.finish().unwrap().1, 0);
}

#[test]
fn a_reload_that_renumbers_a_tag_inside_the_model_starts_over() {
    // Tags are numbered across the whole program in label order, so handling
    // `KeyDown`, which sorts before the list's `Link`, moves `Link`'s number.
    let ticks = counter(0, 1, "");
    let keys = ticks.replace("Tick(dt)", "KeyDown(key)");
    let mut program = live(&ticks);
    tick(&mut program, 2);
    assert_eq!(program.reload(&reloadable(&keys)), Ok(Reloaded::Reset));
    assert!(program.send(&Event::KeyDown("a".into())).unwrap());
    program.draw().unwrap();
    let (frames, live) = program.finish().unwrap();
    assert_eq!((frames.vertices, live), (3, 0));
}

#[test]
fn a_reload_rescues_a_program_the_runaway_update_stopped() {
    let mut program = live(SPINNING);
    assert!(program.send(&Event::Tick(16.0)).is_err());

    let fixed = counter(5, 1, "");
    assert_eq!(program.reload(&reloadable(&fixed)), Ok(Reloaded::Reset));
    tick(&mut program, 1);
    program.draw().unwrap();
    assert_eq!(program.into_sink().lines, [line_to(6.0)]);
}

#[test]
fn a_module_that_owns_its_memory_cannot_be_reloaded() {
    let owned = goat::compile_turtle(&counter(0, 1, "")).unwrap();
    let mut program = Interactive::new(&owned, Frames::default()).unwrap();
    assert!(program.reload(&reloadable(&counter(0, 2, ""))).is_err());

    let mut program = live(&counter(0, 1, ""));
    tick(&mut program, 1);
    assert!(program.reload(&owned).is_err());
    tick(&mut program, 1);
    program.draw().unwrap();
    let (frames, live) = program.finish().expect("the old program kept running");
    assert_eq!((frames.lines, live), ([line_to(2.0)].to_vec(), 0));
}

#[test]
fn only_an_interactive_program_can_be_compiled_reloadable() {
    let error = goat::compile_reloadable("print(1)", &HostInterface::turtle()).unwrap_err();
    assert!(error[0].message.contains("run-once"), "{error:?}");
}
