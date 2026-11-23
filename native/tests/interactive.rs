//! Interactive programs on the native backend (ADR 0015): the event
//! constructors, `draw` handing the host one `scene.frame` buffer per frame,
//! method sites and reload. Each program runs under wasmtime too, and the
//! scene (and the bytes of every frame) must be the same.

use goat::native::Interactive as Wasm;
use goat::{Boundary, Event, Host, HostInterface, HostValue, Reloaded, SceneCommand, SceneHost};
use goat_native::{Interactive, Library, build, clang_available};

macro_rules! need_clang {
    () => {
        if !clang_available() {
            eprintln!("skipping: clang is not available");
            return;
        }
    };
}

const EXAMPLE: &str = include_str!("../../examples/interactive.goat");
const SHAPES: &str = include_str!("../../examples/shapes.goat");
const ARROW_DRAW: &str = include_str!("../../examples/arrow_draw.goat");

fn library(source: &str) -> Library {
    build(goat::Profile::Desktop, source, &HostInterface::turtle())
        .unwrap_or_else(|e| panic!("{source}\n{e}"))
}

/// A host that keeps the raw bytes of each frame it is handed, as well as
/// replaying it into a scene.
struct Recording {
    inner: SceneHost,
    frames: Vec<Vec<u8>>,
}

impl Host for Recording {
    fn signature(&self, module: &str, name: &str) -> Option<(Vec<Boundary>, Boundary)> {
        self.inner.signature(module, name)
    }

    fn call(&mut self, module: &str, name: &str, args: &[HostValue]) -> Result<HostValue, String> {
        self.inner.call(module, name, args)
    }

    fn frame(&mut self, bytes: &[u8]) -> Result<(), String> {
        self.frames.push(bytes.to_vec());
        self.inner.frame(bytes)
    }
}

fn script() -> Vec<Event> {
    let keys = ["ArrowRight", "ArrowUp", "a", "ArrowLeft", "ArrowDown", ""];
    keys.iter()
        .flat_map(|k| [Event::Tick(16.0), Event::KeyDown(k.to_string())])
        .chain([
            Event::KeyUp("ArrowUp".into()),
            Event::PointerMove { x: 1.0, y: 2.0 },
        ])
        .collect()
}

fn on_native(source: &str, events: &[Event]) -> (Vec<SceneCommand>, u32) {
    let mut program: Interactive<SceneHost> =
        Interactive::new(library(source), SceneHost::default()).expect("starts");
    for event in events {
        if program.send(event).expect("event runs") {
            program.draw().expect("draw runs");
        }
    }
    let (sink, live) = program.finish().expect("tears down");
    (sink.commands, live)
}

fn on_wasm(source: &str, events: &[Event]) -> (Vec<SceneCommand>, u32) {
    let wasm = goat::compile_reloadable(source, &HostInterface::turtle()).expect("compiles");
    let mut program: Wasm<SceneHost> = Wasm::new(&wasm, SceneHost::default()).expect("starts");
    for event in events {
        if program.send(event).expect("event runs") {
            program.draw().expect("draw runs");
        }
    }
    let (sink, live) = program.finish().expect("tears down");
    (sink.commands, live)
}

#[test]
fn the_scene_matches_wasm_and_nothing_leaks() {
    need_clang!();
    for source in [EXAMPLE, SHAPES, ARROW_DRAW] {
        let native = on_native(source, &script());
        assert_eq!(native, on_wasm(source, &script()));
        assert_eq!(native.1, 0, "leaked");
        assert!(native.0.contains(&SceneCommand::Begin), "drew something");
    }
}

#[test]
fn each_draw_hands_the_host_one_frame_with_the_bytes_wasm_makes() {
    need_clang!();
    let frames = |native: bool| {
        let host = Recording {
            inner: SceneHost::default(),
            frames: Vec::new(),
        };
        if native {
            let mut guest = goat_native::Guest::new(library(SHAPES), host).unwrap();
            let model = guest.setup().unwrap();
            guest.draw(model).unwrap();
            guest.draw(model).unwrap();
            guest.release_model(model).unwrap();
            guest.shutdown().unwrap();
            assert_eq!(guest.live_allocs(), 0, "leaked");
            guest.into_host().frames
        } else {
            let wasm = goat::compile_reloadable(SHAPES, &HostInterface::turtle()).unwrap();
            let mut guest = goat::native::Guest::new(&wasm, host).unwrap();
            let model: i32 = guest.call("goat_setup", ()).unwrap();
            guest.call::<_, ()>("goat_draw", model).unwrap();
            guest.call::<_, ()>("goat_draw", model).unwrap();
            guest.call::<_, ()>("goat_release_model", model).unwrap();
            guest.call::<_, ()>("goat_shutdown", ()).unwrap();
            guest.into_host().frames
        }
    };
    let native = frames(true);
    assert_eq!(native.len(), 2, "one frame call per draw");
    assert_eq!(native, frames(false));
    assert_eq!(native[0][0], goat_mir::frame::VERSION);
}

#[test]
fn only_the_events_update_handles_are_subscribed() {
    need_clang!();
    let program: Interactive<SceneHost> =
        Interactive::new(library(EXAMPLE), SceneHost::default()).unwrap();
    let mut subscribed = program.subscriptions().to_vec();
    subscribed.sort();
    assert_eq!(subscribed, ["KeyDown", "Tick"]);
    let mut program = program;
    assert!(
        !program
            .send(&Event::PointerDown { x: 0.0, y: 0.0 })
            .unwrap()
    );
    program.finish().unwrap();
}

const METHODS: &str = r#"
init = {n: 0, bump: program(self) do {...self, n: self.n + 1} done}
update = program(model, event) do
  match event do Tick(dt) then model.bump() done
done
draw = program(model) do
  [Text({x: 0, y: 0, text: "n", color: "red"})]
done
"#;

fn reloaded(first: &str, second: &str) -> (Reloaded, SceneHost, u32) {
    let mut program: Interactive<SceneHost> =
        Interactive::new(library(first), SceneHost::default()).unwrap();
    program.send(&Event::Tick(16.0)).unwrap();
    program.draw().unwrap();
    let outcome = program.reload(library(second)).expect("reload runs");
    program.send(&Event::Tick(16.0)).unwrap();
    program.draw().unwrap();
    let (sink, live) = program.finish().unwrap();
    (outcome, sink, live)
}

#[test]
fn a_reload_keeps_the_model_and_rebinds_its_methods() {
    need_clang!();
    let changed = METHODS.replace("self.n + 1", "self.n + 10");
    let (outcome, sink, live) = reloaded(METHODS, &changed);
    assert_eq!(outcome, Reloaded::Refreshed);
    assert_eq!(live, 0, "leaked");
    assert_eq!(sink.commands.len(), 2 * 3);

    let wasm = |source: &str| goat::compile_reloadable(source, &HostInterface::turtle()).unwrap();
    let mut program: Wasm<SceneHost> = Wasm::new(&wasm(METHODS), SceneHost::default()).unwrap();
    program.send(&Event::Tick(16.0)).unwrap();
    program.draw().unwrap();
    assert_eq!(
        program.reload(&wasm(&changed)).unwrap(),
        Reloaded::Refreshed
    );
    program.send(&Event::Tick(16.0)).unwrap();
    program.draw().unwrap();
    assert_eq!(program.finish().unwrap().0.commands, sink.commands);
}

#[test]
fn a_reload_that_cannot_keep_the_model_says_why_and_restarts() {
    need_clang!();
    let reshaped = METHODS
        .replace("n: 0,", "n: \"zero\",")
        .replace("{...self, n: self.n + 1}", "self");
    let (outcome, _, live) = reloaded(METHODS, &reshaped);
    let Reloaded::Reset(reason) = outcome else {
        panic!("{outcome:?}");
    };
    assert_eq!(reason.kind, "type_changed");
    assert_eq!(reason.args, ["n", "Int", "String"]);
    assert_eq!(live, 0, "leaked");
}

#[test]
fn an_optimized_build_runs_and_counts_allocations() {
    need_clang!();
    let ll = goat::compile_ll(goat::Profile::Desktop, EXAMPLE, &HostInterface::turtle())
        .expect("compiles");
    let optimized = Library::build_with(&ll, &["-O2"]).expect("builds at -O2");
    let mut program: Interactive<SceneHost> =
        Interactive::new(optimized, SceneHost::default()).expect("starts");
    let setup = program.allocations();
    assert!(program.send(&Event::Tick(16.0)).expect("event runs"));
    program.draw().expect("draw runs");
    assert!(program.allocations() > setup);
    assert_eq!(program.finish().expect("tears down").1, 0);
}
