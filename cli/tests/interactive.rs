//! The interactive export contract (ADR 0015): setup, event constructors,
//! update, draw, release and shutdown, run on the MIR interpreter and on wasm.
//! The two must agree on the model after every event and on the scene `draw`
//! streams, command for command, and leave nothing allocated.

use goat_cli::Guest;
use goat_mir::{HeapKind, Layout, MTy, Program, SceneCommand, SceneHost, Session, Value};

const EXAMPLE: &str = include_str!("../../examples/interactive.goat");

const HEADER: usize = 8;
const SLOT: usize = 8;
const EVENTS: [&str; 6] = [
    "Tick",
    "KeyDown",
    "KeyUp",
    "PointerMove",
    "PointerDown",
    "PointerUp",
];

/// A pointer program that draws the path the pointer has dragged and handles
/// no `Tick`.
const SKETCH: &str = r##"
init = {down: false, path: [{x: 0, y: 0}]}

update = program(model, event) do
  match event do
    PointerDown(p) then {down: true, path: [p]}
    PointerMove(p) then if model.down then {down: true, path: Link(p, model.path)} else model done
    PointerUp(p) then {down: false, path: model.path}
  done
done

draw = program(model) do
  [Polyline({points: model.path, color: "#0a0"}), Line({x1: 0, y1: 0, x2: 1, y2: 1, color: "black"})]
done
"##;

#[derive(Clone, Debug)]
enum Event {
    Tick(f64),
    KeyDown(&'static str),
    KeyUp(&'static str),
    Pointer(&'static str, f64, f64),
}

impl Event {
    fn label(&self) -> String {
        match self {
            Event::Tick(_) => "Tick".into(),
            Event::KeyDown(_) => "KeyDown".into(),
            Event::KeyUp(_) => "KeyUp".into(),
            Event::Pointer(kind, ..) => format!("Pointer{kind}"),
        }
    }
}

fn example_script() -> Vec<Event> {
    let keys = [
        "ArrowRight",
        "ArrowRight",
        "ArrowUp",
        "a",
        "ArrowLeft",
        "ArrowDown",
        "ArrowUpp",
        "",
    ];
    keys.iter()
        .flat_map(|k| [Event::Tick(16.0), Event::KeyDown(k)])
        .chain([Event::KeyUp("ArrowUp")])
        .collect()
}

fn sketch_script() -> Vec<Event> {
    let at = |kind, x, y| Event::Pointer(kind, x, y);
    vec![
        at("Move", 5.0, 5.0),
        at("Down", 1.0, 2.0),
        at("Move", 3.0, 4.0),
        at("Move", 5.0, 6.0),
        at("Up", 7.0, 8.0),
        at("Move", 9.0, 9.0),
        at("Down", -1.0, -2.0),
    ]
}

fn program(source: &str) -> Program {
    let checked = goat_checker::check(source).expect("program type-checks");
    let program = goat_mir::mono(&checked).expect("program monomorphizes");
    assert_eq!(goat_mir::verify(&program), Ok(()));
    program
}

/// What one backend did with a script.
#[derive(Debug, PartialEq)]
struct Trace {
    /// The leading numeric fields of the model after each handled event.
    models: Vec<Vec<f64>>,
    /// Every `scene.*` call, in order.
    scene: Vec<SceneCommand>,
    live: usize,
}

/// Run `script` on the interpreter, skipping events `update` does not handle
/// (the host never sends one). `numbers` is how many leading model fields are
/// numbers to record.
fn interpreted(program: &Program, script: &[Event], numbers: usize) -> Trace {
    let mut host = SceneHost::default();
    let (mut session, mut model) = Session::setup(program, &mut host).expect("setup runs");
    let mut models = Vec::new();
    let handled: Vec<&Event> = script
        .iter()
        .filter(|e| session.handles(&e.label()))
        .collect();
    for event in handled {
        let built = match event {
            Event::Tick(dt) => session.event("Tick", vec![Value::Float(*dt)]),
            Event::KeyDown(key) | Event::KeyUp(key) => {
                let key = session.string(key).expect("string allocates");
                session.event(&event.label(), vec![key])
            }
            Event::Pointer(_, x, y) => {
                session.event(&event.label(), vec![Value::Float(*x), Value::Float(*y)])
            }
        }
        .expect("event constructs");
        model = session.update(model, built).expect("update runs");
        session.draw(model).expect("draw runs");
        let fields = session.fields(model).unwrap();
        models.push(
            fields
                .iter()
                .take(numbers)
                .map(|v| match v {
                    Value::Float(x) => *x,
                    Value::Int(n) => *n as f64,
                    other => panic!("not a number: {other:?}"),
                })
                .collect(),
        );
    }
    session.release_model(model).unwrap();
    let live = session.shutdown().expect("shutdown runs");
    Trace {
        models,
        scene: host.commands,
        live,
    }
}

fn compiled(program: &Program, script: &[Event], numbers: usize) -> Trace {
    let wasm = goat_wasm::emit(program).expect("program emits");
    let mut guest = Guest::new(&wasm, SceneHost::default()).expect("module instantiates");
    let exports = guest.exports();
    let mut model: i32 = guest.call("goat_setup", ()).expect("setup runs");
    let slots = model_slots(program);
    let mut models = Vec::new();
    let handled = |e: &&Event| exports.contains(&format!("goat_event_{}", e.label()));
    for event in script.iter().filter(handled) {
        let name = format!("goat_event_{}", event.label());
        let built: i32 = match event {
            Event::Tick(dt) => guest.call(&name, *dt),
            Event::KeyDown(key) | Event::KeyUp(key) => {
                let key = guest.string(key).unwrap();
                guest.call(&name, key)
            }
            Event::Pointer(_, x, y) => guest.call(&name, (*x, *y)),
        }
        .expect("event constructs");
        model = guest
            .call("goat_update", (model, built))
            .expect("update runs");
        guest.call::<_, ()>("goat_draw", model).expect("draw runs");
        models.push(
            (0..numbers)
                .map(|i| number(&mut guest, model, i, slots[i]))
                .collect(),
        );
    }
    guest.call::<_, ()>("goat_release_model", model).unwrap();
    guest.call::<_, ()>("goat_shutdown", ()).unwrap();
    let live = guest.live_allocs().unwrap() as usize;
    Trace {
        models,
        scene: guest.into_host().commands,
        live,
    }
}

/// The type of each field of the model, in slot order.
fn model_slots(program: &Program) -> Vec<MTy> {
    let update = program.interactive.as_ref().expect("interactive").update;
    let MTy::Ptr(HeapKind::Record(layout)) = program.funcs[update.0 as usize].params[1].1 else {
        panic!("the model is a record");
    };
    match &program.layouts[layout.0 as usize] {
        Layout::Record(fields) => fields.clone(),
        Layout::Variant(_) => panic!("the model is a record"),
    }
}

fn number(guest: &mut Guest<SceneHost>, model: i32, slot: usize, ty: MTy) -> f64 {
    let bytes = guest
        .read(model as usize + HEADER + SLOT * slot, 8)
        .expect("model readable");
    let bytes = bytes.try_into().unwrap();
    match ty {
        MTy::Int => i64::from_le_bytes(bytes) as f64,
        _ => f64::from_le_bytes(bytes),
    }
}

fn export_names(wasm: &[u8]) -> Vec<String> {
    let engine = wasmtime::Engine::default();
    let module = wasmtime::Module::new(&engine, wasm).unwrap();
    module.exports().map(|e| e.name().to_string()).collect()
}

fn subscriptions(source: &str) -> Vec<String> {
    let wasm = goat::compile_turtle(source).expect("compiles");
    let exports = export_names(&wasm);
    EVENTS
        .iter()
        .filter(|e| exports.contains(&format!("goat_event_{e}")))
        .map(|e| e.to_string())
        .collect()
}

#[test]
fn the_model_and_the_scene_agree_on_both_backends_and_nothing_leaks() {
    let program = program(EXAMPLE);
    let script = example_script();
    let interp = interpreted(&program, &script, 3);
    let wasm = compiled(&program, &script, 3);
    assert_eq!(wasm, interp);
    assert_eq!(interp.live, 0, "leaked");
}

#[test]
fn arrow_keys_reach_the_branch_that_matches_them() {
    let program = program(EXAMPLE);
    let script = [
        Event::KeyDown("ArrowRight"),
        Event::KeyDown("ArrowRight"),
        Event::KeyDown("ArrowUp"),
        Event::KeyDown("ArrowLeft"),
        Event::KeyDown("ArrowDown"),
        Event::KeyDown("a"),
        Event::KeyDown("ArrowUpp"),
        Event::KeyDown(""),
    ];
    let expected = [
        (10.0, 0.0),
        (20.0, 0.0),
        (20.0, -10.0),
        (10.0, -10.0),
        (10.0, 0.0),
        (10.0, 0.0),
        (10.0, 0.0),
        (10.0, 0.0),
    ];
    for trace in [
        interpreted(&program, &script, 3),
        compiled(&program, &script, 3),
    ] {
        let seen: Vec<(f64, f64)> = trace.models.iter().map(|m| (m[1], m[2])).collect();
        assert_eq!(seen, expected);
        assert_eq!(trace.live, 0);
    }
}

#[test]
fn the_picture_is_streamed_as_one_bracketed_frame_per_draw() {
    let program = program(EXAMPLE);
    let trace = interpreted(&program, &[Event::KeyDown("ArrowRight")], 3);
    use SceneCommand::*;
    assert_eq!(
        trace.scene,
        [
            Begin,
            Line {
                from: (0.0, 0.0),
                to: (10.0, 0.0),
                color: "red".into()
            },
            PolylineBegin("blue".into()),
            Vertex(0.0, 0.0),
            Vertex(10.0, 0.0),
            Vertex(10.0, 0.0),
            PolylineEnd,
            End,
        ]
    );
}

#[test]
fn a_polyline_grows_with_the_pointer_path_on_both_backends() {
    let program = program(SKETCH);
    let script = sketch_script();
    let interp = interpreted(&program, &script, 0);
    let wasm = compiled(&program, &script, 0);
    assert_eq!(wasm, interp);
    assert_eq!(interp.live, 0, "leaked");
    let frames = interp
        .scene
        .iter()
        .filter(|c| **c == SceneCommand::Begin)
        .count();
    assert_eq!(frames, script.len());
    let vertices = interp
        .scene
        .iter()
        .filter(|c| matches!(c, SceneCommand::Vertex(..)))
        .count();
    assert!(vertices > script.len(), "{vertices}");
}

#[test]
fn only_the_events_update_handles_are_exported() {
    assert_eq!(subscriptions(EXAMPLE), ["Tick", "KeyDown"]);
    assert_eq!(
        subscriptions(SKETCH),
        ["PointerMove", "PointerDown", "PointerUp"]
    );
    let key_only = EXAMPLE.replace("    Tick(dt) then {...model, ticks: model.ticks + 1}\n", "");
    assert_eq!(subscriptions(&key_only), ["KeyDown"]);
}

#[test]
fn an_else_arm_adds_no_subscription() {
    let source = r#"
init = {n: 0}
update = program(model, event) do
  match event do
    Tick(dt) then {n: model.n + 1}
  else model done
done
draw = program(model) do [] done
"#;
    assert_eq!(subscriptions(source), ["Tick"]);
}

#[test]
fn an_interactive_module_exports_the_contract_and_not_an_entry() {
    let wasm = goat::compile_turtle(EXAMPLE).expect("compiles");
    let exports = export_names(&wasm);
    for name in [
        "goat_setup",
        "goat_update",
        "goat_draw",
        "goat_release_model",
        "goat_shutdown",
        "goat_alloc",
        "goat_live_allocs",
        "memory",
    ] {
        assert!(exports.iter().any(|e| e == name), "{name} in {exports:?}");
    }
    assert!(!exports.iter().any(|e| e == "goat_entry"), "{exports:?}");
}

#[test]
fn setup_hands_the_host_a_model_with_count_one() {
    let wasm = goat::compile_turtle(EXAMPLE).expect("compiles");
    let mut guest = Guest::new(&wasm, SceneHost::default()).unwrap();
    let model: i32 = guest.call("goat_setup", ()).unwrap();
    assert_eq!(number(&mut guest, model, 1, MTy::Float), 0.0);
    guest.call::<_, ()>("goat_draw", model).unwrap();
    guest.call::<_, ()>("goat_draw", model).unwrap();
    guest.call::<_, ()>("goat_release_model", model).unwrap();
    guest.call::<_, ()>("goat_shutdown", ()).unwrap();
    assert_eq!(guest.live_allocs().unwrap(), 0);
    assert_eq!(guest.into_host().commands.len(), 2 * 8);
}

const TOO_MANY_POINTS: &str = r#"
init = {n: 100001}
update = program(model, event) do
  match event do Tick(dt) then model done
done
points = program(n, acc) do
  if n == 0 then acc else points(n - 1, Link({x: n, y: n}, acc)) done
done
draw = program(model) do
  [Polyline({points: points(model.n, []), color: "red"})]
done
"#;

#[test]
fn a_picture_past_the_per_frame_cap_traps() {
    let program = program(TOO_MANY_POINTS);
    let mut host = SceneHost::default();
    let (mut session, model) = Session::setup(&program, &mut host).unwrap();
    let error = session.draw(model).expect_err("draw should trap");
    assert!(
        format!("{error:?}").contains("too many shapes"),
        "{error:?}"
    );

    let wasm = goat_wasm::emit(&program).unwrap();
    let mut guest = Guest::new(&wasm, SceneHost::default()).unwrap();
    let model: i32 = guest.call("goat_setup", ()).unwrap();
    let error = guest.call::<_, ()>("goat_draw", model).unwrap_err();
    assert!(error.contains("trapped"), "{error}");
}

#[test]
fn a_color_outside_the_allowlist_traps() {
    let source = SKETCH.replace("#0a0", "red; alert(1)");
    let program = program(&source);
    let wasm = goat_wasm::emit(&program).unwrap();
    let mut guest = Guest::new(&wasm, SceneHost::default()).unwrap();
    let model: i32 = guest.call("goat_setup", ()).unwrap();
    let error = guest.call::<_, ()>("goat_draw", model).unwrap_err();
    assert!(error.contains("trapped"), "{error}");
}

#[test]
fn a_program_without_all_three_still_runs_once() {
    let src = "init = {x: 1}\ndraw = program(model) do [] done\nprint(init.x + 1)";
    let wasm = goat::compile_turtle(src).expect("compiles");
    let exports = export_names(&wasm);
    assert!(exports.iter().any(|e| e == "goat_entry"), "{exports:?}");
    assert!(!exports.iter().any(|e| e == "goat_setup"), "{exports:?}");
    let run = goat_cli::run(&wasm).expect("runs");
    assert_eq!(run.printed, ["2"]);
    assert_eq!(run.live_allocs, 0);
}

#[test]
fn rebinding_a_contract_name_reverts_to_running_once() {
    let src = format!("{EXAMPLE}\ninit = 7\nprint(init)\n");
    let wasm = goat::compile_turtle(&src).expect("compiles");
    let run = goat_cli::run(&wasm).expect("runs");
    assert_eq!(run.printed, ["7"]);
}

const ARROW_DRAW: &str = include_str!("../../examples/arrow_draw.goat");

fn polylines(scene: &[SceneCommand]) -> Vec<Vec<(f64, f64)>> {
    let mut frames = Vec::new();
    for command in scene {
        match command {
            SceneCommand::Begin => frames.push(Vec::new()),
            SceneCommand::Vertex(x, y) => frames.last_mut().unwrap().push((*x, *y)),
            _ => {}
        }
    }
    frames
}

#[test]
fn arrow_draw_accumulates_a_trail_on_both_backends_and_nothing_leaks() {
    let program = program(ARROW_DRAW);
    let script = [
        Event::KeyDown("ArrowRight"),
        Event::KeyDown("ArrowUp"),
        Event::KeyDown("x"),
        Event::KeyDown("ArrowLeft"),
        Event::KeyDown("ArrowDown"),
    ];
    let interp = interpreted(&program, &script, 0);
    let wasm = compiled(&program, &script, 0);
    assert_eq!(wasm, interp);
    assert_eq!(interp.live, 0, "leaked");
    let frames = polylines(&interp.scene);
    assert_eq!(frames.len(), script.len());
    assert_eq!(frames[0], [(10.0, 0.0), (0.0, 0.0)]);
    assert_eq!(
        frames[4],
        [
            (0.0, 0.0),
            (0.0, -10.0),
            (10.0, -10.0),
            (10.0, 0.0),
            (0.0, 0.0)
        ]
    );
}

#[test]
fn arrow_draw_subscribes_to_key_presses_only() {
    assert_eq!(subscriptions(ARROW_DRAW), ["KeyDown"]);
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
fn an_update_that_never_returns_runs_out_of_fuel_and_traps() {
    let wasm = goat::compile_turtle(SPINNING).expect("compiles");
    let mut guest = Guest::new(&wasm, SceneHost::default()).unwrap();
    let model: i32 = guest.call("goat_setup", ()).unwrap();
    guest.set_fuel(100_000).unwrap();
    let tick: i32 = guest.call("goat_event_Tick", 16.0f64).unwrap();
    let error = guest
        .call::<_, i32>("goat_update", (model, tick))
        .expect_err("a runaway update must trap, not hang");
    assert!(error.contains("trapped"), "{error}");
}

#[test]
fn an_interactive_module_starts_with_one_updates_worth_of_fuel() {
    let wasm = goat::compile_turtle(SPINNING).expect("compiles");
    let mut guest = Guest::new(&wasm, SceneHost::default()).unwrap();
    assert_eq!(guest.fuel().unwrap(), goat::native::UPDATE_FUEL);
}

#[test]
fn a_run_once_module_starts_with_more_fuel_than_an_update_gets() {
    let wasm = goat::compile_turtle("1").expect("compiles");
    let mut guest = Guest::new(&wasm, SceneHost::default()).unwrap();
    assert!(guest.fuel().unwrap() > goat::native::UPDATE_FUEL);
}

fn press(guest: &mut Guest<SceneHost>, model: i32, key: &str) -> Result<i32, String> {
    let key = guest.string(key)?;
    let event: i32 = guest.call("goat_event_KeyDown", key)?;
    guest.call("goat_update", (model, event))
}

#[test]
fn refilled_fuel_lets_ordinary_updates_run_many_times() {
    let wasm = goat::compile_turtle(ARROW_DRAW).expect("compiles");
    let mut guest = Guest::new(&wasm, SceneHost::default()).unwrap();
    let mut model: i32 = guest.call("goat_setup", ()).unwrap();
    for _ in 0..2_000 {
        guest.set_fuel(10_000).unwrap();
        model = press(&mut guest, model, "ArrowRight").unwrap();
    }
    guest.call::<_, ()>("goat_release_model", model).unwrap();
    guest.call::<_, ()>("goat_shutdown", ()).unwrap();
    assert_eq!(guest.live_allocs().unwrap(), 0);
}

#[test]
fn fuel_that_is_never_refilled_runs_out() {
    let wasm = goat::compile_turtle(ARROW_DRAW).expect("compiles");
    let mut guest = Guest::new(&wasm, SceneHost::default()).unwrap();
    let mut model: i32 = guest.call("goat_setup", ()).unwrap();
    guest.set_fuel(200).unwrap();
    let outcome = (0..2_000).try_for_each(|_| {
        model = press(&mut guest, model, "ArrowRight")?;
        Ok::<(), String>(())
    });
    assert!(outcome.is_err(), "fuel should be spent");
}

/// An all-scalar model, so a steady-state `update` allocates nothing but the
/// model's own cell, which it should reuse.
const COUNTER: &str = r##"
init = {x: 0, y: 0, n: 0}

update = program(model, event) do
  match event do
    KeyDown(key) then {...model, x: model.x + 1, n: model.n + 1}
  else model done
done

draw = program(model) do
  [Line({x1: 0, y1: 0, x2: model.x, y2: model.y, color: "black"})]
done
"##;

#[test]
fn update_reuses_the_models_cell_on_both_backends_and_nothing_leaks() {
    let program = program(COUNTER);
    let mut host = SceneHost::default();
    let (mut session, mut model) = Session::setup(&program, &mut host).expect("setup runs");
    let first = model;
    for _ in 0..50 {
        let key = session.string("a").expect("string allocates");
        let event = session
            .event("KeyDown", vec![key])
            .expect("event constructs");
        model = session.update(model, event).expect("update runs");
        assert_eq!(model, first, "interpreter allocated a fresh model");
    }
    assert_eq!(session.fields(model).unwrap()[0], Value::Int(50));
    session.release_model(model).unwrap();
    assert_eq!(session.shutdown().unwrap(), 0, "interpreter leaked");

    let wasm = goat_wasm::emit(&program).expect("program emits");
    let mut guest = Guest::new(&wasm, SceneHost::default()).expect("module instantiates");
    let mut model: i32 = guest.call("goat_setup", ()).expect("setup runs");
    let first = model;
    for _ in 0..50 {
        model = press(&mut guest, model, "a").expect("update runs");
        assert_eq!(model, first, "wasm allocated a fresh model");
    }
    assert_eq!(number(&mut guest, model, 0, MTy::Int), 50.0);
    guest.call::<_, ()>("goat_release_model", model).unwrap();
    guest.call::<_, ()>("goat_shutdown", ()).unwrap();
    assert_eq!(guest.live_allocs().unwrap(), 0, "wasm leaked");
}
