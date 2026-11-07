//! The interactive export contract (ADR 0015): setup, update, draw, release and
//! shutdown, run on the MIR interpreter and on wasm, which must agree and leave
//! nothing allocated.

use goat_mir::{Interactive, NoHost, Program, Session, Value};
use wasmtime::{Config, Engine, Instance, Linker, Memory, Module, Store};

const EXAMPLE: &str = include_str!("../../examples/interactive.goat");

#[derive(Clone, Copy)]
enum Event {
    Tick,
    Step(f64),
}

const HEADER: usize = 8;
const SLOT: usize = 8;
const PAYLOAD: usize = 16;

fn script() -> Vec<Event> {
    (0..300)
        .map(|i| {
            if i % 3 == 0 {
                Event::Tick
            } else {
                Event::Step(i as f64 / 4.0 - 10.0)
            }
        })
        .collect()
}

fn program(source: &str) -> Program {
    let checked = goat_checker::check(source).expect("program type-checks");
    let program = goat_mir::mono(&checked).expect("program monomorphizes");
    assert_eq!(goat_mir::verify(&program), Ok(()));
    program
}

fn tag(interactive: &Interactive, label: &str) -> u32 {
    interactive.tags.iter().find(|(l, _)| l == label).unwrap().1
}

/// `(ticks, x)` after each event, from the interpreter, and the objects live
/// at the end.
fn interpreted(program: &Program) -> (Vec<(f64, f64)>, usize) {
    let mut host = NoHost;
    let (mut session, mut model) = Session::setup(program, &mut host).expect("setup runs");
    let number = |v: &Value| match v {
        Value::Float(x) => *x,
        other => panic!("not a number: {other:?}"),
    };
    let mut models = Vec::new();
    for event in script() {
        let event = match event {
            Event::Tick => session.variant("Tick", vec![]),
            Event::Step(dx) => session.variant("Step", vec![Value::Float(dx)]),
        }
        .unwrap();
        model = session.update(model, event).expect("update runs");
        session.draw(model).expect("draw runs");
        let fields = session.fields(model).unwrap();
        models.push((number(&fields[0]), number(&fields[1])));
    }
    session.release_model(model).unwrap();
    (models, session.shutdown().expect("shutdown runs"))
}

struct Wasm {
    store: Store<()>,
    instance: Instance,
    memory: Memory,
}

impl Wasm {
    fn new(program: &Program) -> Wasm {
        let wasm = goat_wasm::emit(program).expect("program emits");
        let mut config = Config::new();
        config.wasm_tail_call(true);
        let engine = Engine::new(&config).unwrap();
        let module = Module::new(&engine, &wasm).unwrap();
        let mut linker: Linker<()> = Linker::new(&engine);
        linker
            .func_wrap("goat", "print_number", |_: f64| {})
            .unwrap();
        linker.func_wrap("goat", "print_bool", |_: i32| {}).unwrap();
        let mut store = Store::new(&engine, ());
        let instance = linker.instantiate(&mut store, &module).unwrap();
        let memory = instance.get_memory(&mut store, "memory").unwrap();
        Wasm {
            store,
            instance,
            memory,
        }
    }

    fn call<P: wasmtime::WasmParams, R: wasmtime::WasmResults>(
        &mut self,
        name: &str,
        args: P,
    ) -> R {
        let func = self
            .instance
            .get_typed_func::<P, R>(&mut self.store, name)
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        func.call(&mut self.store, args)
            .unwrap_or_else(|e| panic!("{name} trapped: {e:#}"))
    }

    /// An event owned by the host (count 1), as `goat_update` consumes it.
    fn event(&mut self, tag: u32, step: Option<f64>) -> i32 {
        let size = if step.is_some() {
            PAYLOAD + SLOT
        } else {
            PAYLOAD
        };
        let ptr: i32 = self.call("goat_alloc", size as i32);
        let base = ptr as usize;
        self.memory
            .write(&mut self.store, base + HEADER, &tag.to_le_bytes())
            .unwrap();
        if let Some(dx) = step {
            self.memory
                .write(&mut self.store, base + PAYLOAD, &dx.to_le_bytes())
                .unwrap();
        }
        ptr
    }

    fn number(&mut self, model: i32, slot: usize) -> f64 {
        let mut bytes = [0; 8];
        let at = model as usize + HEADER + SLOT * slot;
        self.memory.read(&self.store, at, &mut bytes).unwrap();
        f64::from_le_bytes(bytes)
    }
}

fn compiled(program: &Program) -> (Vec<(f64, f64)>, u32) {
    let interactive = program.interactive.as_ref().unwrap();
    let (tick, step) = (tag(interactive, "Tick"), tag(interactive, "Step"));
    let mut wasm = Wasm::new(program);
    let mut model: i32 = wasm.call("goat_setup", ());
    let mut models = Vec::new();
    for event in script() {
        let event = match event {
            Event::Tick => wasm.event(tick, None),
            Event::Step(dx) => wasm.event(step, Some(dx)),
        };
        model = wasm.call("goat_update", (model, event));
        wasm.call::<_, ()>("goat_draw", model);
        models.push((wasm.number(model, 0), wasm.number(model, 1)));
    }
    wasm.call::<_, ()>("goat_release_model", model);
    wasm.call::<_, ()>("goat_shutdown", ());
    (models, wasm.call("goat_live_allocs", ()))
}

#[test]
fn the_model_survives_every_update_and_nothing_is_left_allocated() {
    let program = program(EXAMPLE);
    let (interp_models, interp_live) = interpreted(&program);
    let (wasm_models, wasm_live) = compiled(&program);

    let ticks = script().iter().filter(|e| matches!(e, Event::Tick)).count();
    let x: f64 = script()
        .iter()
        .map(|e| if let Event::Step(dx) = e { *dx } else { 0.0 })
        .sum();
    assert_eq!(interp_models.last(), Some(&(ticks as f64, x)));
    assert_eq!(wasm_models, interp_models);
    assert_eq!(interp_live, 0, "interpreter leaked");
    assert_eq!(wasm_live, 0, "wasm leaked");
}

#[test]
fn setup_hands_the_host_a_model_with_count_one() {
    let program = program(EXAMPLE);
    let mut wasm = Wasm::new(&program);
    let model: i32 = wasm.call("goat_setup", ());
    assert_eq!(wasm.number(model, 0), 0.0);
    wasm.call::<_, ()>("goat_draw", model);
    wasm.call::<_, ()>("goat_draw", model);
    wasm.call::<_, ()>("goat_release_model", model);
    wasm.call::<_, ()>("goat_shutdown", ());
    assert_eq!(wasm.call::<_, u32>("goat_live_allocs", ()), 0);
}

#[test]
fn an_interactive_module_exports_the_contract_and_not_an_entry() {
    let wasm = goat::compile(EXAMPLE).expect("compiles");
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
fn a_program_without_all_three_still_runs_once() {
    let src = "init = {x: 1}\ndraw = program(model) do [Circle(model.x)] done\nprint(init.x + 1)";
    let wasm = goat::compile(src).expect("compiles");
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
    let wasm = goat::compile(&src).expect("compiles");
    let run = goat_cli::run(&wasm).expect("runs");
    assert_eq!(run.printed, ["7"]);
}

fn export_names(wasm: &[u8]) -> Vec<String> {
    let engine = Engine::default();
    let module = Module::new(&engine, wasm).unwrap();
    module.exports().map(|e| e.name().to_string()).collect()
}
