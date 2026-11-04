//! The wasm allocator, driven through hand-built MIR (so a test can plant a
//! leak or a double free that well-typed source cannot express) and through
//! the exported `goat_alloc` / `goat_live_allocs`.

#[path = "../../mir/tests/common/mod.rs"]
mod common;

use common::*;
use goat_mir::*;
use wasmtime::{Config, Engine, Instance, Linker, Module, Store, StoreLimits, StoreLimitsBuilder};

const PAGE: usize = 65536;

struct State {
    printed: Vec<String>,
    limits: StoreLimits,
}

struct Running {
    store: Store<State>,
    instance: Instance,
}

fn instantiate(program: &Program, memory_limit: usize) -> Running {
    let wasm = goat_wasm::emit(program).expect("program emits");
    let mut config = Config::new();
    config.wasm_tail_call(true);
    let engine = Engine::new(&config).unwrap();
    let module = Module::new(&engine, &wasm).unwrap();
    let mut linker: Linker<State> = Linker::new(&engine);
    linker
        .func_wrap(
            "goat",
            "print_number",
            |mut c: wasmtime::Caller<'_, State>, x: f64| {
                c.data_mut().printed.push(goat::format_number(x));
            },
        )
        .unwrap();
    linker.func_wrap("goat", "print_bool", |_: i32| {}).unwrap();
    let limits = StoreLimitsBuilder::new().memory_size(memory_limit).build();
    let mut store = Store::new(
        &engine,
        State {
            printed: Vec::new(),
            limits,
        },
    );
    store.limiter(|state| &mut state.limits);
    let instance = linker.instantiate(&mut store, &module).unwrap();
    Running { store, instance }
}

impl Running {
    fn entry(&mut self) -> wasmtime::Result<()> {
        let entry = self
            .instance
            .get_typed_func::<(), ()>(&mut self.store, "goat_entry")?;
        entry.call(&mut self.store, ())
    }

    fn live(&mut self) -> u32 {
        let live = self
            .instance
            .get_typed_func::<(), u32>(&mut self.store, "goat_live_allocs")
            .unwrap();
        live.call(&mut self.store, ()).unwrap()
    }

    fn alloc(&mut self, size: u32) -> wasmtime::Result<u32> {
        let alloc = self
            .instance
            .get_typed_func::<u32, u32>(&mut self.store, "goat_alloc")?;
        alloc.call(&mut self.store, size)
    }

    fn word(&mut self, address: u32) -> u32 {
        let memory = self.instance.get_memory(&mut self.store, "memory").unwrap();
        let bytes = &memory.data(&self.store)[address as usize..][..4];
        u32::from_le_bytes(bytes.try_into().unwrap())
    }
}

/// `loop(n)` allocates a record and drops it, `n` times, in constant stack.
fn alloc_drop_loop(iterations: i64, drop_it: bool) -> Program {
    let release = if drop_it { drop_(1) } else { int(0) };
    let body = let_(
        1,
        alloc_record(7),
        let_(
            2,
            release,
            if_(
                cmp(CmpOp::Eq, local(0), int(0)),
                int(0),
                Expr::TailCall(Callee::Direct(FuncId(1)), vec![sub(local(0), int(1))]),
            ),
        ),
    );
    program(vec![
        func(MTy::Int, call(1, vec![int(iterations)])),
        func_with(vec![(0, MTy::Int)], MTy::Int, body),
    ])
}

#[test]
fn freed_blocks_are_reused_inside_a_single_page() {
    let mut run = instantiate(&alloc_drop_loop(100_000, true), PAGE);
    run.entry().expect("reclaimed blocks fit in one page");
    assert_eq!(run.live(), 0);
}

#[test]
fn without_the_drop_the_same_loop_exhausts_the_page() {
    let mut run = instantiate(&alloc_drop_loop(100_000, false), PAGE);
    assert!(run.entry().is_err());
}

#[test]
fn a_planted_leak_is_counted() {
    let p = program(vec![func(MTy::Int, let_(0, alloc_record(1), int(0)))]);
    let mut run = instantiate(&p, usize::MAX);
    run.entry().unwrap();
    assert_eq!(run.live(), 1);
}

#[test]
fn a_double_release_faults() {
    let body = let_(
        0,
        alloc_record(1),
        let_(1, drop_(0), let_(2, drop_(0), int(0))),
    );
    let mut run = instantiate(&program(vec![func(MTy::Int, body)]), usize::MAX);
    let error = run.entry().expect_err("second release must trap");
    assert!(
        format!("{error:?}").contains("unreachable"),
        "expected an unreachable trap, got {error:?}"
    );
}

#[test]
fn a_dangling_read_sees_poison() {
    let pair = LayoutId(2);
    let body = let_(
        0,
        Expr::AllocRecord(pair, vec![int(3), int(4)]),
        let_(1, drop_(0), Expr::Field(Local(0), 1)),
    );
    let mut p = program(vec![func(MTy::Int, body)]);
    p.layouts.push(Layout::Record(vec![MTy::Int, MTy::Int]));
    let mut run = instantiate(&p, usize::MAX);
    run.entry().unwrap();
    assert_eq!(run.store.data().printed, [(-0x01010102).to_string()]);
}

#[test]
fn goat_alloc_hands_out_distinct_owned_blocks() {
    let p = program(vec![func(MTy::Unit, Expr::Const(Const::Unit))]);
    let mut run = instantiate(&p, usize::MAX);
    let blocks: Vec<u32> = [0, 1, 24, 256, 257, 5000]
        .into_iter()
        .map(|size| run.alloc(size).unwrap())
        .collect();
    assert_eq!(run.live(), blocks.len() as u32);
    let mut sorted = blocks.clone();
    sorted.sort();
    sorted.dedup();
    assert_eq!(sorted.len(), blocks.len());
    for block in blocks {
        assert_eq!(block % 8, 0);
        assert_eq!(run.word(block), 1, "arrives with rc = 1");
    }
}

#[test]
fn goat_alloc_grows_memory_for_a_large_block_and_rejects_absurd_sizes() {
    let p = program(vec![func(MTy::Unit, Expr::Const(Const::Unit))]);
    let mut run = instantiate(&p, usize::MAX);
    let block = run.alloc(3 * PAGE as u32).unwrap();
    assert!(
        block as usize + 3 * PAGE
            <= run
                .instance
                .get_memory(&mut run.store, "memory")
                .unwrap()
                .data_size(&run.store)
    );
    assert!(run.alloc(u32::MAX).is_err());
}
