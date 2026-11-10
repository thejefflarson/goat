//! The embedded profile's memory discipline (ADR 0026), checked with no board:
//! the heap is a fixed arena that never grows, and calls nest only so deep.
//! Running past either is a runtime trap that carries a message, never a
//! compiler panic. The suite also runs under WAMR (`tests/wamr.rs`).

#![allow(clippy::duplicate_mod)]

#[allow(dead_code)]
mod support;

use goat::Profile;
use goat_wasm::{EmbeddedLimits, HEAP_BUDGET_EXHAUSTED, STACK_OVERFLOW, emit_with_limits};
use support::execute;
use wasmtime::{Config, Engine, ExternType, Module};

const BUILD: &str = "build = program(n, acc) do \
                       if n < 1 then acc else build(n - 1, Link(n, acc)) done \
                     done ";
const DEEP: &str = "down = program(n) do if n < 1 then 0 else 1 + down(n - 1) done done ";

fn wasm_with(profile: Profile, limits: EmbeddedLimits, src: &str) -> Vec<u8> {
    let checked = goat_checker::check(src).expect("type-checks");
    let program = goat_mir::mono_for(&checked, profile).expect("monomorphizes");
    assert_eq!(goat_mir::verify(&program), Ok(()), "{src}");
    emit_with_limits(&program, limits).expect("emits")
}

fn limits(heap_bytes: u32, call_depth: u32) -> EmbeddedLimits {
    EmbeddedLimits {
        heap_bytes,
        call_depth,
    }
}

fn run_within(limits: EmbeddedLimits, src: &str) -> Result<goat_cli::Run, String> {
    execute(&wasm_with(Profile::Embedded, limits, src))
}

#[test]
fn a_program_within_its_heap_budget_runs_and_frees_everything() {
    let run = run_within(
        limits(8 << 10, 1024),
        &format!("{BUILD} length(build(100, []))"),
    )
    .expect("fits");
    assert_eq!(run.printed, ["100"]);
    assert_eq!(run.live_allocs, 0);
}

#[test]
fn a_program_past_its_heap_budget_traps_with_a_message() {
    let src = format!("{BUILD} length(build(10000, []))");
    let error = run_within(limits(8 << 10, 1024), &src)
        .err()
        .expect("traps");
    assert_eq!(error, format!("trap: {HEAP_BUDGET_EXHAUSTED}"));
}

#[test]
fn freed_blocks_are_reused_so_a_long_loop_fits_a_small_budget() {
    let src = "spin = program(n, r) do \
                 if n < 1 then r.x else spin(n - 1, {x: r.x + 1}) done \
               done spin(100000, {x: 0})";
    let run = run_within(limits(1 << 10, 1024), src).expect("reuses its blocks");
    assert_eq!(run.printed, ["100000"]);
    assert_eq!(run.live_allocs, 0);
}

#[test]
fn the_default_budget_is_declared_and_holds_a_modest_list() {
    let src = format!("{BUILD} length(build(1000, []))");
    let wasm = wasm_with(Profile::Embedded, EmbeddedLimits::default(), &src);
    assert_eq!(execute(&wasm).expect("fits").printed, ["1000"]);
}

#[test]
fn an_embedded_memory_has_a_fixed_size_and_a_desktop_memory_can_grow() {
    let memory = |profile| {
        let wasm = wasm_with(profile, EmbeddedLimits::default(), "1 + 1");
        let engine = Engine::new(Config::new().wasm_tail_call(true)).unwrap();
        let module = Module::new(&engine, &wasm).unwrap();
        let export = module.exports().find(|e| e.name() == "memory").unwrap();
        let ExternType::Memory(ty) = export.ty() else {
            panic!("memory is a memory");
        };
        (ty.minimum(), ty.maximum())
    };
    let (minimum, maximum) = memory(Profile::Embedded);
    assert_eq!(maximum, Some(minimum));
    assert_eq!(memory(Profile::Desktop).1, None);
}

#[test]
fn calls_nested_past_the_bound_trap_with_a_message() {
    let src = format!("{DEEP} print(down(100))");
    let error = run_within(limits(64 << 10, 50), &src).err().expect("traps");
    assert_eq!(error, format!("trap: {STACK_OVERFLOW}"));
    let run = run_within(limits(64 << 10, 150), &src).expect("fits");
    assert_eq!(run.printed, ["100"]);
}

#[test]
fn a_tail_call_does_not_count_against_the_bound() {
    let src = "loop = program(n) do if n < 1 then 7 else loop(n - 1) done done loop(1000000)";
    let run = run_within(limits(64 << 10, 4), src).expect("runs in constant depth");
    assert_eq!(run.printed, ["7"]);
}

#[test]
fn running_out_of_memory_names_a_range_of_the_source_under_wasmtime() {
    let src = format!("{BUILD} length(build(10000, []))");
    let wasm = wasm_with(Profile::Embedded, limits(8 << 10, 1024), &src);
    let stopped = if support::uses_wamr() {
        goat_wamr::run_to_end(&wasm, goat::NoHost)
            .expect("loads")
            .result
    } else {
        goat::native::run_to_end(&wasm, goat::NoHost)
            .expect("loads")
            .result
    };
    let stopped = stopped.expect_err("traps");
    assert_eq!(stopped.message, HEAP_BUDGET_EXHAUSTED);
    if !support::uses_wamr() {
        let (start, end) = stopped.site.expect("the trap names a range of the source");
        assert!(start < end && end <= src.len(), "{start}..{end}");
    }
}

#[test]
fn wasmtime_supports_custom_page_sizes_but_the_embedded_heap_does_not_use_them() {
    let mut memories = wasm_encoder::MemorySection::new();
    memories.memory(wasm_encoder::MemoryType {
        minimum: 64,
        maximum: Some(64),
        memory64: false,
        shared: false,
        page_size_log2: Some(0),
    });
    let mut module = wasm_encoder::Module::new();
    module.section(&memories);
    let bytes = module.finish();

    let default = Engine::new(&Config::new()).unwrap();
    assert!(Module::new(&default, &bytes).is_err());
    let mut config = Config::new();
    config.wasm_custom_page_sizes(true);
    let enabled = Engine::new(&config).unwrap();
    assert!(Module::new(&enabled, &bytes).is_ok());

    let wasm = wasm_with(Profile::Embedded, EmbeddedLimits::default(), "1 + 1");
    assert!(Module::new(&default, &wasm).is_ok());
}
