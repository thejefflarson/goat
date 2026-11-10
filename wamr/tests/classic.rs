//! ADR 0025: the fast interpreter refuses a function past 32767 cells at load,
//! the classic interpreter runs it, and the driver picks the classic one for
//! such a module.

use goat_wamr::{FAST_INTERP_CELL_LIMIT, Interp, NoHost, interp_for, run, run_to_end_on};
use wasm_encoder::{
    CodeSection, ExportKind, ExportSection, Function, FunctionSection, Instruction, Module,
    TypeSection, ValType,
};

/// `goat_live_allocs` calls a function with `locals` i32 locals, stores 7 in
/// the last one, and returns it, so the driver reports 7.
fn module(locals: u32) -> Vec<u8> {
    let mut types = TypeSection::new();
    types.ty().function([], [ValType::I32]);
    types.ty().function([], []);

    let mut functions = FunctionSection::new();
    for ty in [0, 0, 1] {
        functions.function(ty);
    }

    let mut exports = ExportSection::new();
    exports.export("goat_live_allocs", ExportKind::Func, 1);
    exports.export("goat_entry", ExportKind::Func, 2);

    let mut code = CodeSection::new();
    let mut wide = Function::new([(locals, ValType::I32)]);
    wide.instruction(&Instruction::I32Const(7))
        .instruction(&Instruction::LocalSet(locals - 1))
        .instruction(&Instruction::LocalGet(locals - 1))
        .instruction(&Instruction::End);
    code.function(&wide);
    let mut live = Function::new([]);
    live.instruction(&Instruction::Call(0))
        .instruction(&Instruction::End);
    code.function(&live);
    let mut entry = Function::new([]);
    entry.instruction(&Instruction::End);
    code.function(&entry);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&exports)
        .section(&code);
    module.finish()
}

#[test]
fn a_module_within_the_cell_limit_runs_on_the_fast_interpreter() {
    let wasm = module(100);
    assert_eq!(interp_for(&wasm), Ok(Interp::Fast));
    assert_eq!(run(&wasm).expect("runs").live_allocs, 7);
}

#[test]
fn a_function_past_the_cell_limit_does_not_load_on_the_fast_interpreter() {
    let wasm = module(FAST_INTERP_CELL_LIMIT + 1000);
    let refused = run_to_end_on(Interp::Fast, &wasm, NoHost)
        .err()
        .expect("the fast interpreter refuses it");
    assert!(refused.contains("invalid module"), "{refused}");
}

#[test]
fn the_driver_runs_an_oversized_function_on_the_classic_interpreter() {
    let wasm = module(FAST_INTERP_CELL_LIMIT + 1000);
    assert_eq!(interp_for(&wasm), Ok(Interp::Classic));
    assert_eq!(run(&wasm).expect("runs").live_allocs, 7);
    let classic = run_to_end_on(Interp::Classic, &wasm, NoHost).expect("loads");
    assert_eq!(classic.result.map_err(|s| s.message), Ok(7));
}

#[test]
fn the_classic_interpreter_agrees_with_the_fast_one_within_the_limit() {
    let wasm = module(100);
    for interp in [Interp::Fast, Interp::Classic] {
        let finished = run_to_end_on(interp, &wasm, NoHost).expect("loads");
        assert_eq!(finished.result.map_err(|s| s.message), Ok(7), "{interp:?}");
    }
}
