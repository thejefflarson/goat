//! WAMR 2.4.5 does not implement the custom-page-sizes proposal, so the
//! embedded heap sizes a default 64 KiB-page memory instead (ADR 0026). If a
//! WAMR upgrade starts loading these modules, this test fails and the decision
//! is due for another look.

use goat_wamr::{Interp, NoHost, run_to_end_on};
use wasm_encoder::{
    CodeSection, ExportKind, ExportSection, Function, FunctionSection, Instruction, MemorySection,
    MemoryType, Module, TypeSection, ValType,
};

fn module(page_size_log2: Option<u32>) -> Vec<u8> {
    let mut types = TypeSection::new();
    types.ty().function([], [ValType::I32]);
    types.ty().function([], []);
    let mut functions = FunctionSection::new();
    functions.function(0);
    functions.function(1);
    let mut memories = MemorySection::new();
    memories.memory(MemoryType {
        minimum: 64,
        maximum: Some(64),
        memory64: false,
        shared: false,
        page_size_log2,
    });
    let mut exports = ExportSection::new();
    exports.export("goat_live_allocs", ExportKind::Func, 0);
    exports.export("goat_entry", ExportKind::Func, 1);
    let mut code = CodeSection::new();
    let mut live = Function::new([]);
    live.instruction(&Instruction::I32Const(0))
        .instruction(&Instruction::End);
    code.function(&live);
    let mut entry = Function::new([]);
    entry.instruction(&Instruction::End);
    code.function(&entry);
    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memories)
        .section(&exports)
        .section(&code);
    module.finish()
}

#[test]
fn the_default_page_size_loads_on_both_interpreters() {
    for interp in [Interp::Fast, Interp::Classic] {
        let finished = run_to_end_on(interp, &module(None), NoHost).expect("loads");
        assert_eq!(finished.result.map_err(|s| s.message), Ok(0), "{interp:?}");
    }
}

#[test]
fn a_custom_page_size_is_refused_on_both_interpreters() {
    for interp in [Interp::Fast, Interp::Classic] {
        let refused = run_to_end_on(interp, &module(Some(0)), NoHost)
            .err()
            .expect("WAMR has no custom page sizes");
        assert!(refused.contains("invalid module"), "{interp:?}: {refused}");
    }
}
