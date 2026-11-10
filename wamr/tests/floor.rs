//! The runtime's feature floor (ADR 0019): a module that uses `return_call`,
//! `return_call_indirect`, or `memory.fill` does not load without its flag,
//! so each is exercised directly, apart from whatever goat emits.

use goat_wamr::{Interp, NoHost, run_to_end_on};
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, ElementSection, Elements, ExportKind, ExportSection,
    Function, FunctionSection, Instruction, MemArg, MemArgTarget, MemorySection, MemoryType,
    Module, RefType, TableSection, TableType, TypeSection, ValType,
};

/// Exports the driver's two entry points. `goat_live_allocs` counts a million
/// steps down through `return_call`, a million more through
/// `return_call_indirect`, then fills memory and reads a byte back, so the
/// number the driver reports as the live-allocation count is their sum.
fn module() -> Vec<u8> {
    let mut types = TypeSection::new();
    types.ty().function([ValType::I32], [ValType::I32]);
    types.ty().function([], [ValType::I32]);
    types.ty().function([], []);

    let mut functions = FunctionSection::new();
    for ty in [0, 0, 1, 2] {
        functions.function(ty);
    }

    let mut tables = TableSection::new();
    tables.table(TableType {
        element_type: RefType::FUNCREF,
        minimum: 1,
        maximum: Some(1),
        table64: false,
        shared: false,
    });

    let mut memories = MemorySection::new();
    memories.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    exports.export("goat_live_allocs", ExportKind::Func, 2);
    exports.export("goat_entry", ExportKind::Func, 3);

    let mut elements = ElementSection::new();
    elements.active(
        None,
        &ConstExpr::i32_const(0),
        Elements::Functions(vec![1].into()),
    );

    let mut code = CodeSection::new();

    // direct(n) = if n == 0 then 0 else return_call direct(n - 1)
    let mut direct = Function::new([]);
    direct
        .instruction(&Instruction::LocalGet(0))
        .instruction(&Instruction::I32Eqz)
        .instruction(&Instruction::If(BlockType::Result(ValType::I32)))
        .instruction(&Instruction::I32Const(0))
        .instruction(&Instruction::Else)
        .instruction(&Instruction::LocalGet(0))
        .instruction(&Instruction::I32Const(1))
        .instruction(&Instruction::I32Sub)
        .instruction(&Instruction::ReturnCall(0))
        .instruction(&Instruction::End)
        .instruction(&Instruction::End);
    code.function(&direct);

    // indirect(n) = if n == 0 then 7 else return_call_indirect table[0](n - 1)
    let mut indirect = Function::new([]);
    indirect
        .instruction(&Instruction::LocalGet(0))
        .instruction(&Instruction::I32Eqz)
        .instruction(&Instruction::If(BlockType::Result(ValType::I32)))
        .instruction(&Instruction::I32Const(7))
        .instruction(&Instruction::Else)
        .instruction(&Instruction::LocalGet(0))
        .instruction(&Instruction::I32Const(1))
        .instruction(&Instruction::I32Sub)
        .instruction(&Instruction::I32Const(0))
        .instruction(&Instruction::ReturnCallIndirect {
            type_index: 0,
            table_index: 0,
        })
        .instruction(&Instruction::End)
        .instruction(&Instruction::End);
    code.function(&indirect);

    // sum = direct(1e6) + indirect(1e6) + (memory.fill(0, 9, 4096); memory[100])
    let mut sum = Function::new([]);
    sum.instruction(&Instruction::I32Const(1_000_000))
        .instruction(&Instruction::Call(0))
        .instruction(&Instruction::I32Const(1_000_000))
        .instruction(&Instruction::Call(1))
        .instruction(&Instruction::I32Add)
        .instruction(&Instruction::I32Const(0))
        .instruction(&Instruction::I32Const(9))
        .instruction(&Instruction::I32Const(4096))
        .instruction(&Instruction::MemoryFill(0))
        .instruction(&Instruction::I32Const(100))
        .instruction(&Instruction::I32Load8U(MemArg {
            offset: 0,
            align: 0,
            target: MemArgTarget::Memory(0),
            ordering: None,
        }))
        .instruction(&Instruction::I32Add)
        .instruction(&Instruction::End);
    code.function(&sum);

    let mut nothing = Function::new([]);
    nothing.instruction(&Instruction::End);
    code.function(&nothing);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&tables)
        .section(&memories)
        .section(&exports)
        .section(&elements)
        .section(&code);
    module.finish()
}

#[test]
fn tail_calls_and_bulk_memory_run_in_constant_stack() {
    for interp in [Interp::Fast, Interp::Classic] {
        let finished = run_to_end_on(interp, &module(), NoHost).expect("module loads");
        let live = finished.result.map_err(|s| s.message);
        assert_eq!(live, Ok(7 + 9), "{interp:?}: indirect(0) + the filled byte");
    }
}
