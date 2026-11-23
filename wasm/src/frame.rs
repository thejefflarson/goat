//! The frame buffer (ADR 0015, second addendum): a block of the module's heap a
//! frame's shapes are encoded into, and the three functions that manage it.
//! Three globals hold it: the block (0 when there is none), the bytes written
//! and the bytes the block can hold. The block is allocated by the first
//! write of a frame and freed by `present`, so a frame that traps leaves it
//! for the next frame's `reset` to free.

use wasm_encoder::{BlockType, Function, Instruction, ValType};

use crate::{Code, assemble, layout, memarg};

pub const PTR_GLOBAL: u32 = 8;
pub const LEN_GLOBAL: u32 = 9;
pub const CAP_GLOBAL: u32 = 10;

/// The smallest block the buffer asks the allocator for.
const MIN_CAPACITY: i32 = 256;

/// What the buffer's functions call.
pub struct Runtime {
    pub alloc: u32,
    pub free: u32,
    /// The host's `scene.frame`.
    pub import: u32,
    /// Code that traps the program with `frame::TOO_BIG`.
    pub too_big: Code,
}

/// `free` takes a block whose count has reached zero, so the buffer's block,
/// allocated with count 1, is zeroed first.
fn free_block(rt: &Runtime) -> Code {
    use Instruction::*;
    vec![
        GlobalGet(PTR_GLOBAL),
        If(BlockType::Empty),
        GlobalGet(PTR_GLOBAL),
        I32Const(0),
        I32Store(memarg(layout::RC, 2)),
        GlobalGet(PTR_GLOBAL),
        Call(rt.free),
        End,
    ]
}

fn clear() -> Code {
    use Instruction::*;
    vec![
        I32Const(0),
        GlobalSet(PTR_GLOBAL),
        I32Const(0),
        GlobalSet(LEN_GLOBAL),
        I32Const(0),
        GlobalSet(CAP_GLOBAL),
    ]
}

/// `reserve(n: i64) -> i32`: the address of `n` more bytes of the buffer,
/// growing it (doubling, at least to fit) and trapping past `LIMIT`. The
/// size is an `i64` so that a sum of string lengths cannot wrap before it is
/// checked.
pub fn reserve(rt: &Runtime) -> Function {
    use Instruction::*;
    let (n, len, cap, total, grown, block) = (0, 1, 2, 3, 4, 5);
    let mut code: Code = vec![
        LocalGet(n),
        I64Const(goat_mir::frame::LIMIT as i64),
        GlobalGet(LEN_GLOBAL),
        I64ExtendI32U,
        I64Sub,
        I64GtU,
        If(BlockType::Empty),
    ];
    code.extend(rt.too_big.iter().cloned());
    code.extend([
        End,
        GlobalGet(LEN_GLOBAL),
        LocalSet(len),
        LocalGet(len),
        LocalGet(n),
        I32WrapI64,
        I32Add,
        LocalSet(total),
        GlobalGet(CAP_GLOBAL),
        LocalSet(cap),
        LocalGet(total),
        LocalGet(cap),
        I32GtU,
        If(BlockType::Empty),
        // grown = max(total, 2 * cap, MIN_CAPACITY)
        LocalGet(cap),
        I32Const(1),
        I32Shl,
        LocalSet(grown),
        LocalGet(grown),
        LocalGet(total),
        I32LtU,
        If(BlockType::Empty),
        LocalGet(total),
        LocalSet(grown),
        End,
        LocalGet(grown),
        I32Const(MIN_CAPACITY),
        I32LtU,
        If(BlockType::Empty),
        I32Const(MIN_CAPACITY),
        LocalSet(grown),
        End,
        LocalGet(grown),
        I32Const(layout::HEADER as i32),
        I32Add,
        Call(rt.alloc),
        LocalSet(block),
        LocalGet(block),
        I32Const(layout::HEADER as i32),
        I32Add,
        GlobalGet(PTR_GLOBAL),
        I32Const(layout::HEADER as i32),
        I32Add,
        LocalGet(len),
        MemoryCopy {
            src_mem: 0,
            dst_mem: 0,
        },
    ]);
    code.extend(free_block(rt));
    code.extend([
        LocalGet(block),
        GlobalSet(PTR_GLOBAL),
        LocalGet(grown),
        GlobalSet(CAP_GLOBAL),
        End,
        LocalGet(total),
        GlobalSet(LEN_GLOBAL),
        GlobalGet(PTR_GLOBAL),
        I32Const(layout::HEADER as i32),
        I32Add,
        LocalGet(len),
        I32Add,
    ]);
    let locals = [(5, ValType::I32)];
    let mut f = Function::new(locals);
    for instr in &code {
        f.instruction(instr);
    }
    f.instruction(&End);
    f
}

/// `reset()`: drop whatever a frame that trapped left behind.
pub fn reset(rt: &Runtime) -> Function {
    let mut code = free_block(rt);
    code.extend(clear());
    assemble(Function::new([]), &code)
}

/// `present()`: hand the buffer's bytes to the host and free it.
pub fn present(rt: &Runtime) -> Function {
    use Instruction::*;
    let mut code = vec![
        GlobalGet(PTR_GLOBAL),
        If(BlockType::Empty),
        GlobalGet(PTR_GLOBAL),
        I32Const(layout::HEADER as i32),
        I32Add,
        GlobalGet(LEN_GLOBAL),
        Call(rt.import),
        End,
    ];
    code.extend(free_block(rt));
    code.extend(clear());
    assemble(Function::new([]), &code)
}
