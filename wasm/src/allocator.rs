//! The wasm allocator: size-class free lists over a bump region.
//!
//! A second strategy (fixed-size pools inside a declared heap budget, for
//! embedded targets) replaces this module behind the same three functions:
//! `alloc(size) -> ptr`, `free(ptr)`, and the live-allocation count.
//!
//! Invariants:
//! - Every block is a multiple of 8 bytes and at least `MIN_BLOCK`, so a freed
//!   block can hold its free-list link just past the header.
//! - `alloc` stores `rc = 1` and the block's size class in the header's `_pad`
//!   word; `free` reads the class back, so it needs no size from the caller.
//! - A freed block has `rc == 0`, its link in the first payload word, and every
//!   other payload byte set to `POISON`. A second release of the same block
//!   meets `rc == 0` and traps, and a read through a dangling pointer sees
//!   `0xFEFEFEFE` (or the link) rather than stale data.
//! - `alloc` traps if a block it pops off a free list has `rc != 0`, which
//!   catches a write that reached a block after it was freed.
//! - The live count moves only here. Immortal objects (`rc == u32::MAX`)
//!   live in the data segment, never pass through `alloc` or `free`, and so
//!   are never counted.

use wasm_encoder::{BlockType, Function, Instruction, ValType};

use crate::{layout, memarg, rc_load};

const HEAP_GLOBAL: u32 = 0;
pub const LIVE_GLOBAL: u32 = 1;
pub const FUNCTIONS: u32 = 3;

const MIN_BLOCK: u32 = 16;
const SMALL_MAX: u32 = 256;
const SMALL_CLASSES: u32 = SMALL_MAX / 8;
/// A large class `c` holds blocks of `1 << (c - LARGE_BASE)` bytes.
const LARGE_BASE: u32 = 24;
const MAX_REQUEST: u32 = 1 << 30;
const CLASSES: u32 = LARGE_BASE + 30 + 1;
const POISON: i32 = 0xFE;
const PAGE_BITS: i32 = 16;

pub const TABLE_BYTES: u32 = (CLASSES * 4).next_multiple_of(8);

type Code = Vec<Instruction<'static>>;

/// Free-list heads, one word per size class, at `table` in linear memory.
pub struct FreeList {
    pub table: u32,
}

fn guard(cond: Code) -> Code {
    let mut out = cond;
    out.extend([
        Instruction::If(BlockType::Empty),
        Instruction::Unreachable,
        Instruction::End,
    ]);
    out
}

fn finish(locals: &[(u32, ValType)], code: Code) -> Function {
    let mut f = Function::new(locals.iter().copied());
    for instr in &code {
        f.instruction(instr);
    }
    f.instruction(&Instruction::End);
    f
}

/// Leaves the byte size of the block class held in `class` on the stack.
fn class_bytes(class: u32) -> Code {
    use Instruction::*;
    vec![
        LocalGet(class),
        I32Const(SMALL_CLASSES as i32),
        I32LeU,
        If(BlockType::Result(ValType::I32)),
        LocalGet(class),
        I32Const(3),
        I32Shl,
        Else,
        I32Const(1),
        LocalGet(class),
        I32Const(LARGE_BASE as i32),
        I32Sub,
        I32Shl,
        End,
    ]
}

/// Leaves the address of the head slot for the class held in `class`.
fn head_slot(class: u32) -> Code {
    use Instruction::*;
    vec![LocalGet(class), I32Const(2), I32Shl]
}

impl FreeList {
    /// `alloc(size: i32) -> i32`: a block with `rc = 1`, from the class's free
    /// list when it has one and from the bump region otherwise.
    pub fn alloc(&self) -> Function {
        use Instruction::*;
        let (size, class, block, bytes, end) = (0, 1, 2, 3, 4);
        let mut code = guard(vec![LocalGet(size), I32Const(MAX_REQUEST as i32), I32GtU]);
        code.extend([
            LocalGet(size),
            I32Const(7),
            I32Add,
            I32Const(-8),
            I32And,
            LocalSet(bytes),
            LocalGet(bytes),
            I32Const(MIN_BLOCK as i32),
            I32LtU,
            If(BlockType::Empty),
            I32Const(MIN_BLOCK as i32),
            LocalSet(bytes),
            End,
            // class = bytes / 8 up to SMALL_MAX, else LARGE_BASE + ceil(log2(bytes)).
            LocalGet(bytes),
            I32Const(SMALL_MAX as i32),
            I32LeU,
            If(BlockType::Result(ValType::I32)),
            LocalGet(bytes),
            I32Const(3),
            I32ShrU,
            Else,
            I32Const((LARGE_BASE + 32) as i32),
            LocalGet(bytes),
            I32Const(1),
            I32Sub,
            I32Clz,
            I32Sub,
            End,
            LocalSet(class),
        ]);
        code.extend(class_bytes(class));
        code.push(LocalSet(bytes));

        code.extend(head_slot(class));
        code.extend([
            I32Load(memarg(self.table, 2)),
            LocalTee(block),
            If(BlockType::Empty),
        ]);
        code.extend(guard(vec![LocalGet(block), rc_load()]));
        code.extend(head_slot(class));
        code.extend([
            LocalGet(block),
            I32Load(memarg(layout::LINK, 2)),
            I32Store(memarg(self.table, 2)),
            Else,
            GlobalGet(HEAP_GLOBAL),
            LocalTee(block),
            LocalGet(bytes),
            I32Add,
            LocalTee(end),
            MemorySize(0),
            I32Const(PAGE_BITS),
            I32Shl,
            I32GtU,
            If(BlockType::Empty),
            LocalGet(end),
            MemorySize(0),
            I32Const(PAGE_BITS),
            I32Shl,
            I32Sub,
            I32Const((1 << PAGE_BITS) - 1),
            I32Add,
            I32Const(PAGE_BITS),
            I32ShrU,
            MemoryGrow(0),
            I32Const(-1),
            I32Eq,
            If(BlockType::Empty),
            Unreachable,
            End,
            End,
            LocalGet(end),
            GlobalSet(HEAP_GLOBAL),
            End,
            LocalGet(block),
            I32Const(1),
            I32Store(memarg(layout::RC, 2)),
            LocalGet(block),
            LocalGet(class),
            I32Store(memarg(layout::CLASS, 2)),
            GlobalGet(LIVE_GLOBAL),
            I32Const(1),
            I32Add,
            GlobalSet(LIVE_GLOBAL),
            LocalGet(block),
        ]);
        finish(&[(4, ValType::I32)], code)
    }

    /// `free(ptr: i32)`: takes a block whose count just reached zero, poisons
    /// it, and pushes it on its class's free list.
    pub fn free(&self) -> Function {
        use Instruction::*;
        let (ptr, class, bytes) = (0, 1, 2);
        let mut code = guard(vec![LocalGet(ptr), rc_load()]);
        code.extend([
            LocalGet(ptr),
            I32Load(memarg(layout::CLASS, 2)),
            LocalSet(class),
        ]);
        code.extend(class_bytes(class));
        code.extend([
            LocalSet(bytes),
            LocalGet(ptr),
            I32Const(layout::HEADER as i32),
            I32Add,
            I32Const(POISON),
            LocalGet(bytes),
            I32Const(layout::HEADER as i32),
            I32Sub,
            MemoryFill(0),
            LocalGet(ptr),
        ]);
        code.extend(head_slot(class));
        code.extend([
            I32Load(memarg(self.table, 2)),
            I32Store(memarg(layout::LINK, 2)),
        ]);
        code.extend(head_slot(class));
        code.extend([
            LocalGet(ptr),
            I32Store(memarg(self.table, 2)),
            GlobalGet(LIVE_GLOBAL),
            I32Const(1),
            I32Sub,
            GlobalSet(LIVE_GLOBAL),
        ]);
        finish(&[(2, ValType::I32)], code)
    }

    /// `goat_live_allocs() -> i32`: blocks allocated and not yet freed.
    pub fn live_allocs(&self) -> Function {
        finish(&[], vec![Instruction::GlobalGet(LIVE_GLOBAL)])
    }
}
