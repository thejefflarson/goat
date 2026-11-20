//! `Float` `//` and `%` as module-local functions over `f64`: wasm has no
//! `fmod`, and a host import would put a requirement on every host. The
//! embedded profile widens its `f32`s to `f64` around the call, which is exact,
//! and rounds the result back.

use wasm_encoder::{BlockType, Function, Instruction, ValType};

use crate::{Code, assemble};

/// C's `fmod(x, y)`, exact: the quotient's whole part is removed one power of
/// two of `|y|` at a time, and each subtraction is exact because the
/// subtrahend is at most the minuend and at least half of it.
pub(crate) fn fmod() -> Function {
    use Instruction::*;
    let (x, y, ax, t, ay) = (0, 1, 2, 3, 4);
    let code: Code = vec![
        LocalGet(y),
        F64Abs,
        LocalTee(ay),
        F64Const(0.0.into()),
        F64Eq,
        LocalGet(x),
        F64Abs,
        LocalTee(ax),
        F64Const(f64::INFINITY.into()),
        F64Eq,
        I32Or,
        LocalGet(x),
        LocalGet(x),
        F64Ne,
        I32Or,
        LocalGet(y),
        LocalGet(y),
        F64Ne,
        I32Or,
        If(BlockType::Empty),
        F64Const(f64::NAN.into()),
        Return,
        End,
        LocalGet(ax),
        LocalGet(ay),
        F64Lt,
        If(BlockType::Empty),
        LocalGet(x),
        Return,
        End,
        LocalGet(ay),
        LocalSet(t),
        // Double `t` while twice it still fits under `ax`.
        Block(BlockType::Empty),
        Loop(BlockType::Empty),
        LocalGet(t),
        F64Const(2.0.into()),
        F64Mul,
        LocalGet(ax),
        F64Gt,
        BrIf(1),
        LocalGet(t),
        F64Const(2.0.into()),
        F64Mul,
        LocalSet(t),
        Br(0),
        End,
        End,
        // Subtract it where it fits, then halve back down to `|y|`.
        Block(BlockType::Empty),
        Loop(BlockType::Empty),
        LocalGet(ax),
        LocalGet(t),
        F64Ge,
        If(BlockType::Empty),
        LocalGet(ax),
        LocalGet(t),
        F64Sub,
        LocalSet(ax),
        End,
        LocalGet(t),
        LocalGet(ay),
        F64Eq,
        BrIf(1),
        LocalGet(t),
        F64Const(0.5.into()),
        F64Mul,
        LocalSet(t),
        Br(0),
        End,
        End,
        LocalGet(ax),
        LocalGet(x),
        F64Copysign,
    ];
    assemble(Function::new([(3, ValType::F64)]), &code)
}

/// Python's `x // y` (`want_quotient`) or `x % y` over `f64`: CPython's
/// `float_divmod` built on `fmod`. A zero divisor follows IEEE: `x // 0` is
/// `x / 0`, and `x % 0` is NaN (from `fmod`).
pub(crate) fn floored(fmod_fn: u32, want_quotient: bool) -> Function {
    use Instruction::*;
    let (x, y, m, d, floor) = (0, 1, 2, 3, 4);
    let mut code: Code = Vec::new();
    if want_quotient {
        code.extend([
            LocalGet(y),
            F64Const(0.0.into()),
            F64Eq,
            If(BlockType::Empty),
            LocalGet(x),
            LocalGet(y),
            F64Div,
            Return,
            End,
        ]);
    }
    code.extend([
        LocalGet(x),
        LocalGet(y),
        Call(fmod_fn),
        LocalSet(m),
        LocalGet(x),
        LocalGet(m),
        F64Sub,
        LocalGet(y),
        F64Div,
        LocalSet(d),
        LocalGet(m),
        F64Const(0.0.into()),
        F64Ne,
        If(BlockType::Empty),
        // A remainder on the wrong side of zero moves to the divisor's side.
        LocalGet(y),
        F64Const(0.0.into()),
        F64Lt,
        LocalGet(m),
        F64Const(0.0.into()),
        F64Lt,
        I32Ne,
        If(BlockType::Empty),
        LocalGet(m),
        LocalGet(y),
        F64Add,
        LocalSet(m),
        LocalGet(d),
        F64Const(1.0.into()),
        F64Sub,
        LocalSet(d),
        End,
        Else,
        F64Const(0.0.into()),
        LocalGet(y),
        F64Copysign,
        LocalSet(m),
        End,
        LocalGet(d),
        F64Const(0.0.into()),
        F64Ne,
        If(BlockType::Empty),
        LocalGet(d),
        F64Floor,
        LocalSet(floor),
        // `d` is a rounded quotient, so a floor more than half away is a
        // whole number the rounding crossed.
        LocalGet(d),
        LocalGet(floor),
        F64Sub,
        F64Const(0.5.into()),
        F64Gt,
        If(BlockType::Empty),
        LocalGet(floor),
        F64Const(1.0.into()),
        F64Add,
        LocalSet(floor),
        End,
        Else,
        F64Const(0.0.into()),
        LocalGet(x),
        LocalGet(y),
        F64Div,
        F64Copysign,
        LocalSet(floor),
        End,
        LocalGet(if want_quotient { floor } else { m }),
    ]);
    assemble(Function::new([(3, ValType::F64)]), &code)
}
