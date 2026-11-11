//! `Write` and `StrEq` in the emitted module: the host imports they bring in,
//! and a module that still validates.

#[path = "../../mir/tests/common/mod.rs"]
mod common;

use common::*;
use goat_mir::*;
use goat_wasm::emit;

fn wat(p: &Program) -> String {
    assert_eq!(verify(p), Ok(()));
    let bytes = emit(p).expect("program emits");
    wasmparser::Validator::new_with_features(
        wasmparser::WasmFeatures::default() | wasmparser::WasmFeatures::TAIL_CALL,
    )
    .validate_all(&bytes)
    .expect("module validates");
    wasmprinter::print_bytes(bytes).expect("prints")
}

fn string_program(body: Expr, ret: MTy) -> Program {
    let mut p = program(vec![func(ret, body)]);
    p.data = vec![b"ab".to_vec(), b"ac".to_vec()];
    p
}

fn then(first: Expr, rest: Expr, local: u32) -> Expr {
    let_(local, first, rest)
}

fn writes() -> Program {
    let body = then(
        Expr::Write(Write::Lit(DataId(0))),
        then(
            Expr::Write(Write::Number(Box::new(float(1.5)))),
            Expr::Write(Write::End),
            1,
        ),
        0,
    );
    string_program(body, MTy::Unit)
}

#[test]
fn write_imports_the_host_writers_after_the_print_imports() {
    let text = wat(&writes());
    for (index, name, params) in [
        (3, "write_number", "(param f64)"),
        (4, "write_string", "(param i32)"),
        (5, "write_end", ""),
        (6, "write_int", "(param i64)"),
    ] {
        let import = format!("(import \"goat\" \"{name}\" (func (;{index};)");
        assert!(text.contains(&import), "{name}: {text}");
        assert!(text.contains(params), "{name}: {text}");
    }
}

#[test]
fn an_int_write_calls_write_int_and_a_float_write_calls_write_number() {
    let write = |value| {
        string_program(
            then(
                Expr::Write(Write::Number(Box::new(value))),
                Expr::Write(Write::End),
                0,
            ),
            MTy::Unit,
        )
    };
    let ints = wat(&write(int(7)));
    let floats = wat(&write(float(1.5)));
    assert!(ints.contains("call 6"), "{ints}");
    assert!(!ints.contains("call 3"), "{ints}");
    assert!(floats.contains("call 3"), "{floats}");
    assert!(!floats.contains("call 6"), "{floats}");
}

#[test]
fn a_program_without_writes_imports_none() {
    let text = wat(&program(vec![func(MTy::Int, int(1))]));
    assert!(!text.contains("write_"), "{text}");
}

#[test]
fn a_string_root_keeps_print_string_ahead_of_the_writers() {
    let body = then(Expr::Write(Write::End), Expr::StrLit(DataId(0)), 0);
    let text = wat(&string_program(body, MTy::Ptr(HeapKind::Str)));
    assert!(
        text.contains("(import \"goat\" \"print_string\" (func (;3;)"),
        "{text}"
    );
    assert!(
        text.contains("(import \"goat\" \"write_number\" (func (;4;)"),
        "{text}"
    );
}

#[test]
fn string_equality_loops_over_the_bytes() {
    let body = let_(
        0,
        Expr::StrLit(DataId(0)),
        let_(
            1,
            Expr::StrLit(DataId(1)),
            let_(
                2,
                Expr::StrEq(Local(0), Local(1)),
                let_(
                    3,
                    Expr::Drop(Local(0)),
                    let_(4, Expr::Drop(Local(1)), local(2)),
                ),
            ),
        ),
    );
    let text = wat(&string_program(body, MTy::Bool));
    assert!(text.contains("i32.load8_u"), "{text}");
    assert!(text.contains("loop"), "{text}");
}

#[test]
fn reading_a_character_scans_within_the_length_and_allocates() {
    let body = let_(
        0,
        Expr::StrLit(DataId(0)),
        let_(
            1,
            int(2),
            let_(
                2,
                Expr::StrChar(Local(0), Local(1)),
                let_(
                    3,
                    Expr::StrChars(Local(2)),
                    let_(
                        4,
                        Expr::Drop(Local(2)),
                        let_(5, Expr::Drop(Local(0)), local(3)),
                    ),
                ),
            ),
        ),
    );
    let text = wat(&string_program(body, MTy::Int));
    assert!(text.contains("i32.load8_u"), "{text}");
    assert!(text.contains("i32.store8"), "{text}");
    assert!(text.contains("i64.eqz"), "{text}");
    assert!(text.contains(BYTE_OUT_OF_RANGE), "{text}");
}

#[test]
fn reading_a_byte_checks_the_position_against_the_length() {
    let body = let_(
        0,
        Expr::StrLit(DataId(0)),
        let_(
            1,
            int(2),
            let_(
                2,
                Expr::StrByte(Local(0), Local(1)),
                let_(
                    3,
                    Expr::StrLen(Local(0)),
                    let_(4, Expr::Drop(Local(0)), local(2)),
                ),
            ),
        ),
    );
    let text = wat(&string_program(body, MTy::Int));
    assert!(text.contains("i32.load8_u"), "{text}");
    assert!(text.contains("i64.ge_u"), "{text}");
    assert!(text.contains(BYTE_OUT_OF_RANGE), "{text}");
}
