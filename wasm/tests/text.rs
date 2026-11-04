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
        (2, "write_number", "(param f64)"),
        (3, "write_string", "(param i32)"),
        (4, "write_end", ""),
    ] {
        let import = format!("(import \"goat\" \"{name}\" (func (;{index};)");
        assert!(text.contains(&import), "{name}: {text}");
        assert!(text.contains(params), "{name}: {text}");
    }
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
        text.contains("(import \"goat\" \"print_string\" (func (;2;)"),
        "{text}"
    );
    assert!(
        text.contains("(import \"goat\" \"write_number\" (func (;3;)"),
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
