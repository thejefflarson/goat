#[path = "../../mir/tests/common/mod.rs"]
mod common;

use common::*;
use goat_mir::*;
use goat_wasm::{EmitError, emit};

fn emit_valid(p: &Program) -> Vec<u8> {
    assert_eq!(verify(p), Ok(()));
    let bytes = emit(p).expect("program emits");
    wasmparser::Validator::new()
        .validate_all(&bytes)
        .expect("module validates");
    bytes
}

fn wat(p: &Program) -> String {
    wasmprinter::print_bytes(emit_valid(p)).expect("prints")
}

fn golden(name: &str, p: &Program) {
    let actual = wat(p);
    let path = format!("{}/tests/golden/{name}.wat", env!("CARGO_MANIFEST_DIR"));
    if std::env::var_os("UPDATE_GOLDEN").is_some() {
        std::fs::write(&path, &actual).unwrap();
    }
    let expected = std::fs::read_to_string(&path).expect("golden file exists");
    assert_eq!(
        actual, expected,
        "run with UPDATE_GOLDEN=1 to refresh {path}"
    );
}

fn arithmetic() -> Program {
    let body = let_(
        0,
        bin_float(FloatOp::Add, float(1.5), float(2.5)),
        bin_float(FloatOp::Mul, local(0), float(2.0)),
    );
    program(vec![func(MTy::Float, body)])
}

fn conditional() -> Program {
    let body = let_(
        0,
        float(3.0),
        if_(
            cmp(CmpOp::Lt, local(0), float(5.0)),
            bin_float(FloatOp::Sub, local(0), float(1.0)),
            Expr::Trap("unreachable branch".into()),
        ),
    );
    program(vec![func(MTy::Float, body)])
}

fn fib() -> Program {
    let n = || local(0);
    let fib_body = if_(
        cmp(CmpOp::Lt, n(), int(2)),
        n(),
        add(
            call(1, vec![sub(n(), int(1))]),
            call(1, vec![sub(n(), int(2))]),
        ),
    );
    program(vec![
        func(MTy::Int, call(1, vec![int(10)])),
        func_with(vec![(0, MTy::Int)], MTy::Int, fib_body),
    ])
}

#[test]
fn arithmetic_matches_golden() {
    golden("arithmetic", &arithmetic());
}

#[test]
fn conditional_matches_golden() {
    golden("conditional", &conditional());
}

#[test]
fn recursive_fib_matches_golden() {
    golden("fib", &fib());
}

#[test]
fn comparison_roots_print_bool() {
    let ints = program(vec![func(MTy::Bool, cmp(CmpOp::Ge, int(3), int(2)))]);
    let floats = program(vec![func(
        MTy::Bool,
        cmp(CmpOp::Ne, float(1.0), float(2.0)),
    )]);
    for p in [ints, floats] {
        let text = wat(&p);
        assert!(text.contains("call 1"), "{text}");
    }
}

#[test]
fn every_comparison_operator_validates() {
    use CmpOp::*;
    for op in [Eq, Ne, Lt, Le, Gt, Ge] {
        emit_valid(&program(vec![func(MTy::Bool, cmp(op, int(1), int(2)))]));
        emit_valid(&program(vec![func(
            MTy::Bool,
            cmp(op, float(1.0), float(2.0)),
        )]));
    }
}

#[test]
fn unit_root_prints_nothing() {
    let p = program(vec![func(MTy::Unit, Expr::Const(Const::Unit))]);
    let text = wat(&p);
    assert!(
        !text.contains("call 0") && !text.contains("call 1"),
        "{text}"
    );
}

#[test]
fn unit_values_are_erased_through_let_and_calls() {
    let side_effect = func(MTy::Unit, Expr::Const(Const::Unit));
    let root = func(
        MTy::Float,
        let_(0, call(1, vec![]), let_(1, local(0), float(7.0))),
    );
    emit_valid(&program(vec![root, side_effect]));
}

#[test]
fn trap_in_value_position_validates() {
    let body = bin_float(FloatOp::Add, float(1.0), Expr::Trap("boom".into()));
    emit_valid(&program(vec![func(MTy::Float, body)]));
    let both = if_(
        boolean(true),
        Expr::Trap("a".into()),
        Expr::Trap("b".into()),
    );
    emit_valid(&program(vec![func(MTy::Float, both)]));
}

#[test]
fn module_shape() {
    let text = wat(&arithmetic());
    for expected in [
        "(import \"goat\" \"print_number\" (func (;0;) (type 0) (param f64)))",
        "(import \"goat\" \"print_bool\" (func (;1;) (type 1) (param i32)))",
        "(memory (;0;) 1)",
        "(global (;0;) (mut i32) i32.const 8)",
        "(export \"memory\" (memory 0))",
        "(export \"goat_entry\" (func 3))",
        "(data (;0;) (i32.const 8) \"\")",
    ] {
        assert!(text.contains(expected), "missing {expected}\n{text}");
    }
}

#[test]
fn heap_starts_after_the_aligned_data_segment() {
    let mut p = arithmetic();
    p.data = vec![vec![0; 13]];
    let text = wat(&p);
    assert!(
        text.contains("(global (;0;) (mut i32) i32.const 24)"),
        "{text}"
    );
}

#[test]
fn heap_and_closure_nodes_are_rejected() {
    let heap = program(vec![func(MTy::Int, let_(0, alloc_record(1), int(0)))]);
    assert!(matches!(emit(&heap), Err(EmitError::Unsupported(_))));
    let closure = program(vec![func(
        MTy::Int,
        Expr::CallClosure(Box::new(int(0)), vec![]),
    )]);
    assert!(matches!(emit(&closure), Err(EmitError::Unsupported(_))));
}
