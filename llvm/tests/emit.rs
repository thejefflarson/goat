#[path = "../../mir/tests/common/mod.rs"]
mod common;

use common::*;
use goat_llvm::{EmitError, emit};
use goat_mir::*;
use std::path::PathBuf;
use std::process::Command;

fn ll(p: &Program) -> String {
    assert_eq!(verify(p), Ok(()));
    emit(p).expect("program emits")
}

fn golden(name: &str, p: &Program) {
    let actual = ll(p);
    let path = format!("{}/tests/golden/{name}.ll", env!("CARGO_MANIFEST_DIR"));
    if std::env::var_os("UPDATE_GOLDEN").is_some() {
        std::fs::write(&path, &actual).unwrap();
    }
    let expected = std::fs::read_to_string(&path).expect("golden file exists");
    assert_eq!(
        actual, expected,
        "run with UPDATE_GOLDEN=1 to refresh {path}"
    );
}

fn embedded(mut p: Program) -> Program {
    p.profile = Profile::Embedded;
    p
}

fn int_op(op: IntOp, a: i64, b: i64) -> Expr {
    Expr::BinInt(op, Box::new(int(a)), Box::new(int(b)))
}

fn float_op(op: FloatOp, a: f64, b: f64) -> Expr {
    bin_float(op, float(a), float(b))
}

fn arithmetic() -> Program {
    let body = let_(
        0,
        bin_float(FloatOp::Add, float(1.5), float(2.5)),
        bin_float(FloatOp::Mul, local(0), float(2.0)),
    );
    program(vec![func(MTy::Float, body)])
}

fn checked_int() -> Program {
    let body = mul(add(int(2), int(3)), sub(int(10), int(4)));
    program(vec![func(MTy::Int, body)])
}

fn division() -> Program {
    let body = add(
        add(int_op(IntOp::Div, 7, -2), int_op(IntOp::FloorDiv, 7, -2)),
        int_op(IntOp::Mod, 7, -2),
    );
    program(vec![func(MTy::Int, body)])
}

fn conditional() -> Program {
    let body = let_(
        0,
        float(3.0),
        if_(
            cmp(CmpOp::Lt, local(0), float(5.0)),
            bin_float(FloatOp::Add, local(0), float(1.0)),
            local(0),
        ),
    );
    program(vec![func(MTy::Float, body)])
}

fn nested_conditional() -> Program {
    let body = if_(
        cmp(CmpOp::Gt, int(2), int(1)),
        if_(boolean(false), int(1), add(int(2), int(3))),
        Expr::Trap("never".to_string()),
    );
    program(vec![func(MTy::Int, body)])
}

fn floored_float() -> Program {
    let body = bin_float(
        FloatOp::Add,
        float_op(FloatOp::FloorDiv, 7.5, -2.0),
        float_op(FloatOp::Mod, 7.5, -2.0),
    );
    program(vec![func(MTy::Float, body)])
}

fn conversions() -> Program {
    let body = Expr::FloatFn(
        FloatFn::Truncate,
        Box::new(Expr::FloatFn(
            FloatFn::Sqrt,
            Box::new(Expr::IntToFloat(Box::new(int(17)))),
        )),
    );
    program(vec![func(MTy::Int, body)])
}

fn calls() -> Program {
    let entry = func(MTy::Int, call(1, vec![int(20), int(22)]));
    let sum = func_with(
        vec![(0, MTy::Int), (1, MTy::Int)],
        MTy::Int,
        add(local(0), local(1)),
    );
    program(vec![entry, sum])
}

#[test]
fn arithmetic_matches_golden() {
    golden("arithmetic", &arithmetic());
}

#[test]
fn checked_int_matches_golden() {
    golden("checked_int", &checked_int());
}

#[test]
fn division_matches_golden() {
    golden("division", &division());
}

#[test]
fn conditional_matches_golden() {
    golden("conditional", &conditional());
}

#[test]
fn nested_conditional_matches_golden() {
    golden("nested_conditional", &nested_conditional());
}

#[test]
fn floored_float_matches_golden() {
    golden("floored_float", &floored_float());
}

#[test]
fn conversions_match_golden() {
    golden("conversions", &conversions());
}

#[test]
fn calls_match_golden() {
    golden("calls", &calls());
}

#[test]
fn embedded_matches_golden() {
    golden("embedded", &embedded(checked_int()));
}

#[test]
fn emitted_ir_has_no_undefined_behavior_flags_or_triple() {
    let all = [
        arithmetic(),
        checked_int(),
        division(),
        conditional(),
        nested_conditional(),
        floored_float(),
        conversions(),
        calls(),
        embedded(division()),
    ];
    for p in all {
        let text = ll(&p);
        for forbidden in [
            "nsw",
            "nuw",
            "fast",
            "nnan",
            "ninf",
            "contract",
            "afn",
            "reassoc",
            "!tbaa",
            "target triple",
            "target datalayout",
        ] {
            assert!(
                !text
                    .split(|c: char| !c.is_alphanumeric() && c != '!')
                    .any(|w| w == forbidden),
                "{forbidden} in:\n{text}"
            );
        }
        for line in text.lines().filter(|l| l.starts_with("define ")) {
            assert!(line.contains(" nounwind "), "{line}");
        }
    }
}

#[test]
fn unsupported_nodes_are_internal_errors() {
    let p = program(vec![func(
        MTy::Int,
        Expr::TailCall(Callee::Direct(FuncId(0)), vec![]),
    )]);
    let err = emit(&p).unwrap_err();
    assert_eq!(err, EmitError::Unsupported("tail calls"));
    assert!(
        err.to_string()
            .contains("not yet supported by the native backend")
    );

    let p = program(vec![func(record_ty(), alloc_record(1))]);
    assert_eq!(emit(&p), Err(EmitError::Unsupported("heap values")));
}

fn clang() -> Option<&'static str> {
    let found = Command::new("clang")
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success());
    if !found {
        eprintln!("skipping: clang is not on PATH");
    }
    found.then_some("clang")
}

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("goat_llvm_{}_{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

#[test]
fn clang_reads_every_program() {
    let Some(clang) = clang() else { return };
    let programs = [
        ("arithmetic", arithmetic()),
        ("checked_int", checked_int()),
        ("division", division()),
        ("conditional", conditional()),
        ("nested_conditional", nested_conditional()),
        ("floored_float", floored_float()),
        ("conversions", conversions()),
        ("calls", calls()),
        ("embedded", embedded(checked_int())),
        ("embedded_division", embedded(division())),
        ("embedded_floored", embedded(floored_float())),
        ("embedded_conversions", embedded(conversions())),
    ];
    let dir = scratch("parse");
    for (name, p) in programs {
        let path = dir.join(format!("{name}.ll"));
        std::fs::write(&path, ll(&p)).unwrap();
        let out = Command::new(clang)
            .args(["-x", "ir", "-c", "-o", "/dev/null"])
            .arg(&path)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
}

const HARNESS: &str = r#"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
void goat_trap(void *inst, const char *message, int32_t len) {
    printf("trap: %.*s\n", (int)len, message);
    exit(0);
}
extern RET goat_entry(void *inst);
int main(void) {
    printf(FMT "\n", (CAST)goat_entry(0));
    return 0;
}
"#;

#[derive(Clone, Copy)]
enum Ret {
    Int,
    Int32,
    Float,
    Bool,
}

/// Compiles `p` with a C `main`, runs it, and returns what it printed.
fn run(clang: &str, name: &str, p: &Program, ret: Ret) -> String {
    let (c_ty, fmt, cast) = match ret {
        Ret::Int => ("int64_t", "\"%lld\"", "long long"),
        Ret::Int32 => ("int32_t", "\"%d\"", "int"),
        Ret::Float => ("double", "\"%.17g\"", "double"),
        Ret::Bool => ("_Bool", "\"%d\"", "int"),
    };
    let dir = scratch(name);
    let (ll_path, c_path, exe) = (dir.join("p.ll"), dir.join("main.c"), dir.join("p"));
    std::fs::write(&ll_path, ll(p)).unwrap();
    std::fs::write(&c_path, HARNESS).unwrap();
    let build = Command::new(clang)
        .arg(format!("-DRET={c_ty}"))
        .arg(format!("-DFMT={fmt}"))
        .arg(format!("-DCAST={cast}"))
        .arg(&c_path)
        .args(["-x", "ir"])
        .arg(&ll_path)
        .arg("-lm")
        .arg("-o")
        .arg(&exe)
        .output()
        .unwrap();
    assert!(
        build.status.success(),
        "{name}: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let out = Command::new(&exe).output().unwrap();
    assert!(out.status.success(), "{name} exited with {:?}", out.status);
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

fn int_program(body: Expr) -> Program {
    program(vec![func(MTy::Int, body)])
}

#[test]
fn integer_arithmetic_runs_and_traps_on_overflow() {
    let Some(clang) = clang() else { return };
    let overflow = format!("trap: {INT_OVERFLOW}");
    let zero = format!("trap: {DIVISION_BY_ZERO}");
    let (max, min) = (i64::MAX, i64::MIN);
    let cases: Vec<(IntOp, i64, i64, String)> = vec![
        (IntOp::Add, 40, 2, "42".into()),
        (IntOp::Add, max, 1, overflow.clone()),
        (IntOp::Add, min, -1, overflow.clone()),
        (IntOp::Sub, 5, 7, "-2".into()),
        (IntOp::Sub, min, 1, overflow.clone()),
        (IntOp::Sub, 0, min, overflow.clone()),
        (IntOp::Mul, -6, 7, "-42".into()),
        (IntOp::Mul, max, 2, overflow.clone()),
        (IntOp::Mul, min, -1, overflow.clone()),
        (IntOp::Div, 7, -2, "-3".into()),
        (IntOp::Div, 7, 0, zero.clone()),
        (IntOp::Div, min, -1, overflow.clone()),
        (IntOp::FloorDiv, 7, -2, "-4".into()),
        (IntOp::FloorDiv, -7, 2, "-4".into()),
        (IntOp::FloorDiv, 6, 3, "2".into()),
        (IntOp::FloorDiv, 1, 0, zero.clone()),
        (IntOp::FloorDiv, min, -1, overflow.clone()),
        (IntOp::Mod, 7, -2, "-1".into()),
        (IntOp::Mod, -7, 2, "1".into()),
        (IntOp::Mod, 6, 3, "0".into()),
        (IntOp::Mod, 1, 0, zero.clone()),
        (IntOp::Mod, min, -1, "0".into()),
    ];
    for (i, (op, a, b, expected)) in cases.into_iter().enumerate() {
        let got = run(
            clang,
            &format!("int{i}"),
            &int_program(int_op(op, a, b)),
            Ret::Int,
        );
        assert_eq!(got, expected, "{op:?} {a} {b}");
    }
}

#[test]
fn embedded_integers_are_32_bit() {
    let Some(clang) = clang() else { return };
    let overflow = format!("trap: {INT_OVERFLOW}");
    let cases: Vec<(IntOp, i64, i64, String)> = vec![
        (IntOp::Add, i64::from(i32::MAX), 1, overflow.clone()),
        (IntOp::Mul, 65536, 65536, overflow.clone()),
        (IntOp::Div, i64::from(i32::MIN), -1, overflow.clone()),
        (IntOp::Mod, i64::from(i32::MIN), -1, "0".into()),
        (IntOp::FloorDiv, -7, 2, "-4".into()),
    ];
    for (i, (op, a, b, expected)) in cases.into_iter().enumerate() {
        let p = embedded(int_program(int_op(op, a, b)));
        let got = run(clang, &format!("emb{i}"), &p, Ret::Int32);
        assert_eq!(got, expected, "{op:?} {a} {b}");
    }
}

#[test]
fn comparisons_and_if_run() {
    let Some(clang) = clang() else { return };
    let ops = [
        (CmpOp::Eq, "0"),
        (CmpOp::Ne, "1"),
        (CmpOp::Lt, "1"),
        (CmpOp::Le, "1"),
        (CmpOp::Gt, "0"),
        (CmpOp::Ge, "0"),
    ];
    for (i, (op, expected)) in ops.into_iter().enumerate() {
        let p = program(vec![func(MTy::Bool, cmp(op, int(1), int(2)))]);
        assert_eq!(
            run(clang, &format!("cmp{i}"), &p, Ret::Bool),
            expected,
            "{op:?}"
        );
    }
    let nan = bin_float(FloatOp::Div, float(0.0), float(0.0));
    let p = program(vec![func(
        MTy::Bool,
        cmp(CmpOp::Ne, nan.clone(), nan.clone()),
    )]);
    assert_eq!(run(clang, "nan_ne", &p, Ret::Bool), "1");
    let p = program(vec![func(MTy::Bool, cmp(CmpOp::Eq, nan.clone(), nan))]);
    assert_eq!(run(clang, "nan_eq", &p, Ret::Bool), "0");
    assert_eq!(run(clang, "nested", &nested_conditional(), Ret::Int), "5");
    assert_eq!(run(clang, "calls", &calls(), Ret::Int), "42");
}

#[test]
fn floats_run() {
    let Some(clang) = clang() else { return };
    assert_eq!(run(clang, "arith", &arithmetic(), Ret::Float), "8");
    assert_eq!(run(clang, "cond", &conditional(), Ret::Float), "4");
    assert_eq!(run(clang, "conv", &conversions(), Ret::Int), "4");
    // Python: 7.5 // -2.0 == -4.0 and 7.5 % -2.0 == -0.5.
    assert_eq!(run(clang, "floored", &floored_float(), Ret::Float), "-4.5");
    for (i, (op, a, b, expected)) in [
        (FloatOp::FloorDiv, -7.0, 2.0, "-4"),
        (FloatOp::Mod, -7.0, 2.0, "1"),
        (FloatOp::FloorDiv, 1.0, 0.0, "inf"),
        (FloatOp::Mod, 1.0, 0.0, "-nan"),
    ]
    .into_iter()
    .enumerate()
    {
        let p = program(vec![func(MTy::Float, float_op(op, a, b))]);
        let got = run(clang, &format!("fl{i}"), &p, Ret::Float);
        assert!(
            got == expected || got == "nan" && expected == "-nan",
            "{op:?}: {got}"
        );
    }
}

#[test]
fn truncating_a_float_traps_outside_the_int_range() {
    let Some(clang) = clang() else { return };
    let trunc = |x: f64| Expr::FloatFn(FloatFn::Truncate, Box::new(float(x)));
    let cases = [
        (trunc(-3.9), "-3".to_string()),
        (trunc(1e30), format!("trap: {NOT_A_WHOLE_NUMBER}")),
        (
            Expr::FloatFn(
                FloatFn::Truncate,
                Box::new(bin_float(FloatOp::Div, float(0.0), float(0.0))),
            ),
            format!("trap: {NOT_A_WHOLE_NUMBER}"),
        ),
    ];
    for (i, (body, expected)) in cases.into_iter().enumerate() {
        assert_eq!(
            run(clang, &format!("tr{i}"), &int_program(body), Ret::Int),
            expected
        );
    }
}
