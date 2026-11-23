#[path = "../../mir/tests/common/mod.rs"]
mod common;

use common::*;
use goat_llvm::{EmitError, EmitOptions, emit, emit_with_options};
use goat_mir::*;
use std::path::PathBuf;
use std::process::Command;

/// Goldens and runs use checked builds whatever the profile the tests were
/// compiled with, so they read the same everywhere.
const CHECKED: EmitOptions = EmitOptions {
    poison_freed: true,
    call_depth: goat_llvm::DEFAULT_CALL_DEPTH,
    abi: goat_llvm::Abi::DEFAULT,
};

fn ll(p: &Program) -> String {
    assert_eq!(verify(p), Ok(()));
    emit_with_options(p, CHECKED).expect("program emits")
}

fn golden(name: &str, p: &Program) {
    golden_with(name, p, CHECKED);
}

fn golden_with(name: &str, p: &Program, options: EmitOptions) {
    assert_eq!(verify(p), Ok(()));
    let actual = emit_with_options(p, options).expect("program emits");
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
        heap(),
        strings(),
        apply_double(),
        record_of_functions(),
        capturing_a_record(),
        embedded(division()),
        embedded(heap()),
        embedded(record_of_functions()),
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
    let p = program(vec![func(MTy::Int, Expr::MethodKey(Local(0)))]);
    let err = emit(&p).unwrap_err();
    assert_eq!(err, EmitError::Unsupported("method sites"));
    assert!(
        err.to_string()
            .contains("not yet supported by the native backend")
    );
}

/// A record built and read, a variant matched, and a string read: every kind of
/// heap value, so the runtime they need is emitted.
fn heap() -> Program {
    let body = let_(
        0,
        alloc_record(40),
        let_(
            1,
            Expr::Field(Local(0), 0),
            let_(
                2,
                drop_(0),
                let_(
                    3,
                    Expr::AllocVariant(VARIANT, 1, vec![local(1)]),
                    let_(
                        4,
                        Expr::Switch(
                            Local(3),
                            vec![(1, Expr::Payload(Local(3), 1, 0))],
                            Box::new(int(0)),
                        ),
                        let_(5, drop_(3), local(4)),
                    ),
                ),
            ),
        ),
    );
    program(vec![func(MTy::Int, body)])
}

fn strings() -> Program {
    let body = let_(
        0,
        Expr::StrLit(DataId(0)),
        let_(
            1,
            int(2),
            let_(
                2,
                add(Expr::StrLen(Local(0)), Expr::StrByte(Local(0), Local(1))),
                let_(3, drop_(0), local(2)),
            ),
        ),
    );
    let mut p = program(vec![func(MTy::Int, body)]);
    p.data = vec![b"h\xc3\xa9llo".to_vec()];
    p
}

/// `double(x) = x * 2`, taking and dropping its environment.
fn double() -> Func {
    closure_fn(
        vec![(0, MTy::Int)],
        1,
        vec![],
        MTy::Int,
        let_(2, drop_(1), mul(local(0), int(2))),
    )
}

/// `\x -> x + k` with `k` captured.
fn add_k() -> Func {
    closure_fn(
        vec![(0, MTy::Int)],
        1,
        vec![MTy::Int],
        MTy::Int,
        let_(
            2,
            Expr::Capture(0),
            let_(3, drop_(1), add(local(0), local(2))),
        ),
    )
}

fn apply_double() -> Program {
    let apply = func_with(
        vec![(0, closure_ty(0)), (1, MTy::Int)],
        MTy::Int,
        call_closure(local(0), vec![local(1)]),
    );
    let main = func(
        MTy::Int,
        call(2, vec![Expr::MakeClosure(FuncId(1), vec![]), int(21)]),
    );
    with_closures(program(vec![main, double(), apply]), vec![MTy::Int])
}

/// A record holding a static closure and one capturing `10`; releasing the
/// record releases the closures through the drop id each carries.
fn record_of_functions() -> Program {
    let main = func(
        MTy::Int,
        let_(
            0,
            Expr::AllocRecord(
                FNS,
                vec![
                    Expr::MakeClosure(FuncId(1), vec![]),
                    Expr::MakeClosure(FuncId(2), vec![int(10)]),
                ],
            ),
            let_(
                1,
                call_closure(Expr::Field(Local(0), 0), vec![int(7)]),
                let_(
                    2,
                    call_closure(Expr::Field(Local(0), 1), vec![local(1)]),
                    let_(3, drop_(0), local(2)),
                ),
            ),
        ),
    );
    with_closures(program(vec![main, double(), add_k()]), vec![MTy::Int])
}

/// A closure that captures a record and is called twice: the second call frees
/// it, and the capture with it.
fn capturing_a_record() -> Program {
    let body = closure_fn(
        vec![(0, MTy::Int)],
        1,
        vec![record_ty()],
        MTy::Int,
        let_(
            2,
            Expr::Capture(0),
            let_(
                3,
                Expr::Field(Local(2), 0),
                let_(4, drop_(2), let_(5, drop_(1), add(local(3), local(0)))),
            ),
        ),
    );
    let main = func(
        MTy::Int,
        let_(
            0,
            alloc_record(7),
            let_(
                1,
                Expr::MakeClosure(FuncId(1), vec![local(0)]),
                let_(
                    2,
                    Expr::Dup(Local(1)),
                    let_(
                        3,
                        call_closure(local(1), vec![int(5)]),
                        let_(
                            4,
                            call_closure(local(1), vec![int(1)]),
                            add(local(3), local(4)),
                        ),
                    ),
                ),
            ),
        ),
    );
    with_closures(program(vec![main, body]), vec![MTy::Int])
}

#[test]
fn closures_match_golden() {
    golden("closures", &record_of_functions());
    golden("capturing_closure", &capturing_a_record());
}

#[test]
fn closure_code_is_tailcc_and_calls_through_the_closure() {
    let ir = ll(&apply_double());
    assert!(
        ir.contains("define internal tailcc i64 @goat_f1(ptr %inst, ptr %env, i64 %l0)"),
        "{ir}"
    );
    assert!(ir.contains("call tailcc i64 %"), "{ir}");
    assert!(ir.contains("@goat.static."), "an immortal closure: {ir}");
}

#[test]
fn the_call_depth_counter_is_emitted_only_on_the_embedded_profile() {
    let wide = ll(&apply_double());
    assert!(!wide.contains("icmp ugt i32"), "{wide}");
    let narrow = ll(&embedded(apply_double()));
    assert!(narrow.contains("icmp ugt i32 %"), "{narrow}");
    assert!(narrow.contains("the program called itself too deeply"));
    let limited = emit_with_options(
        &embedded(apply_double()),
        EmitOptions {
            call_depth: 7,
            ..CHECKED
        },
    )
    .unwrap();
    assert!(limited.contains(", 7\n"), "{limited}");
}

#[test]
fn heap_programs_match_golden() {
    golden("heap", &heap());
    golden("strings", &strings());
}

#[test]
fn poison_is_emitted_only_when_asked_for() {
    let p = heap();
    let poisoned = emit_with_options(&p, CHECKED).unwrap();
    let plain = emit_with_options(
        &p,
        EmitOptions {
            poison_freed: false,
            ..CHECKED
        },
    )
    .unwrap();
    assert!(poisoned.contains("llvm.memset"), "{poisoned}");
    assert!(!plain.contains("llvm.memset"), "{plain}");
    for ir in [&poisoned, &plain] {
        assert!(ir.contains("a heap block was released twice"));
        assert!(ir.contains("a freed heap block was written to"));
    }
}

#[test]
fn heap_ir_keeps_its_state_in_the_instance() {
    for p in [
        heap(),
        strings(),
        embedded(heap()),
        capturing_a_record(),
        record_of_functions(),
    ] {
        let ir = ll(&p);
        assert!(
            !ir.lines()
                .any(|l| l.starts_with('@') && l.contains(" global ")),
            "{ir}"
        );
        for line in ir.lines().filter(|l| l.starts_with("define ")) {
            assert!(line.contains(" nounwind "), "{line}");
        }
    }
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
        ("heap", heap()),
        ("strings", strings()),
        ("apply_double", apply_double()),
        ("record_of_functions", record_of_functions()),
        ("capturing_a_record", capturing_a_record()),
        ("embedded_closures", embedded(record_of_functions())),
        ("embedded_heap", embedded(heap())),
        ("embedded_strings", embedded(strings())),
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
struct host { uint32_t version; void *fns[SLOTS]; };
struct instance {
    uint32_t version, live, depth, site_start, site_end;
    void *heap; uint64_t heap_size; void *host; void *ctx; uint64_t spill[8];
    uint64_t heap_top, allocs; void *free_lists[FREE_LISTS];
};
static void trap(void *ctx, const char *message, uint64_t len) {
    struct instance *inst = ctx;
    printf("trap: %.*s", (int)len, message);
    if (inst->site_start != UINT32_MAX) printf(" at %u..%u", inst->site_start, inst->site_end);
    printf("\n");
    exit(0);
}
extern RET goat_entry_c(void *inst);
int main(void) {
    struct host host = { .version = 1 };
    host.fns[TRAP_SLOT] = (void *)trap;
    struct instance inst = { .version = 1, .site_start = UINT32_MAX };
    inst.host = &host;
    inst.ctx = &inst;
    printf(FMT "\n", (CAST)goat_entry_c(&inst));
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
    let (c_ty, fmt, cast, ll_ty) = match ret {
        Ret::Int => ("int64_t", "\"%lld\"", "long long", "i64"),
        Ret::Int32 => ("int32_t", "\"%d\"", "int", "i32"),
        Ret::Float => ("double", "\"%.17g\"", "double", "double"),
        Ret::Bool => ("_Bool", "\"%d\"", "int", "zeroext i1"),
    };
    let dir = scratch(name);
    let (ll_path, c_path, exe) = (dir.join("p.ll"), dir.join("main.c"), dir.join("p"));
    // `goat_entry` is `tailcc`, which C cannot call, so the harness calls a
    // C-convention wrapper.
    let bare = ll_ty.trim_start_matches("zeroext ");
    let wrapper = format!(
        "\ndefine {ll_ty} @goat_entry_c(ptr %inst) nounwind {{\n  \
         %r = call tailcc {bare} @goat_entry(ptr %inst)\n  ret {bare} %r\n}}\n"
    );
    std::fs::write(&ll_path, ll(p) + &wrapper).unwrap();
    std::fs::write(&c_path, HARNESS).unwrap();
    let build = Command::new(clang)
        .arg(format!("-DRET={c_ty}"))
        .arg(format!("-DFMT={fmt}"))
        .arg(format!("-DCAST={cast}"))
        .arg(format!("-DSLOTS={}", goat_llvm::HOST_FUNCTIONS.len()))
        .arg(format!("-DFREE_LISTS={}", goat_llvm::FREE_LISTS))
        .arg(format!("-DTRAP_SLOT={}", trap_slot()))
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

fn trap_slot() -> usize {
    goat_llvm::HOST_FUNCTIONS
        .iter()
        .position(|f| *f == "trap")
        .unwrap()
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
fn a_static_closure_is_called_through_its_code_word() {
    let Some(clang) = clang() else { return };
    assert_eq!(run(clang, "static", &apply_double(), Ret::Int), "42");
    let narrow = run(clang, "static32", &embedded(apply_double()), Ret::Int32);
    assert_eq!(narrow, "42");
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

#[test]
fn a_trap_reports_the_current_site_from_the_instance() {
    let Some(clang) = clang() else { return };
    let body = let_(0, Expr::Site(3, 9), int_op(IntOp::Div, 1, 0));
    let got = run(clang, "site", &int_program(body), Ret::Int);
    assert_eq!(got, format!("trap: {DIVISION_BY_ZERO} at 3..9"));
}

#[test]
fn the_ir_has_no_global_state_and_no_external_trap() {
    let ir = ll(&int_program(int_op(IntOp::Div, 1, 0)));
    assert!(!ir.contains("@goat_trap"), "{ir}");
    assert!(
        !ir.lines()
            .any(|l| l.starts_with('@') && l.contains(" global "))
    );
    assert!(ir.contains("define i32 @goat_main(ptr %host, ptr %ctx, ptr %inst)"));
}

#[test]
fn the_layout_probe_reads_in_clang() {
    let Some(clang) = clang() else { return };
    let path = scratch("probe").join("probe.ll");
    std::fs::write(&path, goat_llvm::layout_probe()).unwrap();
    let out = Command::new(clang)
        .args(["-x", "ir", "-c", "-o", "/dev/null"])
        .arg(&path)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}

fn compiled(profile: Profile, source: &str) -> Program {
    let checked = goat_checker::check(source).expect("type-checks");
    let program = goat_mir::mono_for(&checked, profile).expect("monomorphizes");
    assert_eq!(verify(&program), Ok(()), "{source}");
    program
}

const COUNT: &str = "count = program(n, acc) do if n == 0 then acc else count(n - 1, acc + 1) done done\n\
                     count(10, 0) + 0";

const PARITY: &str = "is_even = program(n) do if n < 1 then true else is_odd(n - 1, 0) done done\n\
                      is_odd = program(n, flag) do if n < 1 then false else is_even(n - 1) done done\n\
                      if is_even(10) then 1 else 0 done";

const BOUNCE: &str = "bounce = program(f, n, a, b, c, d, g, h) do if n < 1 then a else f(n - 1, a + 1, b, c, d, g, h) done done\n\
                      go = program(n, a, b, c, d, g, h) do bounce(program(m, a, b, c, d, g, h) do go(m, a, b, c, d, g, h) done, n, a, b, c, d, g, h) done\n\
                      go(10, 0, 0, 0, 0, 0, 0) + 0";

fn abi(int_registers: usize, float_registers: usize, musttail: bool) -> EmitOptions {
    EmitOptions {
        abi: goat_llvm::Abi {
            int_registers,
            float_registers,
            musttail,
        },
        ..CHECKED
    }
}

#[test]
fn a_self_tail_call_is_a_loop() {
    let ir = emit_with_options(&compiled(Profile::Desktop, COUNT), CHECKED).unwrap();
    assert!(ir.contains("br label %loop"), "{ir}");
    assert!(ir.contains("phi i64"), "{ir}");
    assert!(!ir.contains("musttail"), "{ir}");
    golden("tail_self_loop", &compiled(Profile::Desktop, COUNT));
}

#[test]
fn functions_joined_by_tail_calls_are_one_function_with_a_switch() {
    let program = compiled(Profile::Desktop, PARITY);
    let ir = emit_with_options(&program, CHECKED).unwrap();
    assert!(
        ir.contains("tailcc i1 @goat_g0(ptr %inst, i32 %in_which"),
        "{ir}"
    );
    assert!(ir.contains("switch i32 %which"), "{ir}");
    assert!(!ir.contains("musttail"), "{ir}");
    assert!(!ir.contains("define internal tailcc i1 @goat_f"), "{ir}");
    golden("tail_group", &program);
}

#[test]
fn a_tail_call_through_a_closure_is_musttail() {
    let ir = emit_with_options(&compiled(Profile::Desktop, BOUNCE), CHECKED).unwrap();
    assert!(ir.contains("musttail call tailcc i64 %"), "{ir}");
}

#[test]
fn arguments_past_the_register_budget_go_through_the_spill_area() {
    let program = compiled(Profile::Desktop, BOUNCE);
    let spill_slot = goat_llvm::INSTANCE_FIELDS
        .iter()
        .position(|(field, _)| *field == "spill")
        .unwrap();
    let spill = format!("i32 0, i32 {spill_slot}, i32");
    let roomy = emit_with_options(&program, abi(16, 16, true)).unwrap();
    let cramped = emit_with_options(&program, abi(3, 1, true)).unwrap();
    assert!(!roomy.contains(&spill), "{roomy}");
    assert!(cramped.contains(&spill), "{cramped}");
    golden_with("tail_spill", &program, abi(3, 1, true));
}

#[test]
fn a_call_with_more_arguments_than_the_spill_area_holds_is_unsupported() {
    let many = "f = program(a, b, c, d, e, g, h, i, j, k, l, m) do a + b + c + d + e + g + h + i + j + k + l + m done\n\
                f(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12)";
    let program = compiled(Profile::Desktop, many);
    assert!(matches!(
        emit_with_options(&program, abi(2, 1, true)),
        Err(EmitError::Unsupported(_))
    ));
    assert!(emit_with_options(&program, CHECKED).is_ok());
}

#[test]
fn a_target_without_tail_calls_refuses_the_ones_that_are_not_loops() {
    let options = abi(6, 8, false);
    let error = emit_with_options(&compiled(Profile::Desktop, BOUNCE), options).unwrap_err();
    assert!(
        error.to_string().contains("guaranteed tail calls"),
        "{error}"
    );
    for source in [COUNT, PARITY] {
        assert!(emit_with_options(&compiled(Profile::Desktop, source), options).is_ok());
    }
}

#[test]
fn clang_reads_the_tail_call_programs() {
    let Some(clang) = clang() else { return };
    for (name, source, options) in [
        ("count", COUNT, CHECKED),
        ("parity", PARITY, CHECKED),
        ("bounce", BOUNCE, CHECKED),
        ("bounce_tight", BOUNCE, abi(3, 1, true)),
    ] {
        for profile in [Profile::Desktop, Profile::Embedded] {
            let ir = emit_with_options(&compiled(profile, source), options).unwrap();
            let path = scratch("tail").join(format!("{name}.ll"));
            std::fs::write(&path, ir).unwrap();
            for target in ["x86_64-unknown-linux-gnu", "aarch64-apple-darwin"] {
                let out = Command::new(clang)
                    .args(["-target", target, "-x", "ir", "-c", "-o", "/dev/null"])
                    .arg(&path)
                    .output()
                    .unwrap();
                assert!(
                    out.status.success(),
                    "{name} on {profile:?} for {target}: {}",
                    String::from_utf8_lossy(&out.stderr)
                );
            }
        }
    }
}
