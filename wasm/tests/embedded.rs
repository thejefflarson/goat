//! The embedded profile at the wasm level: `Int` is an `i32` and `Float` an
//! `f32`, while `print_number` still takes an `f64` so one host serves both.

#[path = "../../mir/tests/common/mod.rs"]
mod common;

use common::*;
use goat_mir::*;
use goat_wasm::{EmitError, emit};

fn embedded(funcs: Vec<Func>) -> Program {
    Program {
        profile: Profile::Embedded,
        ..program(funcs)
    }
}

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

#[test]
fn an_int_is_an_i32_that_prints_through_an_f64() {
    let text = wat(&embedded(vec![func(MTy::Int, add(int(1), int(2)))]));
    assert!(text.contains("(result i32)"), "{text}");
    assert!(text.contains("i32.const 1"), "{text}");
    assert!(text.contains("f64.convert_i32_s"), "{text}");
    assert!(!text.contains("i64.const 1"), "{text}");
    assert!(
        text.contains("print_number\" (func (;0;) (type 0) (param f64))"),
        "{text}"
    );
}

#[test]
fn an_int_operation_runs_wide_and_traps_when_it_does_not_fit() {
    let text = wat(&embedded(vec![func(MTy::Int, add(int(1), int(2)))]));
    for op in ["i64.extend_i32_s", "i64.add", "i32.wrap_i64", "i64.ne"] {
        assert!(text.contains(op), "{op} missing:\n{text}");
    }
    let desktop = wat(&program(vec![func(MTy::Int, add(int(1), int(2)))]));
    assert!(!desktop.contains("i64.extend_i32_s"), "{desktop}");
}

#[test]
fn a_float_is_an_f32_that_prints_through_an_f64() {
    let sum = bin_float(FloatOp::Add, float(1.5), float(2.5));
    let text = wat(&embedded(vec![func(MTy::Float, sum)]));
    for op in ["(result f32)", "f32.const", "f32.add", "f64.promote_f32"] {
        assert!(text.contains(op), "{op} missing:\n{text}");
    }
    assert!(!text.contains("f64.add"), "{text}");
}

#[test]
fn float_functions_and_floor_division_use_the_narrow_instructions() {
    let sqrt = Expr::FloatFn(FloatFn::Sqrt, Box::new(float(2.0)));
    let text = wat(&embedded(vec![func(MTy::Float, sqrt)]));
    assert!(
        text.contains("f32.sqrt") && !text.contains("f64.sqrt"),
        "{text}"
    );

    let truncate = Expr::FloatFn(FloatFn::Truncate, Box::new(float(2.5)));
    let text = wat(&embedded(vec![func(MTy::Int, truncate)]));
    for op in ["f32.trunc", "i32.trunc_f32_s", "(result i32)"] {
        assert!(text.contains(op), "{op} missing:\n{text}");
    }
    assert!(!text.contains("i64.trunc_f64_s"), "{text}");

    for op in [IntOp::FloorDiv, IntOp::Mod] {
        let body = Expr::BinInt(op, Box::new(int(7)), Box::new(int(2)));
        let text = wat(&embedded(vec![func(MTy::Int, body)]));
        for want in ["i64.extend_i32_s", "i64.rem_s", "i32.wrap_i64"] {
            assert!(text.contains(want), "{want} missing:\n{text}");
        }
    }
}

#[test]
fn comparisons_and_widening_use_the_narrow_instructions() {
    let ints = cmp(CmpOp::Lt, int(1), int(2));
    assert!(wat(&embedded(vec![func(MTy::Bool, ints)])).contains("i32.lt_s"));
    let floats = cmp(CmpOp::Lt, float(1.0), float(2.0));
    assert!(wat(&embedded(vec![func(MTy::Bool, floats)])).contains("f32.lt"));
    let widened = Expr::IntToFloat(Box::new(int(3)));
    assert!(wat(&embedded(vec![func(MTy::Float, widened)])).contains("f32.convert_i32_s"));
}

#[test]
fn a_host_number_is_converted_at_the_boundary() {
    let mut p = embedded(vec![func_with(
        vec![(0, MTy::Float), (1, MTy::Int)],
        MTy::Int,
        Expr::CallForeign(ForeignId(0), vec![Local(0), Local(1)]),
    )]);
    p.foreign = vec![foreign_fn("pair", vec![MTy::Float, MTy::Int], MTy::Int)];
    p.funcs.insert(0, func(MTy::Unit, Expr::Const(Const::Unit)));
    p.entry = FuncId(0);
    let text = wat(&p);
    for op in ["f64.promote_f32", "i64.extend_i32_s", "i32.wrap_i64"] {
        assert!(text.contains(op), "{op} missing:\n{text}");
    }
    assert!(text.contains("(param f64 i64) (result i64)"), "{text}");
}

#[test]
fn an_int_constant_past_i32_is_malformed() {
    let p = embedded(vec![func(MTy::Int, int(i64::from(i32::MAX) + 1))]);
    assert_eq!(
        emit(&p),
        Err(EmitError::Malformed("int constant out of range"))
    );
}

#[test]
fn an_interactive_program_is_unsupported() {
    let mut p = embedded(vec![func(MTy::Unit, Expr::Const(Const::Unit))]);
    p.interactive = Some(Interactive {
        draw_slot: 0,
        init_slot: 1,
        update_slot: 2,
        update: FuncId(0),
        draw: FuncId(0),
        events: vec![],
        model: MTy::Unit,
    });
    assert!(matches!(emit(&p), Err(EmitError::Unsupported(_))));
}
