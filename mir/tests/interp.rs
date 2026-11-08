mod common;

use common::*;
use goat_mir::*;

fn run_verified(p: &Program) -> Outcome {
    assert_eq!(verify(p), Ok(()));
    run(p).expect("program runs")
}

#[test]
fn adds_two_numbers_with_no_live_allocations() {
    let p = program(vec![func(MTy::Int, add(int(1), int(2)))]);
    assert_eq!(
        run_verified(&p),
        Outcome {
            value: Value::Int(3),
            live_allocations: 0,
            allocations: 0,
            root_string: None,
            printed: Vec::new(),
        }
    );
}

#[test]
fn int_arithmetic_traps_where_it_overflows() {
    let trap = |body| run(&program(vec![func(MTy::Int, body)])).expect_err("traps");
    let overflow = InterpError::Trap(INT_OVERFLOW.into());
    assert_eq!(trap(add(int(i64::MAX), int(1))), overflow);
    assert_eq!(trap(sub(int(i64::MIN), int(1))), overflow);
    assert_eq!(trap(mul(int(i64::MAX), int(2))), overflow);
    let divide = |a, b| Expr::BinInt(IntOp::Div, Box::new(int(a)), Box::new(int(b)));
    assert_eq!(trap(divide(i64::MIN, -1)), overflow);
    assert_eq!(
        trap(divide(1, 0)),
        InterpError::Trap(DIVISION_BY_ZERO.into())
    );
    let fits = |body| run_verified(&program(vec![func(MTy::Int, body)])).value;
    assert_eq!(fits(add(int(i64::MAX - 1), int(1))), Value::Int(i64::MAX));
    assert_eq!(fits(mul(int(i64::MIN), int(1))), Value::Int(i64::MIN));
}

#[test]
fn floor_division_and_remainder_round_toward_negative_infinity() {
    let run_op = |op, a, b| {
        let body = Expr::BinInt(op, Box::new(int(a)), Box::new(int(b)));
        run(&program(vec![func(MTy::Int, body)])).map(|out| out.value)
    };
    for (a, b, quotient, remainder) in [
        (7, 2, 3, 1),
        (-7, 2, -4, 1),
        (7, -2, -4, -1),
        (-7, -2, 3, -1),
        (6, -3, -2, 0),
        (-6, 3, -2, 0),
        (0, 5, 0, 0),
        (i64::MIN, 1, i64::MIN, 0),
        (i64::MIN, -1, 0, 0),
        (i64::MAX, -1, -i64::MAX, 0),
    ] {
        if (a, b) != (i64::MIN, -1) {
            assert_eq!(
                run_op(IntOp::FloorDiv, a, b),
                Ok(Value::Int(quotient)),
                "{a} // {b}"
            );
        }
        assert_eq!(
            run_op(IntOp::Mod, a, b),
            Ok(Value::Int(remainder)),
            "{a} % {b}"
        );
    }
    let overflow = InterpError::Trap(INT_OVERFLOW.into());
    assert_eq!(run_op(IntOp::FloorDiv, i64::MIN, -1), Err(overflow));
    let zero = InterpError::Trap(DIVISION_BY_ZERO.into());
    assert_eq!(run_op(IntOp::FloorDiv, 1, 0), Err(zero.clone()));
    assert_eq!(run_op(IntOp::Mod, 1, 0), Err(zero));
}

#[test]
fn a_float_function_takes_a_float_and_traps_where_no_int_fits() {
    let apply = |function, value| {
        let body = Expr::FloatFn(function, Box::new(value));
        let ret = match function {
            FloatFn::Sqrt => MTy::Float,
            FloatFn::Truncate => MTy::Int,
        };
        run(&program(vec![func(ret, body)])).map(|out| out.value)
    };
    assert_eq!(apply(FloatFn::Sqrt, float(2.25)), Ok(Value::Float(1.5)));
    assert_eq!(apply(FloatFn::Truncate, float(-2.9)), Ok(Value::Int(-2)));
    assert_eq!(apply(FloatFn::Truncate, float(2.9)), Ok(Value::Int(2)));
    let too_big = InterpError::Trap(NOT_A_WHOLE_NUMBER.into());
    for bad in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, 9.3e18, -9.3e18] {
        assert_eq!(
            apply(FloatFn::Truncate, float(bad)),
            Err(too_big.clone()),
            "{bad}"
        );
    }
    let edge = apply(FloatFn::Truncate, float(-9_223_372_036_854_775_808.0));
    assert_eq!(edge, Ok(Value::Int(i64::MIN)));
    let p = program(vec![func(
        MTy::Float,
        Expr::FloatFn(FloatFn::Sqrt, Box::new(int(4))),
    )]);
    assert!(verify(&p).is_err());
}

#[test]
fn an_int_widens_to_the_float_nearest_it() {
    let widen = |body| Expr::IntToFloat(Box::new(body));
    let p = program(vec![func(MTy::Float, widen(int(3)))]);
    assert_eq!(run_verified(&p).value, Value::Float(3.0));
    let p = program(vec![func(MTy::Float, widen(float(1.5)))]);
    assert_eq!(
        verify(&p),
        Err(vec![VerifyError {
            func: FuncId(0),
            kind: ErrorKind::TypeMismatch {
                expected: MTy::Int,
                found: MTy::Float
            }
        }])
    );
}

#[test]
fn a_number_prints_whether_it_is_an_int_or_a_float() {
    let write = |value| Expr::Write(Write::Number(Box::new(value)));
    let end = Expr::Write(Write::End);
    let body = let_(0, write(int(7)), let_(1, end, float(0.5)));
    let out = run_verified(&program(vec![func(MTy::Float, body)]));
    assert_eq!(out.printed, [vec![Piece::Int(7)]]);
}

#[test]
fn record_round_trip_frees_everything() {
    let body = let_(
        0,
        alloc_record(41),
        let_(
            1,
            Expr::Field(Local(0), 0),
            let_(2, Expr::Drop(Local(0)), add(local(1), int(1))),
        ),
    );
    let out = run_verified(&program(vec![func(MTy::Int, body)]));
    assert_eq!((out.value, out.live_allocations), (Value::Int(42), 0));
}

#[test]
fn dup_keeps_object_alive_until_last_drop() {
    let body = let_(
        0,
        alloc_record(1),
        let_(
            1,
            Expr::Dup(Local(0)),
            let_(
                2,
                Expr::Drop(Local(0)),
                let_(3, Expr::Drop(Local(0)), int(0)),
            ),
        ),
    );
    assert_eq!(
        run_verified(&program(vec![func(MTy::Int, body)])).live_allocations,
        0
    );
}

#[test]
fn reports_leaked_allocation() {
    let body = let_(0, alloc_record(1), int(0));
    let out = run(&program(vec![func(MTy::Int, body)])).unwrap();
    assert_eq!(out.live_allocations, 1);
}

#[test]
fn detects_double_free() {
    let body = let_(
        0,
        alloc_record(1),
        let_(
            1,
            Expr::Drop(Local(0)),
            let_(2, Expr::Drop(Local(0)), int(0)),
        ),
    );
    assert_eq!(
        run(&program(vec![func(MTy::Int, body)])),
        Err(InterpError::DoubleFree(0))
    );
}

#[test]
fn detects_use_after_free() {
    let body = let_(
        0,
        alloc_record(1),
        let_(1, Expr::Drop(Local(0)), Expr::Field(Local(0), 0)),
    );
    assert_eq!(
        run(&program(vec![func(MTy::Int, body)])),
        Err(InterpError::UseAfterFree(0))
    );
}

#[test]
fn trap_aborts_with_message() {
    let p = program(vec![func(MTy::Int, Expr::Trap("boom".into()))]);
    assert_eq!(run(&p), Err(InterpError::Trap("boom".into())));
}

#[test]
fn closure_reads_capture_and_frees_environment() {
    let mut p = program(vec![]);
    p.sigs = vec![Sig {
        params: vec![MTy::Int],
        ret: MTy::Int,
    }];
    let adder = Func {
        params: vec![(Local(0), MTy::Int)],
        env: Some(Env {
            local: Local(1),
            sig: SigId(0),
            captures: vec![MTy::Int],
        }),
        ret: MTy::Int,
        body: let_(
            2,
            Expr::Capture(0),
            let_(3, Expr::Drop(Local(1)), add(local(0), local(2))),
        ),
        locals: Default::default(),
    };
    let main = func(
        MTy::Int,
        let_(
            0,
            Expr::MakeClosure(FuncId(1), vec![int(10)]),
            Expr::CallClosure(Box::new(local(0)), vec![int(5)]),
        ),
    );
    p.funcs = vec![main, adder];
    let out = run_verified(&p);
    assert_eq!((out.value, out.live_allocations), (Value::Int(15), 0));
}

#[test]
fn tail_call_runs_in_constant_stack() {
    // count(n) = if n == 0 { 0 } else { count(n - 1) }
    let count = Func {
        params: vec![(Local(0), MTy::Int)],
        env: None,
        ret: MTy::Int,
        body: Expr::If(
            Box::new(Expr::Cmp(CmpOp::Eq, Box::new(local(0)), Box::new(int(0)))),
            Box::new(int(0)),
            Box::new(Expr::TailCall(
                Callee::Direct(FuncId(1)),
                vec![Expr::BinInt(
                    IntOp::Sub,
                    Box::new(local(0)),
                    Box::new(int(1)),
                )],
            )),
        ),
        locals: Default::default(),
    };
    let main = func(MTy::Int, Expr::CallDirect(FuncId(1), vec![int(100_000)]));
    let out = run_verified(&program(vec![main, count]));
    assert_eq!(out.value, Value::Int(0));
}

#[test]
fn unbounded_non_tail_recursion_overflows() {
    let recur = func(MTy::Int, Expr::CallDirect(FuncId(1), vec![]));
    let main = func(MTy::Int, Expr::CallDirect(FuncId(1), vec![]));
    assert_eq!(
        run(&program(vec![main, recur])),
        Err(InterpError::StackOverflow)
    );
}

#[test]
fn a_loop_that_allocates_without_end_runs_out_of_memory() {
    // leak(n) = { _ = {n}; leak(n + 1) }
    let leak = Func {
        params: vec![(Local(0), MTy::Int)],
        env: None,
        ret: MTy::Int,
        body: let_(
            1,
            Expr::AllocRecord(RECORD, vec![local(0)]),
            Expr::TailCall(Callee::Direct(FuncId(1)), vec![add(local(0), int(1))]),
        ),
        locals: Default::default(),
    };
    let main = func(MTy::Int, Expr::CallDirect(FuncId(1), vec![int(0)]));
    assert_eq!(
        run_with_object_limit(&program(vec![main, leak]), 10_000),
        Err(InterpError::OutOfMemory)
    );
}

#[test]
fn switch_selects_arm_by_tag_and_reads_payload() {
    let body = let_(
        0,
        Expr::AllocVariant(VARIANT, 1, vec![int(7)]),
        let_(
            1,
            Expr::Switch(
                Local(0),
                vec![(0, int(0))],
                Box::new(Expr::Payload(Local(0), 1, 0)),
            ),
            let_(2, Expr::Drop(Local(0)), local(1)),
        ),
    );
    let out = run_verified(&program(vec![func(MTy::Int, body)]));
    assert_eq!((out.value, out.live_allocations), (Value::Int(7), 0));
}

#[test]
fn string_literal_root_carries_its_bytes_and_is_immortal() {
    let mut p = program(vec![func(MTy::Ptr(HeapKind::Str), Expr::StrLit(DataId(0)))]);
    p.data = vec![b"hello".to_vec()];
    let out = run_verified(&p);
    assert_eq!(out.root_string, Some(b"hello".to_vec()));
    assert_eq!((out.live_allocations, out.allocations), (0, 0));
}

#[test]
fn empty_string_root_is_some_empty() {
    let mut p = program(vec![func(MTy::Ptr(HeapKind::Str), Expr::StrLit(DataId(0)))]);
    p.data = vec![Vec::new()];
    assert_eq!(run_verified(&p).root_string, Some(Vec::new()));
}

#[test]
fn string_literal_with_missing_data_is_malformed() {
    let p = program(vec![func(MTy::Ptr(HeapKind::Str), Expr::StrLit(DataId(0)))]);
    assert_eq!(run(&p), Err(InterpError::Malformed("unknown data")));
}

#[test]
fn non_string_roots_have_no_string() {
    let out = run_verified(&program(vec![func(MTy::Int, int(1))]));
    assert_eq!(out.root_string, None);
}

fn embedded(funcs: Vec<Func>) -> Program {
    Program {
        profile: Profile::Embedded,
        ..program(funcs)
    }
}

#[test]
fn an_embedded_int_traps_where_it_leaves_i32() {
    let trap = |body| run(&embedded(vec![func(MTy::Int, body)])).expect_err("traps");
    let overflow = InterpError::Trap(INT_OVERFLOW.into());
    let max = i64::from(i32::MAX);
    let min = i64::from(i32::MIN);
    assert_eq!(trap(add(int(max), int(1))), overflow);
    assert_eq!(trap(sub(int(min), int(1))), overflow);
    assert_eq!(trap(mul(int(65536), int(32768))), overflow);
    let divide = |a, b| Expr::BinInt(IntOp::Div, Box::new(int(a)), Box::new(int(b)));
    assert_eq!(trap(divide(min, -1)), overflow);
    let fits = |body| {
        run(&embedded(vec![func(MTy::Int, body)]))
            .expect("runs")
            .value
    };
    assert_eq!(fits(add(int(max - 1), int(1))), Value::Int(max));
    assert_eq!(fits(sub(int(min + 1), int(1))), Value::Int(min));
    assert_eq!(fits(mul(int(46340), int(46340))), Value::Int(2_147_395_600));
    assert_eq!(
        run(&program(vec![func(MTy::Int, add(int(max), int(1)))])).map(|o| o.value),
        Ok(Value::Int(max + 1)),
        "the same sum fits on desktop"
    );
}

#[test]
fn an_embedded_float_rounds_to_f32_after_each_operation() {
    let sum = bin_float(FloatOp::Add, float(16_777_216.0), float(1.0));
    let value = |p: Program| run(&p).expect("runs").value;
    assert_eq!(
        value(embedded(vec![func(MTy::Float, sum.clone())])),
        Value::Float(16_777_216.0)
    );
    assert_eq!(
        value(program(vec![func(MTy::Float, sum)])),
        Value::Float(16_777_217.0)
    );
    let tenth = value(embedded(vec![func(MTy::Float, float(0.1))]));
    assert_eq!(tenth, Value::Float(f64::from(0.1_f32)));
    let widen = Expr::IntToFloat(Box::new(int(16_777_217)));
    assert_eq!(
        value(embedded(vec![func(MTy::Float, widen)])),
        Value::Float(16_777_216.0)
    );
}
