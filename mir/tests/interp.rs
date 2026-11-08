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
