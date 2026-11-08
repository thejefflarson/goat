mod common;

use common::*;
use goat_mir::*;
use std::collections::BTreeMap;

const LIST: LayoutId = LayoutId(2);
const FNS: LayoutId = LayoutId(3);

fn list_ty() -> MTy {
    MTy::Ptr(HeapKind::Variant(LIST))
}

fn closure_ty(sig: u32) -> MTy {
    MTy::Ptr(HeapKind::Closure(SigId(sig)))
}

fn sub(a: Expr, b: Expr) -> Expr {
    Expr::BinInt(IntOp::Sub, Box::new(a), Box::new(b))
}

fn mul(a: Expr, b: Expr) -> Expr {
    Expr::BinInt(IntOp::Mul, Box::new(a), Box::new(b))
}

fn cmp(op: CmpOp, a: Expr, b: Expr) -> Expr {
    Expr::Cmp(op, Box::new(a), Box::new(b))
}

fn if_(c: Expr, t: Expr, e: Expr) -> Expr {
    Expr::If(Box::new(c), Box::new(t), Box::new(e))
}

fn call(f: u32, args: Vec<Expr>) -> Expr {
    Expr::CallDirect(FuncId(f), args)
}

fn call_closure(closure: Expr, args: Vec<Expr>) -> Expr {
    Expr::CallClosure(Box::new(closure), args)
}

fn drop_(n: u32) -> Expr {
    Expr::Drop(Local(n))
}

fn params(params: Vec<(u32, MTy)>) -> Vec<(Local, MTy)> {
    params.into_iter().map(|(n, t)| (Local(n), t)).collect()
}

fn closure_fn(ps: Vec<(u32, MTy)>, env: u32, captures: Vec<MTy>, ret: MTy, body: Expr) -> Func {
    Func {
        params: params(ps),
        env: Some(Env {
            local: Local(env),
            sig: SigId(0),
            captures,
        }),
        ret,
        body,
        locals: Default::default(),
    }
}

fn plain_fn(ps: Vec<(u32, MTy)>, ret: MTy, body: Expr) -> Func {
    Func {
        params: params(ps),
        env: None,
        ret,
        body,
        locals: Default::default(),
    }
}

/// `\x -> x + k`, consuming its environment.
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

/// Every program has signature 0 and the list and function-record layouts.
fn build(funcs: Vec<Func>, sig_params: Vec<MTy>) -> Program {
    let mut p = program(funcs);
    p.sigs = vec![Sig {
        params: sig_params,
        ret: MTy::Int,
    }];
    p.layouts.push(Layout::Variant(BTreeMap::from([
        (0, vec![]),
        (1, vec![MTy::Int, list_ty()]),
    ])));
    p.layouts
        .push(Layout::Record(vec![closure_ty(0), closure_ty(0)]));
    p
}

fn list_of(items: &[i64]) -> Expr {
    items
        .iter()
        .rev()
        .fold(Expr::AllocVariant(LIST, 0, vec![]), |rest, &n| {
            Expr::AllocVariant(LIST, 1, vec![int(n), rest])
        })
}

fn check(p: &Program, value: i64) -> Outcome {
    assert_eq!(verify(p), Ok(()));
    let out = run(p).expect("program runs");
    assert_eq!(out.value, Value::Int(value));
    assert_eq!(out.live_allocations, 0, "leak or double free");
    out
}

#[test]
fn closure_captures_an_outer_heap_value() {
    // r = {7}; c = \x -> r.0 + x; c(5) + c(1)
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
    let out = check(&build(vec![main, body], vec![MTy::Int]), 20);
    assert_eq!(out.allocations, 2);
}

#[test]
fn self_recursive_closure_reaches_itself_through_env() {
    // go(n, acc) = if n == 0 then acc else go(n - 1, acc + k), k captured.
    let go = closure_fn(
        vec![(0, MTy::Int), (1, MTy::Int)],
        2,
        vec![MTy::Int],
        MTy::Int,
        if_(
            cmp(CmpOp::Eq, local(0), int(0)),
            let_(3, drop_(2), local(1)),
            let_(
                4,
                Expr::Capture(0),
                Expr::TailCall(
                    Callee::Closure(Box::new(local(2))),
                    vec![sub(local(0), int(1)), add(local(1), local(4))],
                ),
            ),
        ),
    );
    let main = func(
        MTy::Int,
        let_(
            0,
            Expr::MakeClosure(FuncId(1), vec![int(3)]),
            call_closure(local(0), vec![int(1000), int(0)]),
        ),
    );
    let out = check(&build(vec![main, go], vec![MTy::Int, MTy::Int]), 3000);
    assert_eq!(out.allocations, 1);
}

#[test]
fn non_tail_self_call_duplicates_env() {
    // f(n) = if n <= 0 then 0 else k + f(n - 1)
    let f = closure_fn(
        vec![(0, MTy::Int)],
        1,
        vec![MTy::Int],
        MTy::Int,
        if_(
            cmp(CmpOp::Le, local(0), int(0)),
            let_(2, drop_(1), int(0)),
            let_(
                3,
                Expr::Capture(0),
                let_(
                    4,
                    Expr::Dup(Local(1)),
                    let_(
                        5,
                        call_closure(local(1), vec![sub(local(0), int(1))]),
                        let_(6, drop_(1), add(local(3), local(5))),
                    ),
                ),
            ),
        ),
    );
    let main = func(
        MTy::Int,
        let_(
            0,
            Expr::MakeClosure(FuncId(1), vec![int(3)]),
            call_closure(local(0), vec![int(4)]),
        ),
    );
    check(&build(vec![main, f], vec![MTy::Int]), 12);
}

/// Consumes the cell and recurses on the tail, using `step` for the payload.
fn fold_list(self_id: u32, step: fn(Expr, Expr) -> Expr) -> Func {
    plain_fn(
        vec![(0, list_ty())],
        MTy::Int,
        Expr::Switch(
            Local(0),
            vec![(0, let_(1, drop_(0), int(0)))],
            Box::new(Expr::Unpack(
                Local(0),
                1,
                vec![Local(2), Local(3)],
                Box::new(let_(
                    4,
                    Expr::Free(Local(0)),
                    step(local(2), call(self_id, vec![local(3)])),
                )),
            )),
        ),
    )
}

fn length() -> Func {
    fold_list(1, |_head, rest| add(int(1), rest))
}

fn sum() -> Func {
    fold_list(2, add)
}

#[test]
fn recursive_length_over_empty_and_link() {
    let main = |items: &[i64]| func(MTy::Int, call(1, vec![list_of(items)]));
    let out = check(&build(vec![main(&[4, 5, 6]), length()], vec![]), 3);
    assert_eq!(out.allocations, 4);
    check(&build(vec![main(&[]), length()], vec![]), 0);
}

fn map() -> Func {
    plain_fn(
        vec![(0, closure_ty(0)), (1, list_ty())],
        list_ty(),
        Expr::Switch(
            Local(1),
            vec![(0, let_(2, drop_(0), local(1)))],
            Box::new(Expr::Unpack(
                Local(1),
                1,
                vec![Local(3), Local(4)],
                Box::new(let_(
                    5,
                    Expr::Dup(Local(0)),
                    let_(
                        6,
                        call_closure(local(0), vec![local(3)]),
                        let_(
                            7,
                            call(1, vec![local(0), local(4)]),
                            Expr::ReuseVariant(Local(1), LIST, 1, vec![local(6), local(7)]),
                        ),
                    ),
                )),
            )),
        ),
    )
}

fn map_program(main: Func) -> Program {
    build(vec![main, map(), sum(), add_k()], vec![MTy::Int])
}

#[test]
fn map_reuses_cells_of_a_uniquely_owned_list() {
    // sum(map(\x -> x + 10, [1, 2, 3]))
    let main = func(
        MTy::Int,
        let_(
            0,
            Expr::MakeClosure(FuncId(3), vec![int(10)]),
            call(2, vec![call(1, vec![local(0), list_of(&[1, 2, 3])])]),
        ),
    );
    // One closure plus four list cells; the mapped list recycles every cell.
    let out = check(&map_program(main), 36);
    assert_eq!(out.allocations, 5);
}

#[test]
fn map_copies_a_shared_list_and_leaves_the_original_intact() {
    let main = func(
        MTy::Int,
        let_(
            0,
            Expr::MakeClosure(FuncId(3), vec![int(10)]),
            let_(
                1,
                list_of(&[1, 2, 3]),
                let_(
                    2,
                    Expr::Dup(Local(1)),
                    let_(
                        3,
                        call(1, vec![local(0), local(1)]),
                        let_(
                            4,
                            call(2, vec![local(1)]),
                            let_(5, call(2, vec![local(3)]), add(local(4), local(5))),
                        ),
                    ),
                ),
            ),
        ),
    );
    // The five allocations above plus three fresh Link cells; the shared
    // Empty is returned as is.
    let out = check(&map_program(main), 6 + 36);
    assert_eq!(out.allocations, 8);
}

#[test]
fn record_of_functions_called_as_field_access() {
    // r = {double, add10}; r.1(r.0(7))
    let double = closure_fn(
        vec![(0, MTy::Int)],
        1,
        vec![],
        MTy::Int,
        let_(2, drop_(1), mul(local(0), int(2))),
    );
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
    let out = check(&build(vec![main, double, add_k()], vec![MTy::Int]), 24);
    assert_eq!(out.allocations, 3);
}
