mod common;

use common::*;
use goat_mir::*;

const STR: MTy = MTy::Ptr(HeapKind::Str);

fn count(e: &Expr, pred: &impl Fn(&Expr) -> bool) -> usize {
    let mut n = usize::from(pred(e));
    e.for_each_child(&mut |c| n += count(c, pred));
    n
}

fn dups(e: &Expr) -> usize {
    count(e, &|e| matches!(e, Expr::Dup(_)))
}

fn drops(e: &Expr) -> usize {
    count(e, &|e| matches!(e, Expr::Drop(_)))
}

fn calls(e: &Expr) -> Vec<FuncId> {
    fn walk(e: &Expr, out: &mut Vec<FuncId>) {
        if let Expr::CallDirect(f, _) = e {
            out.push(*f);
        }
        e.for_each_child(&mut |c| walk(c, out));
    }
    let mut out = Vec::new();
    walk(e, &mut out);
    out
}

/// Insert RC into `p`, then require the verifier to accept it.
fn rc(mut p: Program) -> Program {
    infer_locals(&mut p);
    insert_rc(&mut p);
    assert_eq!(verify(&p), Ok(()), "{p:#?}");
    p
}

fn run_clean(p: &Program) -> Outcome {
    let out = run(p).expect("runs");
    assert_eq!(out.live_allocations, 0, "{p:#?}");
    out
}

fn entry(p: &Program) -> &Expr {
    &p.funcs[0].body
}

fn binary_record_fn() -> Func {
    func_with(
        vec![(0, record_ty()), (1, record_ty())],
        MTy::Int,
        add(Expr::Field(Local(0), 0), Expr::Field(Local(1), 0)),
    )
}

#[test]
fn a_record_used_twice_is_dupped_once() {
    let body = let_(0, alloc_record(5), call(1, vec![local(0), local(0)]));
    let p = rc(program(vec![func(MTy::Int, body), binary_record_fn()]));
    assert_eq!(dups(entry(&p)), 1);
    assert_eq!(drops(entry(&p)), 0);
    assert_eq!(run_clean(&p).value, Value::Int(10));
}

#[test]
fn a_record_consumed_once_is_not_dupped() {
    let consume = func_with(vec![(0, record_ty())], MTy::Int, Expr::Field(Local(0), 0));
    let body = let_(0, alloc_record(5), call(1, vec![local(0)]));
    let p = rc(program(vec![func(MTy::Int, body), consume]));
    assert_eq!(dups(entry(&p)), 0);
    assert_eq!(drops(entry(&p)), 0);
    assert_eq!(run_clean(&p).value, Value::Int(5));
}

#[test]
fn an_unused_owned_local_is_dropped_right_after_its_binding() {
    let body = let_(0, alloc_record(5), int(1));
    let p = rc(program(vec![func(MTy::Int, body)]));
    let expected = let_(0, alloc_record(5), let_(1, drop_(0), int(1)));
    assert_eq!(entry(&p), &expected);
    run_clean(&p);
}

#[test]
fn an_unused_owned_param_is_dropped_on_entry() {
    let ignore = func_with(vec![(0, record_ty())], MTy::Int, int(3));
    let body = let_(0, alloc_record(5), call(1, vec![local(0)]));
    let p = rc(program(vec![func(MTy::Int, body), ignore]));
    assert_eq!(p.funcs[1].body, let_(1, drop_(0), int(3)));
    run_clean(&p);
}

#[test]
fn a_last_field_load_drops_its_record_afterwards() {
    let body = let_(0, alloc_record(5), Expr::Field(Local(0), 0));
    let p = rc(program(vec![func(MTy::Int, body)]));
    let expected = let_(
        0,
        alloc_record(5),
        let_(1, Expr::Field(Local(0), 0), let_(2, drop_(0), local(1))),
    );
    assert_eq!(entry(&p), &expected);
    assert_eq!(run_clean(&p).value, Value::Int(5));
}

#[test]
fn a_field_load_before_a_later_use_does_not_drop() {
    let body = let_(
        0,
        alloc_record(5),
        add(Expr::Field(Local(0), 0), call(1, vec![local(0)])),
    );
    let read = func_with(vec![(0, record_ty())], MTy::Int, Expr::Field(Local(0), 0));
    let p = rc(program(vec![func(MTy::Int, body), read]));
    assert_eq!(dups(entry(&p)), 0);
    assert_eq!(drops(entry(&p)), 0);
    assert_eq!(run_clean(&p).value, Value::Int(10));
}

#[test]
fn a_branch_that_does_not_use_a_local_drops_it_first() {
    for condition in [true, false] {
        let body = let_(
            0,
            alloc_record(5),
            if_(boolean(condition), Expr::Field(Local(0), 0), int(0)),
        );
        let p = rc(program(vec![func(MTy::Int, body)]));
        let Expr::Let(_, _, rest) = entry(&p) else {
            panic!("{p:#?}")
        };
        let Expr::If(_, then, otherwise) = &**rest else {
            panic!("{p:#?}")
        };
        assert!(
            matches!(&**otherwise, Expr::Let(_, d, body) if **d == drop_(0) && **body == int(0)),
            "{p:#?}"
        );
        assert_eq!(drops(then), 1);
        assert_eq!(
            run_clean(&p).value,
            Value::Int(if condition { 5 } else { 0 })
        );
    }
}

#[test]
fn a_branch_that_consumes_a_local_does_not_drop_it() {
    let consume = func_with(vec![(0, record_ty())], MTy::Int, Expr::Field(Local(0), 0));
    let body = let_(
        0,
        alloc_record(5),
        if_(boolean(true), call(1, vec![local(0)]), int(0)),
    );
    let p = rc(program(vec![func(MTy::Int, body), consume]));
    let Expr::Let(_, _, rest) = entry(&p) else {
        panic!("{p:#?}")
    };
    let Expr::If(_, then, otherwise) = &**rest else {
        panic!("{p:#?}")
    };
    assert_eq!(drops(then), 0);
    assert_eq!(drops(otherwise), 1);
    assert_eq!(run_clean(&p).value, Value::Int(5));
}

#[test]
fn a_local_needed_after_a_branch_is_dupped_where_the_branch_consumes_it() {
    let consume = func_with(vec![(0, record_ty())], MTy::Int, Expr::Field(Local(0), 0));
    let body = let_(
        0,
        alloc_record(5),
        let_(
            1,
            if_(boolean(true), call(1, vec![local(0)]), int(0)),
            add(local(1), Expr::Field(Local(0), 0)),
        ),
    );
    let p = rc(program(vec![func(MTy::Int, body), consume]));
    assert_eq!(dups(entry(&p)), 1);
    assert_eq!(run_clean(&p).value, Value::Int(10));
}

#[test]
fn a_string_literal_is_never_counted() {
    let two = func_with(vec![(0, STR), (1, STR)], MTy::Int, int(1));
    let mut p = program(vec![
        func(
            MTy::Int,
            let_(
                0,
                Expr::StrLit(DataId(0)),
                call(1, vec![local(0), local(0)]),
            ),
        ),
        two,
    ]);
    p.data = vec![b"hi".to_vec()];
    let p = rc(p);
    assert_eq!(dups(entry(&p)), 1);
    assert_eq!(drops(&p.funcs[1].body), 2);
    let out = run_clean(&p);
    assert_eq!(out.allocations, 0);
}

#[test]
fn a_string_root_is_handed_to_the_host_undropped() {
    let mut p = program(vec![func(STR, Expr::StrLit(DataId(0)))]);
    p.data = vec![b"hi".to_vec()];
    let p = rc(p);
    assert_eq!(p.funcs[0].ret, STR);
    assert_eq!(drops(entry(&p)), 0);
    assert_eq!(run_clean(&p).root_string, Some(b"hi".to_vec()));
}

#[test]
fn a_pointer_root_is_dropped_and_the_entry_returns_unit() {
    let p = rc(program(vec![func(record_ty(), alloc_record(5))]));
    assert_eq!(p.funcs[0].ret, MTy::Unit);
    assert_eq!(run_clean(&p).value, Value::Unit);
}

#[test]
fn a_closure_called_twice_is_dupped_for_the_first_call() {
    let p = with_closures(
        program(vec![
            func(
                MTy::Int,
                let_(
                    0,
                    Expr::MakeClosure(FuncId(1), vec![alloc_record(7)]),
                    add(
                        call_closure(local(0), vec![int(1)]),
                        call_closure(local(0), vec![int(2)]),
                    ),
                ),
            ),
            closure_fn(
                vec![(0, MTy::Int)],
                1,
                vec![record_ty()],
                MTy::Int,
                let_(2, Expr::Capture(0), add(Expr::Field(Local(2), 0), local(0))),
            ),
        ]),
        vec![MTy::Int],
    );
    let p = rc(p);
    assert_eq!(dups(entry(&p)), 1);
    assert_eq!(run_clean(&p).value, Value::Int(17));
}

#[test]
fn a_tail_call_drops_after_evaluating_its_operands() {
    let body = Expr::TailCall(Callee::Direct(FuncId(2)), vec![Expr::Field(Local(0), 0)]);
    let forward = func_with(vec![(0, record_ty())], MTy::Int, body);
    let id = func_with(vec![(0, MTy::Int)], MTy::Int, local(0));
    let entry_body = let_(0, alloc_record(9), call(1, vec![local(0)]));
    let p = rc(program(vec![func(MTy::Int, entry_body), forward, id]));
    // Field load into a temporary, then the deferred drop, then the call.
    let Expr::Let(t, load, rest) = &p.funcs[1].body else {
        panic!("{p:#?}")
    };
    let Expr::Let(_, release, call) = &**rest else {
        panic!("{p:#?}")
    };
    assert_eq!(**load, Expr::Field(Local(0), 0));
    assert_eq!(**release, drop_(0));
    assert_eq!(
        **call,
        Expr::TailCall(Callee::Direct(FuncId(2)), vec![Expr::Local(*t)])
    );
    assert_eq!(run_clean(&p).value, Value::Int(9));
}

#[test]
fn calls_keep_their_order_and_count() {
    let unit_fn = func_with(vec![(0, record_ty())], MTy::Unit, Expr::Const(Const::Unit));
    let body = let_(
        0,
        alloc_record(1),
        let_(
            1,
            call(1, vec![local(0)]),
            let_(2, alloc_record(2), let_(3, call(1, vec![local(2)]), int(0))),
        ),
    );
    let before = program(vec![func(MTy::Int, body), unit_fn]);
    let p = rc(before.clone());
    assert_eq!(calls(entry(&p)), calls(entry(&before)));
    run_clean(&p);
}

#[test]
fn a_cond_borrow_is_dropped_before_the_branches() {
    let body = let_(
        0,
        alloc_record(5),
        if_(
            cmp(CmpOp::Gt, Expr::Field(Local(0), 0), int(1)),
            int(1),
            int(2),
        ),
    );
    let p = rc(program(vec![func(MTy::Int, body)]));
    assert_eq!(drops(entry(&p)), 1);
    assert_eq!(run_clean(&p).value, Value::Int(1));
}

#[test]
fn a_variant_scrutinee_borrow_drops_in_arms_that_do_not_use_it() {
    let payload_sum = Expr::Payload(Local(0), 1, 0);
    let body = let_(
        0,
        Expr::AllocVariant(VARIANT, 1, vec![int(4)]),
        Expr::Switch(
            Local(0),
            vec![(0, int(0)), (1, payload_sum)],
            Box::new(int(9)),
        ),
    );
    let p = rc(program(vec![func(MTy::Int, body)]));
    assert_eq!(drops(entry(&p)), 3);
    assert_eq!(run_clean(&p).value, Value::Int(4));
}

fn from_source(src: &str) -> Program {
    let p = mono(&goat_checker::check(src).expect("checks")).expect("lowers");
    assert_eq!(verify(&p), Ok(()), "{src}");
    p
}

fn total(p: &Program, f: impl Fn(&Expr) -> usize) -> usize {
    p.funcs.iter().map(|func| f(&func.body)).sum()
}

#[test]
fn mono_output_dups_a_record_passed_twice() {
    let p = from_source("r = {a: 2}\nget = program(x) do x.a done\nget(r) * get(r)");
    assert_eq!(total(&p, dups), 1);
    assert_eq!(run_clean(&p).value, Value::Int(4));
}

#[test]
fn mono_output_dups_a_captured_closure_only_while_it_is_live() {
    let p = from_source(
        "r = {a: 2}\nmk = program(n) do program(m) do r.a + n + m done done\nf = mk(1)\nf(10) + f(20)",
    );
    assert!(total(&p, dups) >= 1);
    assert_eq!(run_clean(&p).value, Value::Int(36));
}

#[test]
fn mono_output_of_a_string_root_is_not_dropped() {
    let p = from_source("\"hi\"");
    assert_eq!(total(&p, drops), 0);
    assert_eq!(run_clean(&p).root_string, Some(b"hi".to_vec()));
}

fn foreign_program(body: Expr) -> Program {
    let mut p = program(vec![func(MTy::Int, body)]);
    p.foreign = vec![
        foreign_fn("greet", vec![], STR),
        foreign_fn("say", vec![STR], MTy::Unit),
        foreign_fn("forward", vec![MTy::Float], MTy::Unit),
    ];
    p
}

fn foreign_call(id: u32, args: &[u32]) -> Expr {
    Expr::CallForeign(ForeignId(id), args.iter().map(|&a| Local(a)).collect())
}

#[test]
fn a_unit_foreign_call_in_a_discard_position_is_kept_in_order() {
    // forward(1); forward(2); forward(3); 0, each result dead
    let call = |n: f64| foreign_call(2, &[n as u32]);
    let body = let_(
        10,
        float(1.0),
        let_(
            11,
            float(2.0),
            let_(
                12,
                float(3.0),
                let_(
                    20,
                    call(10.0),
                    let_(21, call(11.0), let_(22, call(12.0), int(0))),
                ),
            ),
        ),
    );
    let before = foreign_program(body);
    let after = rc(before.clone());
    let wanted = [Effect::Foreign(ForeignId(2)); 3];
    assert_eq!(effects(entry(&before)), wanted);
    assert_eq!(effects(entry(&after)), wanted);
    let mut host = Recorder::default();
    let out = run_with_host(&after, &mut host).expect("runs");
    assert_eq!(out.live_allocations, 0);
    let args: Vec<_> = host.calls.into_iter().map(|(_, a)| a).collect();
    assert_eq!(
        args,
        [
            vec![HostValue::Number(1.0)],
            vec![HostValue::Number(2.0)],
            vec![HostValue::Number(3.0)]
        ]
    );
}

#[test]
fn a_foreign_call_borrows_its_pointers_and_the_caller_drops_them() {
    // s = greet(); say(s); say(s); 1
    let body = let_(
        0,
        foreign_call(0, &[]),
        let_(
            1,
            foreign_call(1, &[0]),
            let_(2, foreign_call(1, &[0]), int(1)),
        ),
    );
    let p = rc(foreign_program(body));
    assert_eq!(dups(entry(&p)), 0, "borrowed, so no Dup");
    assert_eq!(drops(entry(&p)), 1, "dropped once, after the last call");
    assert_eq!(
        effects(entry(&p)),
        [
            Effect::Foreign(ForeignId(0)),
            Effect::Foreign(ForeignId(1)),
            Effect::Foreign(ForeignId(1)),
        ]
    );
    let mut host = Recorder::default();
    let out = run_with_host(&p, &mut host).expect("runs");
    assert_eq!((out.value, out.live_allocations), (Value::Int(1), 0));
    assert_eq!(out.allocations, 1);
}

#[test]
fn a_returned_string_that_is_never_used_is_still_released() {
    let p = rc(foreign_program(let_(0, foreign_call(0, &[]), int(7))));
    assert_eq!(effects(entry(&p)), [Effect::Foreign(ForeignId(0))]);
    let out = run_with_host(&p, &mut Recorder::default()).expect("runs");
    assert_eq!((out.value, out.live_allocations), (Value::Int(7), 0));
}

#[test]
fn a_foreign_call_in_each_branch_is_kept_in_each_branch() {
    // if true then (s = greet(); say(s); 1) else (forward(0); 2)
    let then = let_(
        0,
        foreign_call(0, &[]),
        let_(1, foreign_call(1, &[0]), int(1)),
    );
    let other = let_(2, float(0.0), let_(3, foreign_call(2, &[2]), int(2)));
    let p = rc(foreign_program(if_(boolean(true), then, other)));
    assert_eq!(
        effects(entry(&p)),
        [
            Effect::Foreign(ForeignId(0)),
            Effect::Foreign(ForeignId(1)),
            Effect::Foreign(ForeignId(2)),
        ]
    );
    let out = run_with_host(&p, &mut Recorder::default()).expect("runs");
    assert_eq!((out.value, out.live_allocations), (Value::Int(1), 0));
}
