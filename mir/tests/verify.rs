mod common;

use common::*;
use goat_mir::*;
use std::collections::BTreeMap;

fn kinds(p: &Program) -> Vec<ErrorKind> {
    verify(p)
        .expect_err("expected verification to fail")
        .into_iter()
        .map(|e| e.kind)
        .collect()
}

fn main_returning_int(body: Expr) -> Program {
    program(vec![func(MTy::Int, body)])
}

#[test]
fn accepts_well_formed_program() {
    // let r = {1}; let v = r.0; drop r; v
    let body = let_(
        0,
        alloc_record(1),
        let_(
            1,
            Expr::Field(Local(0), 0),
            let_(2, Expr::Drop(Local(0)), local(1)),
        ),
    );
    assert_eq!(verify(&main_returning_int(body)), Ok(()));
}

#[test]
fn accepts_dup_then_two_consumes_and_balanced_branches() {
    let body = let_(
        0,
        alloc_record(1),
        let_(
            1,
            Expr::Dup(Local(0)),
            let_(
                2,
                Expr::Drop(Local(0)),
                Expr::If(
                    Box::new(Expr::Const(Const::Bool(true))),
                    Box::new(let_(3, Expr::Drop(Local(0)), int(1))),
                    Box::new(let_(4, Expr::Drop(Local(0)), int(2))),
                ),
            ),
        ),
    );
    assert_eq!(verify(&main_returning_int(body)), Ok(()));
}

#[test]
fn rejects_type_mismatch() {
    let body = add(int(1), Expr::Const(Const::Bool(true)));
    assert_eq!(
        kinds(&main_returning_int(body)),
        [ErrorKind::TypeMismatch {
            expected: MTy::Int,
            found: MTy::Bool
        }]
    );
}

#[test]
fn rejects_double_consumed_owned_pointer() {
    // Moving r into a, then moving it again into b.
    let body = let_(
        0,
        alloc_record(1),
        let_(
            1,
            local(0),
            let_(2, local(0), let_(3, Expr::Drop(Local(1)), int(0))),
        ),
    );
    let errors = kinds(&main_returning_int(body));
    assert!(
        errors.contains(&ErrorKind::UseAfterMove(Local(0))),
        "{errors:?}"
    );
}

#[test]
fn rejects_use_after_drop() {
    let body = let_(
        0,
        alloc_record(1),
        let_(1, Expr::Drop(Local(0)), Expr::Field(Local(0), 0)),
    );
    assert_eq!(
        kinds(&main_returning_int(body)),
        [ErrorKind::UseAfterDrop(Local(0))]
    );
}

#[test]
fn rejects_leaked_pointer() {
    let body = let_(0, alloc_record(1), int(0));
    assert_eq!(
        kinds(&main_returning_int(body)),
        [ErrorKind::Leak(Local(0))]
    );
}

#[test]
fn rejects_tail_call_outside_tail_position() {
    let callee = func(MTy::Int, int(0));
    let caller = func(
        MTy::Int,
        add(Expr::TailCall(Callee::Direct(FuncId(1)), vec![]), int(1)),
    );
    let errors = kinds(&program(vec![caller, callee]));
    assert!(errors.contains(&ErrorKind::TailCallNotInTail), "{errors:?}");
}

#[test]
fn rejects_branch_that_consumes_on_one_path_only() {
    let body = let_(
        0,
        alloc_record(1),
        Expr::If(
            Box::new(Expr::Const(Const::Bool(true))),
            Box::new(let_(1, Expr::Drop(Local(0)), int(1))),
            Box::new(int(2)),
        ),
    );
    let errors = kinds(&main_returning_int(body));
    assert!(
        errors.contains(&ErrorKind::BranchOwnershipMismatch(Local(0))),
        "{errors:?}"
    );
}

#[test]
fn rejects_duplicate_and_out_of_range_switch_arms() {
    let body = let_(
        0,
        Expr::AllocVariant(VARIANT, 0, vec![]),
        let_(
            1,
            Expr::Switch(
                Local(0),
                vec![
                    (0, Expr::Const(Const::Unit)),
                    (0, Expr::Const(Const::Unit)),
                    (7, Expr::Const(Const::Unit)),
                ],
                Box::new(Expr::Const(Const::Unit)),
            ),
            let_(2, Expr::Drop(Local(0)), int(0)),
        ),
    );
    let errors = kinds(&main_returning_int(body));
    assert!(
        errors.contains(&ErrorKind::DuplicateSwitchArm(0)),
        "{errors:?}"
    );
    assert!(errors.contains(&ErrorKind::BadTag(7)), "{errors:?}");
}

#[test]
fn rejects_non_bool_condition_and_mismatched_branches() {
    let body = Expr::If(
        Box::new(int(1)),
        Box::new(int(1)),
        Box::new(Expr::Const(Const::Unit)),
    );
    let errors = kinds(&main_returning_int(body));
    assert_eq!(errors.len(), 2, "{errors:?}");
}

fn unpack_then(body: Expr) -> Program {
    let unpack = Expr::Unpack(Local(0), 1, vec![Local(1)], Box::new(body));
    main_returning_int(let_(
        0,
        Expr::AllocVariant(VARIANT, 1, vec![int(5)]),
        unpack,
    ))
}

#[test]
fn unpack_token_must_be_consumed_by_free_or_reuse() {
    let freed = let_(2, Expr::Free(Local(0)), local(1));
    assert_eq!(verify(&unpack_then(freed)), Ok(()));

    let reused = let_(
        2,
        Expr::ReuseVariant(Local(0), VARIANT, 1, vec![int(9)]),
        let_(3, Expr::Drop(Local(2)), local(1)),
    );
    assert_eq!(verify(&unpack_then(reused)), Ok(()));

    assert_eq!(
        kinds(&unpack_then(local(1))),
        vec![ErrorKind::Leak(Local(0))]
    );
}

#[test]
fn unpack_token_cannot_be_used_as_a_value() {
    let errors = kinds(&unpack_then(let_(2, Expr::Drop(Local(0)), local(1))));
    assert!(
        errors.contains(&ErrorKind::UseAfterMove(Local(0))),
        "{errors:?}"
    );
}

#[test]
fn reuse_and_free_require_a_token() {
    let body = let_(
        0,
        Expr::AllocVariant(VARIANT, 1, vec![int(5)]),
        let_(1, Expr::Free(Local(0)), int(0)),
    );
    assert!(kinds(&main_returning_int(body)).contains(&ErrorKind::NotAToken(Local(0))));
}

#[test]
fn unpack_requires_sole_ownership() {
    let body = let_(
        0,
        Expr::AllocVariant(VARIANT, 1, vec![int(5)]),
        let_(
            2,
            Expr::Dup(Local(0)),
            Expr::Unpack(
                Local(0),
                1,
                vec![Local(1)],
                Box::new(let_(3, Expr::Free(Local(0)), local(1))),
            ),
        ),
    );
    assert!(kinds(&main_returning_int(body)).contains(&ErrorKind::NotUnique(Local(0))));
}

#[test]
fn reuse_rejects_a_differently_sized_cell() {
    let mut p = unpack_then(let_(
        2,
        Expr::ReuseVariant(Local(0), LayoutId(2), 0, vec![int(1), int(2)]),
        let_(3, Expr::Drop(Local(2)), local(1)),
    ));
    p.layouts.push(Layout::Variant(BTreeMap::from([(
        0,
        vec![MTy::Int, MTy::Int],
    )])));
    assert_eq!(
        kinds(&p),
        vec![ErrorKind::ReuseSizeMismatch {
            from: VARIANT,
            to: LayoutId(2)
        }]
    );
}

fn with_foreign(body: Expr) -> Program {
    let mut p = main_returning_int(body);
    p.foreign = vec![foreign_fn("double", vec![MTy::Float], MTy::Float)];
    p
}

#[test]
fn accepts_a_well_typed_foreign_call() {
    let body = let_(
        0,
        float(1.0),
        let_(1, Expr::CallForeign(ForeignId(0), vec![Local(0)]), int(1)),
    );
    assert_eq!(verify(&with_foreign(body)), Ok(()));
}

#[test]
fn rejects_a_malformed_foreign_call() {
    let unknown = Expr::CallForeign(ForeignId(3), vec![]);
    assert_eq!(
        kinds(&with_foreign(let_(0, unknown, int(1)))),
        [ErrorKind::UnknownForeign(ForeignId(3))]
    );
    let arity = let_(0, Expr::CallForeign(ForeignId(0), vec![]), int(1));
    assert_eq!(
        kinds(&with_foreign(arity)),
        [ErrorKind::ArityMismatch {
            expected: 1,
            found: 0
        }]
    );
    let wrong = let_(
        0,
        boolean(true),
        let_(1, Expr::CallForeign(ForeignId(0), vec![Local(0)]), int(1)),
    );
    assert_eq!(
        kinds(&with_foreign(wrong)),
        [ErrorKind::TypeMismatch {
            expected: MTy::Float,
            found: MTy::Bool
        }]
    );
}
