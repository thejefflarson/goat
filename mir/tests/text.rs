//! `Write` and `StrEq`: how the verifier checks them and what the interpreter
//! does with them.

mod common;

use common::*;
use goat_mir::*;

fn string_program(data: &[&str], body: Expr, ret: MTy) -> Program {
    let mut p = program(vec![func(ret, body)]);
    p.data = data.iter().map(|s| s.as_bytes().to_vec()).collect();
    p
}

fn kinds(p: &Program) -> Vec<ErrorKind> {
    verify(p)
        .expect_err("expected verification to fail")
        .into_iter()
        .map(|e| e.kind)
        .collect()
}

fn run_verified(p: &Program) -> Outcome {
    assert_eq!(verify(p), Ok(()));
    run(p).expect("program runs")
}

fn write(w: Write) -> Expr {
    Expr::Write(w)
}

/// `first`, then `rest`, binding the first's `Unit` to a local no one reads.
fn then(first: Expr, rest: Expr) -> Expr {
    thread_local!(static NEXT: std::cell::Cell<u32> = const { std::cell::Cell::new(100) });
    let local = NEXT.with(|next| next.replace(next.get() + 1));
    let_(local, first, rest)
}

fn unit() -> Expr {
    Expr::Const(Const::Unit)
}

#[test]
fn write_collects_pieces_into_lines() {
    let body = then(
        write(Write::Lit(DataId(0))),
        then(
            write(Write::Number(Box::new(float(2.5)))),
            then(
                write(Write::End),
                then(write(Write::Lit(DataId(0))), write(Write::End)),
            ),
        ),
    );
    let out = run_verified(&string_program(&["n = "], body, MTy::Unit));
    assert_eq!(
        out.printed,
        vec![
            vec![Piece::Text(b"n = ".to_vec()), Piece::Number(2.5)],
            vec![Piece::Text(b"n = ".to_vec())],
        ]
    );
    assert_eq!(out.live_allocations, 0);
}

#[test]
fn write_str_borrows_its_string() {
    let leaks = let_(
        0,
        Expr::StrLit(DataId(0)),
        then(write(Write::Str(Local(0))), write(Write::End)),
    );
    assert_eq!(
        kinds(&string_program(&["hi"], leaks, MTy::Unit)),
        [ErrorKind::Leak(Local(0))]
    );
    let balanced = let_(
        0,
        Expr::StrLit(DataId(0)),
        then(
            write(Write::Str(Local(0))),
            then(write(Write::End), let_(1, Expr::Drop(Local(0)), unit())),
        ),
    );
    let out = run_verified(&string_program(&["hi"], balanced, MTy::Unit));
    assert_eq!(out.printed, vec![vec![Piece::Text(b"hi".to_vec())]]);
}

#[test]
fn str_eq_compares_bytes_not_addresses() {
    for (a, b, same) in [
        ("ab", "ab", true),
        ("ab", "ac", false),
        ("ab", "abc", false),
    ] {
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
        let out = run_verified(&string_program(&[a, b], body, MTy::Bool));
        assert_eq!(out.value, Value::Bool(same), "{a} == {b}");
    }
}

#[test]
fn write_of_missing_data_is_malformed() {
    let p = string_program(&[], write(Write::Lit(DataId(3))), MTy::Unit);
    assert_eq!(run(&p), Err(InterpError::Malformed("unknown data")));
}

#[test]
fn the_verifier_wants_a_float_a_string_and_known_data() {
    let bad_number = write(Write::Number(Box::new(boolean(true))));
    assert_eq!(
        kinds(&string_program(&[], bad_number, MTy::Unit)),
        [ErrorKind::TypeMismatch {
            expected: MTy::Float,
            found: MTy::Bool
        }]
    );
    assert_eq!(
        kinds(&string_program(
            &[],
            write(Write::Lit(DataId(5))),
            MTy::Unit
        )),
        [ErrorKind::UnknownData(DataId(5))]
    );
    let not_a_string = let_(
        0,
        alloc_record(1),
        then(
            write(Write::Str(Local(0))),
            then(Expr::Drop(Local(0)), unit()),
        ),
    );
    assert_eq!(
        kinds(&string_program(&[], not_a_string, MTy::Unit)),
        [ErrorKind::NotAString(MTy::Ptr(HeapKind::Record(RECORD)))]
    );
}

#[test]
fn str_eq_wants_strings() {
    let bad = let_(
        0,
        alloc_record(1),
        let_(
            1,
            Expr::StrEq(Local(0), Local(0)),
            let_(2, Expr::Drop(Local(0)), local(1)),
        ),
    );
    assert!(
        kinds(&string_program(&[], bad, MTy::Bool))
            .contains(&ErrorKind::NotAString(MTy::Ptr(HeapKind::Record(RECORD))))
    );
}
