//! `Write`, `StrEq`, `StrLen` and `StrByte`: how the verifier checks them and what the interpreter
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

/// `StrByte` at the 1-based `position` of the string `text`, string dropped.
fn byte_at(text: &str, position: i64) -> Program {
    let body = let_(
        0,
        Expr::StrLit(DataId(0)),
        let_(
            1,
            int(position),
            let_(
                2,
                Expr::StrByte(Local(0), Local(1)),
                let_(3, Expr::Drop(Local(0)), local(2)),
            ),
        ),
    );
    string_program(&[text], body, MTy::Int)
}

#[test]
fn str_len_counts_bytes() {
    for (text, bytes) in [("", 0), ("ab", 2), ("é", 2), ("🐐", 4)] {
        let body = let_(
            0,
            Expr::StrLit(DataId(0)),
            let_(
                1,
                Expr::StrLen(Local(0)),
                let_(2, Expr::Drop(Local(0)), local(1)),
            ),
        );
        let out = run_verified(&string_program(&[text], body, MTy::Int));
        assert_eq!(out.value, Value::Int(bytes), "{text}");
    }
}

#[test]
fn str_byte_counts_from_one() {
    for (position, byte) in [(1, 195), (2, 169), (3, 97)] {
        let out = run_verified(&byte_at("éa", position));
        assert_eq!(out.value, Value::Int(byte), "position {position}");
    }
}

#[test]
fn str_byte_outside_the_string_traps() {
    for position in [0, 4, -1, i64::MIN, i64::MAX] {
        let p = byte_at("éa", position);
        assert_eq!(verify(&p), Ok(()));
        assert_eq!(
            run(&p),
            Err(InterpError::Trap(BYTE_OUT_OF_RANGE.into())),
            "position {position}"
        );
    }
    assert_eq!(
        run(&byte_at("", 1)),
        Err(InterpError::Trap(BYTE_OUT_OF_RANGE.into()))
    );
}

#[test]
fn the_string_functions_want_a_string_and_an_int_position() {
    let not_a_string = |read: Expr| {
        let_(
            0,
            alloc_record(1),
            let_(
                1,
                int(1),
                let_(2, read, let_(3, Expr::Drop(Local(0)), local(2))),
            ),
        )
    };
    let record = ErrorKind::NotAString(MTy::Ptr(HeapKind::Record(RECORD)));
    for read in [Expr::StrLen(Local(0)), Expr::StrByte(Local(0), Local(1))] {
        let found = kinds(&string_program(&[], not_a_string(read), MTy::Int));
        assert!(found.contains(&record), "{found:?}");
    }
    let float_position = let_(
        0,
        Expr::StrLit(DataId(0)),
        let_(
            1,
            float(1.0),
            let_(
                2,
                Expr::StrByte(Local(0), Local(1)),
                let_(3, Expr::Drop(Local(0)), local(2)),
            ),
        ),
    );
    assert_eq!(
        kinds(&string_program(&["a"], float_position, MTy::Int)),
        [ErrorKind::TypeMismatch {
            expected: MTy::Int,
            found: MTy::Float
        }]
    );
}

/// `StrChar` at the 1-based `position` of `text`, giving the new string's byte
/// length; both strings dropped.
fn char_at_length(text: &str, position: i64) -> Program {
    let body = let_(
        0,
        Expr::StrLit(DataId(0)),
        let_(
            1,
            int(position),
            let_(
                2,
                Expr::StrChar(Local(0), Local(1)),
                let_(
                    3,
                    Expr::StrLen(Local(2)),
                    let_(
                        4,
                        Expr::Drop(Local(2)),
                        let_(5, Expr::Drop(Local(0)), local(3)),
                    ),
                ),
            ),
        ),
    );
    string_program(&[text], body, MTy::Int)
}

#[test]
fn str_chars_counts_code_points() {
    for (text, count) in [("", 0), ("ab", 2), ("é", 1), ("日本", 2), ("👍🏽", 2)] {
        let body = let_(
            0,
            Expr::StrLit(DataId(0)),
            let_(
                1,
                Expr::StrChars(Local(0)),
                let_(2, Expr::Drop(Local(0)), local(1)),
            ),
        );
        let out = run_verified(&string_program(&[text], body, MTy::Int));
        assert_eq!(out.value, Value::Int(count), "{text}");
    }
}

#[test]
fn str_char_copies_one_code_point_into_a_counted_string() {
    for (position, bytes) in [(1, 1), (2, 2), (3, 3), (4, 4), (5, 1)] {
        let out = run_verified(&char_at_length("aé日🐐b", position));
        assert_eq!(out.value, Value::Int(bytes), "position {position}");
        assert_eq!(out.live_allocations, 0, "position {position}");
    }
}

#[test]
fn str_char_outside_the_string_traps() {
    for position in [0, 6, -1, i64::MIN, i64::MAX] {
        let p = char_at_length("aé日🐐b", position);
        assert_eq!(verify(&p), Ok(()));
        assert_eq!(
            run(&p),
            Err(InterpError::Trap(BYTE_OUT_OF_RANGE.into())),
            "position {position}"
        );
    }
    assert_eq!(
        run(&char_at_length("", 1)),
        Err(InterpError::Trap(BYTE_OUT_OF_RANGE.into()))
    );
}

#[test]
fn the_character_nodes_want_a_string_and_an_int_position() {
    let float_position = let_(
        0,
        Expr::StrLit(DataId(0)),
        let_(
            1,
            float(1.0),
            let_(
                2,
                Expr::StrChar(Local(0), Local(1)),
                let_(
                    3,
                    Expr::Drop(Local(2)),
                    let_(4, Expr::Drop(Local(0)), int(0)),
                ),
            ),
        ),
    );
    assert_eq!(
        kinds(&string_program(&["a"], float_position, MTy::Int)),
        [ErrorKind::TypeMismatch {
            expected: MTy::Int,
            found: MTy::Float
        }]
    );
    let not_a_string = let_(
        0,
        alloc_record(1),
        let_(
            1,
            Expr::StrChars(Local(0)),
            let_(2, Expr::Drop(Local(0)), local(1)),
        ),
    );
    assert!(
        kinds(&string_program(&[], not_a_string, MTy::Int))
            .contains(&ErrorKind::NotAString(MTy::Ptr(HeapKind::Record(RECORD))))
    );
}
