//! Two records that both may have a field `a`, whose presence nothing has
//! settled yet, meet in one type. If the field types can never be the same (an
//! `Int` against a `String`), the field can only be absent in both, so the
//! verdict does not depend on whether a later statement settles the presence
//! first (ADR 0033). Field types that could still be the same are unified as
//! before.

use goat_checker::check_with_prelude;

fn checks(source: &str) -> bool {
    check_with_prelude("", source).is_ok()
}

fn first_error(source: &str) -> String {
    match check_with_prelude("", source) {
        Ok(_) => panic!("should not check: {source}"),
        Err(errors) => errors[0].message.clone(),
    }
}

const SPREADS: &str = "x = {...p, a: 1}\n y = {...q, a: \"x\"}\n";
const SPREADS_SWAPPED: &str = "y = {...q, a: \"x\"}\n x = {...p, a: 1}\n";

fn program(body: &str) -> String {
    format!("f = program(p, q) do {body} done\n1")
}

#[test]
fn two_open_fields_of_clashing_types_are_absent() {
    let joined = program(&format!("{SPREADS} if true then p else q done"));
    assert!(checks(&joined));
}

#[test]
fn the_statement_order_of_the_spreads_does_not_matter() {
    let joined = program(&format!("{SPREADS_SWAPPED} if true then p else q done"));
    assert!(checks(&joined));
    let reversed = program(&format!("{SPREADS} if true then q else p done"));
    assert!(checks(&reversed));
}

#[test]
fn a_presence_settled_before_or_after_gives_the_same_verdict() {
    let settled_first = program(&format!(
        "b = p == {{k: 1}}\n {SPREADS} if true then p else q done"
    ));
    let settled_after = program(&format!(
        "{SPREADS} if true then p else q done;\n b = p == {{k: 1}}"
    ));
    assert!(checks(&settled_first));
    assert!(checks(&settled_after));
}

#[test]
fn a_field_a_later_use_needs_is_refused_in_either_order() {
    let used_after = program(&format!(
        "{SPREADS} if true then p else q done;\n t = p.a\n t"
    ));
    let used_before = program(&format!("{SPREADS} t = p.a\n if true then p else q done"));
    let message = first_error(&used_after);
    assert!(message.contains("neither can have it"), "{message}");
    assert!(!checks(&used_after));
    assert!(!checks(&used_before));
}

#[test]
fn a_present_field_still_meets_the_other_side_at_its_type() {
    let message = first_error(&program(&format!(
        "{SPREADS} t = q.a\n if true then p else q done"
    )));
    assert!(
        message.contains("String") || message.contains("mismatch"),
        "{message}"
    );
}

#[test]
fn field_types_that_could_be_equal_are_unified() {
    let source = "f = program(p, q, u, v) do x = {...p, a: u}\n y = {...q, a: v}\n if true then p else q done done\n1";
    assert!(checks(source));
}

#[test]
fn a_field_with_a_function_type_against_a_string_is_absent() {
    let source = program(
        "x = {...p, a: program(v) do v done}\n y = {...q, a: \"s\"}\n if true then p else q done",
    );
    assert!(checks(&source));
}

#[test]
fn equal_field_types_keep_the_field() {
    let source =
        program("x = {...p, a: 1}\n y = {...q, a: 2}\n r = if true then p else q done\n r.a");
    assert!(checks(&source));
}

/// Two variable field types are not unified when the entries meet: each entry
/// keeps its own field, held until the presence settles, so the verdict is the
/// same whether a later statement settles the presence first (ADR 0033).
#[test]
fn variable_fields_are_joined_only_when_the_presence_settles() {
    let tail = "z = u + 1\n w = v == \"s\"\n 1";
    let spreads = "x = {...p, a: u}\n y = {...q, a: v}\n";
    let joined_first = format!(
        "f = program(p, q, u, v) do {spreads} if true then p else q done;\n {tail} done\n1"
    );
    let settled_first = format!(
        "f = program(p, q, u, v) do b = p == {{k: 1}}\n {spreads} if true then p else q done;\n {tail} done\n1"
    );
    assert!(checks(&joined_first));
    assert!(checks(&settled_first));
}

/// A field that a later read makes present is joined for real: `u` is a number
/// and `v` a string, in either order.
#[test]
fn variable_fields_of_a_present_field_are_refused_in_either_order() {
    let tail = "z = u + 1\n w = v == \"s\"\n 1";
    let spreads = "x = {...p, a: u}\n y = {...q, a: v}\n";
    let read_first = format!(
        "f = program(p, q, u, v) do t = p.a\n {spreads} if true then p else q done;\n {tail} done\n1"
    );
    let read_last = format!(
        "f = program(p, q, u, v) do {spreads} if true then p else q done;\n {tail}\n t = p.a\n t done\n1"
    );
    assert!(!checks(&read_first));
    assert!(!checks(&read_last));
}

/// A function field against a numeral's type is decided the same way: a
/// function is not a number, so the entries can only be absent.
#[test]
fn a_function_field_against_a_numeral_is_absent() {
    let source = program(
        "x = {...p, a: program(v) do v done}\n y = {...q, a: 1}\n if true then p else q done",
    );
    assert!(checks(&source));
    let swapped = program(
        "y = {...q, a: 1}\n x = {...p, a: program(v) do v done}\n if true then p else q done",
    );
    assert!(checks(&swapped));
}

/// Two types no head tells apart, so nothing decides the field absent: the
/// equations are unified together and cannot hold. The verdict is the same in
/// either spread order and with the field read first or last.
#[test]
fn jointly_conflicting_fields_are_refused_in_every_order() {
    let a = "x = {...p, a: {n: 1, s: \"a\"}}\n";
    let b = "y = {...q, a: {n: \"b\", s: 2}}\n";
    for spreads in [format!("{a} {b}"), format!("{b} {a}")] {
        let plain = program(&format!("{spreads} if true then p else q done"));
        let read_first = program(&format!("t = p.a\n {spreads} if true then p else q done"));
        let read_last = program(&format!(
            "{spreads} r = if true then p else q done\n t = p.a\n t"
        ));
        assert!(!checks(&plain), "{plain}");
        assert!(!checks(&read_first), "{read_first}");
        assert!(!checks(&read_last), "{read_last}");
    }
}
