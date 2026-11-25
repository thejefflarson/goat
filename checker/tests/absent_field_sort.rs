//! A sort (`==`) reaching a record reads each field by its presence. A field
//! known absent is no field, so it is never compared. A field whose presence is
//! still open and whose type can never meet the sort (a function) can only be
//! absent, so the sort decides it so: the verdict does not depend on whether the
//! presence settles before or after the comparison (ADR 0033, `forced` in
//! `proofs/GoatInfer.v`). A field whose type is a variable keeps the sort on the
//! entry's own field, held against the spread's value until the presence settles.

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

const FN_FIELD: &str = "f = program(r) do s = {...r, id: program(v) do v done}\n";

#[test]
fn an_absent_function_field_is_not_compared() {
    let source = format!("{FN_FIELD} b = r == {{k: 1}}\n a = r == r\n 1 done\n1");
    assert!(checks(&source));
    let source = format!("{FN_FIELD} a = r == r\n b = r == {{k: 1}}\n 1 done\n1");
    assert!(checks(&source));
}

#[test]
fn a_sort_before_the_presence_settles_decides_a_function_field_absent() {
    let alone = format!("{FN_FIELD} a = r == r\n 1 done\nf({{k: 1}})");
    assert!(checks(&alone));
    let twice =
        format!("{FN_FIELD} a = r == r\n s2 = {{...r, id: program(w) do w done}}\n 1 done\n1");
    assert!(checks(&twice));
    let reversed =
        format!("{FN_FIELD} s2 = {{...r, id: program(w) do w done}}\n a = r == r\n 1 done\n1");
    assert!(checks(&reversed));
}

#[test]
fn a_present_function_field_is_rejected_in_either_order() {
    let source = format!("{FN_FIELD} a = s == s\n b = r == {{k: 1}}\n 1 done\n1");
    assert!(!checks(&source));
    let source = format!("{FN_FIELD} b = r == {{k: 1}}\n a = s == s\n 1 done\n1");
    assert!(!checks(&source));
}

#[test]
fn a_function_field_a_later_use_needs_is_refused_with_the_comparison_error() {
    let compared_first = format!("{FN_FIELD} a = r == r\n t = r.id\n 1 done\n1");
    let read_first = format!("{FN_FIELD} t = r.id\n a = r == r\n 1 done\n1");
    for source in [compared_first, read_first] {
        let message = first_error(&source);
        assert!(message.contains("it has a function inside"), "{message}");
    }
    let call = format!("{FN_FIELD} a = r == r\n 1 done\nf({{id: program(v) do v done}})");
    assert!(first_error(&call).contains("it has a function inside"));
}

#[test]
fn a_field_that_turns_out_absent_leaves_its_type_free_when_settled_first() {
    let call = "f({k: 1}, program(v) do v done)";
    let settled_first = format!(
        "f = program(r, x) do s = {{...r, id: x}}\n b = r == {{k: 1}}\n a = r == r\n 1 done\n{call}"
    );
    assert!(checks(&settled_first));
}

/// `{...r, id: x}` gives `r`'s entry its own field type, held against `x` until
/// the presence settles, so the sort a comparison puts on the field reaches `x`
/// only when `r` turns out to have `id` (ADR 0033).
#[test]
fn a_variable_field_takes_the_sort_in_either_order() {
    let call = "f({k: 1}, program(v) do v done)";
    for (first, second) in [("r == r", "r == {k: 1}"), ("r == {k: 1}", "r == r")] {
        let source = format!(
            "f = program(r, x) do s = {{...r, id: x}}\n a = {first}\n b = {second}\n 1 done\n{call}"
        );
        assert!(checks(&source), "{source}");
    }
}

#[test]
fn a_variable_field_that_stays_present_takes_the_sort_in_either_order() {
    let call = "f({id: program(v) do v done, k: 1}, program(v) do v done)";
    for (first, second) in [("r == r", "r.id"), ("r.id", "r == r")] {
        let source = format!(
            "f = program(r, x) do s = {{...r, id: x}}\n a = {first}\n b = {second}\n 1 done\n{call}"
        );
        assert!(!checks(&source), "{source}");
    }
}

/// A function that spreads onto a parameter of its caller's keeps the equation
/// in its scheme, so each call adds its own and the verdict does not depend on
/// which call comes first.
#[test]
fn a_nested_function_carries_the_equation_in_either_order() {
    let body = |first: &str, second: &str| {
        format!(
            "f = program(r) do\n g = program(x) do {{...r, id: x}} done\n {first}\n {second}\n b = r == {{k: 1}}\n 1 done\nf({{k: 1}})"
        )
    };
    let numeral = "u = g(1)";
    let text = "w = g(\"s\")";
    assert!(checks(&body(numeral, text)));
    assert!(checks(&body(text, numeral)));
}

#[test]
fn a_nested_function_whose_field_stays_present_refuses_two_types_in_either_order() {
    let body = |first: &str, second: &str| {
        format!(
            "f = program(r) do\n g = program(x) do {{...r, id: x}} done\n {first}\n {second}\n b = r.id\n 1 done\nf({{id: 1}})"
        )
    };
    let numeral = "u = g(1)";
    let text = "w = g(\"s\")";
    assert!(!checks(&body(numeral, text)));
    assert!(!checks(&body(text, numeral)));
}

/// The scheme of `h` re-holds its equation at each use: the field of the
/// argument is its own variable, so the sorts `k` puts on it meet `z` only when
/// the presence settles.
#[test]
fn an_instantiated_scheme_holds_its_equation_in_either_order() {
    let k = |first: &str, second: &str| {
        format!(
            "h = program(r, x) do {{...r, id: x}} done\nk = program(a, z) do\n h(a, z);\n {first};\n {second};\n 1 done\nk({{k: 1}}, program(v) do v done)"
        )
    };
    assert!(checks(&k("a == a", "a == {k: 1}")));
    assert!(checks(&k("a == {k: 1}", "a == a")));
}
