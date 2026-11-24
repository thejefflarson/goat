//! A sort (`==`) reaching a record reads each field by its presence. A field
//! known absent is no field, so it is never compared. A field whose presence is
//! still open and whose type can never meet the sort (a function) can only be
//! absent, so the sort decides it so: the verdict does not depend on whether the
//! presence settles before or after the comparison (ADR 0033, `forced` in
//! `proofs/GoatInfer.v`). A field whose type is a variable takes the sort as the
//! variable's own, which is the one case the order of two comparisons still changes.

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

/// Deciding two open entries absent when their field types clash does not reach
/// this program: `{...r, id: x}` gives `r`'s entry `x`'s own type, so the sort
/// lands on `x` and no second entry is unified (ADR 0033).
#[test]
fn a_variable_field_keeps_the_sort_it_took_before() {
    let call = "f({k: 1}, program(v) do v done)";
    let sorted_first = format!(
        "f = program(r, x) do s = {{...r, id: x}}\n a = r == r\n b = r == {{k: 1}}\n 1 done\n{call}"
    );
    assert_eq!(first_error(&sorted_first), "can't compare functions");
}
