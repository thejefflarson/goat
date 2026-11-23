//! A sort (`==`) reaching a row reads through a presence entry that is already
//! settled: a field known absent is no field, so it is never compared. An entry
//! whose presence is still open takes the sort on its field, since it may turn
//! out present (ADR 0033, `rsat` in `proofs/GoatDefs.v`). The two orders of one
//! program can therefore differ: a sort that arrives first sees the open entry.

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
    let source = format!("{FN_FIELD} b = {{k: 1}} == r\n a = r == r\n 1 done\n1");
    assert!(checks(&source));
}

#[test]
fn a_sort_before_the_presence_settles_sees_the_open_entry() {
    let source = format!("{FN_FIELD} a = r == r\n b = r == {{k: 1}}\n 1 done\n1");
    let message = first_error(&source);
    assert!(message.contains("it has a function inside"), "{message}");
}

#[test]
fn a_present_function_field_is_rejected_in_either_order() {
    let source = format!("{FN_FIELD} a = s == s\n b = r == {{k: 1}}\n 1 done\n1");
    assert!(!checks(&source));
    let source = format!("{FN_FIELD} b = r == {{k: 1}}\n a = s == s\n 1 done\n1");
    assert!(!checks(&source));
}

#[test]
fn a_field_that_turns_out_absent_leaves_its_type_free_when_settled_first() {
    let call = "f({k: 1}, program(v) do v done)";
    let settled_first = format!(
        "f = program(r, x) do s = {{...r, id: x}}\n b = r == {{k: 1}}\n a = r == r\n 1 done\n{call}"
    );
    assert!(checks(&settled_first));
}

#[test]
fn a_field_that_turns_out_absent_keeps_the_sort_it_took_before() {
    let call = "f({k: 1}, program(v) do v done)";
    let sorted_first = format!(
        "f = program(r, x) do s = {{...r, id: x}}\n a = r == r\n b = r == {{k: 1}}\n 1 done\n{call}"
    );
    assert_eq!(first_error(&sorted_first), "can't compare functions");
}
