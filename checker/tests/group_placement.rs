//! Which functions of a block the checker infers as one group, which
//! `DK_group_hoist`, `DK_group_late` and `fn_run_names` in `proofs/GoatDen.v`
//! denote: functions glued by forward mentions are one group, typed together
//! (a member is used at one type inside the group); a backward mention counts
//! only into a group still open, so a member already generalized is used at
//! any type.

use goat_checker::check_with_prelude;

fn checks(source: &str) {
    if let Err(errors) = check_with_prelude("", source) {
        panic!("should check: {source}\n{errors:?}");
    }
}

fn rejected(source: &str) {
    assert!(
        check_with_prelude("", source).is_err(),
        "should not check: {source}"
    );
}

#[test]
fn a_function_named_ahead_of_its_declaration_joins_the_group() {
    rejected(
        "f = program(x) do {a: g(1), b: g(\"s\")} done\n\
         g = program(y) do y done\n\
         f(0)",
    );
}

#[test]
fn a_function_declared_first_is_used_at_two_types() {
    checks(
        "g = program(y) do y done\n\
         f = program(x) do {a: g(1), b: g(\"s\")} done\n\
         f(0)",
    );
}

#[test]
fn a_backward_mention_does_not_glue_a_closed_group() {
    checks(
        "g = program(y) do y done\n\
         f = program(x) do g(x) done\n\
         {a: f(1), b: f(\"s\"), c: g(true)}",
    );
}

#[test]
fn a_linked_pair_is_typed_together_and_generalized_after() {
    checks(
        "f = program(x) do g(x) done\n\
         g = program(y) do if true then y else f(y) done done\n\
         {a: f(1), b: f(\"s\")}",
    );
}

#[test]
fn a_pair_after_a_value_one_of_them_uses_is_one_group() {
    checks(
        "limit = 4\n\
         is_even = program(n) do if n < limit then true else is_odd(n - 1) done done\n\
         is_odd = program(n) do if n < 1 then false else is_even(n - 1) done done\n\
         is_even(limit)",
    );
}

#[test]
fn an_unlinked_member_between_two_linked_ones_is_still_typed_apart() {
    checks(
        "a = program(x) do c(x) done\n\
         b = program(y) do y done\n\
         c = program(z) do z done\n\
         {p: b(1), q: b(\"s\"), r: a(true)}",
    );
}
