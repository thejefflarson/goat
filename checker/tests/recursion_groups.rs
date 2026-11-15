//! Recursion in the checker: every `program(...)` binding in a `let` chain is
//! one order-free, mutually recursive group at any block depth (ADR 0003). The
//! proofs model that as an n-ary `letrec` of functions (`proofs/GoatDefs.v`,
//! `T_Letrec`), and the group's functions are generalized once the group is
//! typed.

use goat_checker::{GoatError, check_with_prelude};

fn checks(source: &str) {
    if let Err(errors) = check_with_prelude("", source) {
        panic!("should check: {source}\n{errors:?}");
    }
}

fn errors_of(source: &str) -> Vec<GoatError> {
    match check_with_prelude("", source) {
        Ok(_) => panic!("should not check: {source}"),
        Err(errors) => errors,
    }
}

#[test]
fn a_function_calls_itself() {
    checks("fact = program(n) do if n < 2 then 1 else n * fact(n - 1) done done\nfact(5)");
}

#[test]
fn two_functions_call_each_other_in_either_order() {
    checks(
        "is_even = program(n) do if n == 0 then true else is_odd(n - 1) done done\n\
         is_odd = program(n) do if n == 0 then false else is_even(n - 1) done done\n\
         is_even(4)",
    );
    checks(
        "go = program(n) do half(n) done\n\
         half = program(n) do if n < 1 then 0 else go(n - 2) done done\n\
         go(9)",
    );
}

#[test]
fn a_group_inside_a_function_body_recurses() {
    checks(
        "outer = program(k) do\n\
           down = program(n) do if n < 1 then k else up(n - 1) done done\n\
           up = program(n) do if n < 1 then k else down(n - 1) done done\n\
           down(k)\n\
         done\n\
         outer(3)",
    );
}

#[test]
fn a_recursive_function_is_generalized_after_its_group() {
    checks(
        "count = program(x, n) do if n < 1 then x else count(x, n - 1) done done\n\
         a = count(1, 3)\n\
         b = count(true, 3)\n\
         b",
    );
}

#[test]
fn a_recursive_call_at_another_type_is_rejected() {
    // Within its own group a function has one type, so recursion is monomorphic.
    let errors = errors_of("f = program(x) do if true then 1 else f(true) done done\nf(1)");
    assert!(!errors.is_empty());
}

#[test]
fn a_value_binding_cannot_name_itself() {
    // Only a `program(...)` literal is recursive; `x = x + 1` reads an earlier `x`.
    let errors = errors_of("x = x + 1\nx");
    assert!(!errors.is_empty());
}

#[test]
fn a_group_is_generalized_after_all_its_members() {
    // `f` shares its type variable with `g`, which is typed after it, so both
    // wait for the whole group: the plain Hindley-Milner binding-group rule.
    checks(
        "f = program(x) do g(x) done\n\
         g = program(y) do y done\n\
         a = f(1)\n\
         b = f(true)\n\
         b",
    );
    checks(
        "g = program(y) do y done\n\
         f = program(x) do g(x) done\n\
         a = f(1)\n\
         b = f(true)\n\
         b",
    );
}

#[test]
fn a_mutual_group_is_generalized_after_all_its_members() {
    checks(
        "ping = program(x, n) do if n < 1 then x else pong(x, n - 1) done done\n\
         pong = program(x, n) do if n < 1 then x else ping(x, n - 1) done done\n\
         a = ping(1, 3)\n\
         b = pong(true, 3)\n\
         b",
    );
}

#[test]
fn a_group_inside_a_function_body_is_generalized_after_all_its_members() {
    checks(
        "outer = program(k) do\n\
           f = program(x) do g(x) done\n\
           g = program(y) do y done\n\
           a = f(1)\n\
           f(k)\n\
         done\n\
         outer(true)",
    );
}

#[test]
fn a_member_still_has_one_type_inside_its_group() {
    // `g` is used at two types in `f`, which is inside `g`'s group.
    let errors = errors_of(
        "f = program(x) do {a: g(1), b: g(true)} done\n\
         g = program(y) do y done\n\
         f(1)",
    );
    assert!(!errors.is_empty());
}

#[test]
fn a_function_that_names_no_later_function_is_generalized_when_reached() {
    checks(
        "id = program(x) do x done\n\
         a = id(1)\n\
         twice = program(y) do id(id(y)) done\n\
         b = id(true)\n\
         c = twice(1)\n\
         twice(false)",
    );
}
