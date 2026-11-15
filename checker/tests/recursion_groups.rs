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
