//! A program whose last expression is a heap value computed from nested
//! `let`-bound calls (a record or list of generic calls) runs: the entry
//! drops that value after computing it, and the locals it binds there must
//! not collide with the ones the body already uses. Each program runs through
//! the interpreter and wasm, which must agree and leak nothing.

#[allow(dead_code)]
mod support;

use support::run;

#[test]
fn a_final_record_calls_one_generic_at_two_types() {
    assert_eq!(run("{a: length([1]), b: length([\"a\"])}"), "");
    assert_eq!(run("print({a: length([1]), b: length([\"a\"])}.b)"), "1");
}

#[test]
fn a_final_record_of_other_prelude_generics() {
    assert_eq!(run("{a: first([1]), b: first([\"a\"])}"), "");
    assert_eq!(run("{a: reverse([1, 2]), b: reverse([\"a\"])}"), "");
    let each = "{a: change_each([1], program(x) do x + 1 done), \
                 b: change_each([\"a\"], program(s) do s done)}";
    assert_eq!(run(each), "");
}

#[test]
fn a_final_nested_record_calls_generics() {
    let nested = "{a: {b: length([1]), c: length([\"a\"])}, d: reverse([1, 2])}";
    assert_eq!(run(nested), "");
}

#[test]
fn a_final_list_calls_generics() {
    assert_eq!(run("[length([1]), length([\"a\"])]"), "");
    assert_eq!(run("reverse([1, 2, 3])"), "");
}
