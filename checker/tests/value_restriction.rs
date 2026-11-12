//! A `=` binding generalizes only when its value is syntactic: a function, a
//! literal, a name, or a record or variant of those. A computed binding has
//! one type, and a conflicting later use says so.

use goat_checker::{GoatError, check_with_prelude};

fn errors_of(source: &str) -> Vec<GoatError> {
    match check_with_prelude("", source) {
        Ok(_) => panic!("should not check: {source}"),
        Err(errors) => errors,
    }
}

fn checks(source: &str) {
    if let Err(errors) = check_with_prelude("", source) {
        panic!("should check: {source}\n{errors:?}");
    }
}

#[test]
fn a_function_literal_generalizes() {
    checks("id = program(x) do x done\np = id(1)\nq = id(true)\nq");
}

#[test]
fn a_row_polymorphic_function_literal_generalizes() {
    checks("getx = program(r) do r.x done\np = getx({x: 1})\nq = getx({x: 1, y: 2})\nq");
}

#[test]
fn a_computed_binding_used_once_checks() {
    checks("mk = program(a) do program(b) do b done done\nm = mk(2)\np = m(1)\np");
}

#[test]
fn a_record_of_functions_generalizes() {
    checks("p = {f: program(x) do x done}\na = (p.f)(1)\nb = (p.f)(true)\nb");
}

#[test]
fn a_computed_binding_used_at_two_shapes_is_rejected_with_the_fix() {
    let source = "addX = program(x) do program(y) do x.x + y.y done done\n\
                  a = addX({x: 1})\n\
                  p = a({y: 1})\n\
                  q = a({y: 1, x: 2})\n\
                  q";
    let errors = errors_of(source);
    assert_eq!(errors.len(), 1, "{errors:?}");
    let message = &errors[0].message;
    assert!(message.contains("`a` is a computed value"), "{message}");
    assert!(message.contains("a = program("), "{message}");
    let last_call = source.rfind("a({y: 1, x: 2})").unwrap();
    assert_eq!(errors[0].span.start, last_call);
}

#[test]
fn a_computed_binding_used_at_two_types_is_rejected_with_the_fix() {
    let errors = errors_of(
        "mk = program(a) do program(b) do b done done\nm = mk(2)\np = m(1)\nq = m(true)\nq",
    );
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].message.contains("`m` is a computed value"));
}

#[test]
fn a_spread_of_values_generalizes() {
    checks(
        "b = {id: program(v) do v done, n: 1}\n\
         a = {...b, k: 5}\n\
         p = (a.id)(1)\n\
         q = (a.id)(true)\n\
         q",
    );
}

#[test]
fn a_spread_of_a_spread_generalizes() {
    checks(
        "b = {id: program(v) do v done, n: 1}\n\
         a = {...b, k: 5}\n\
         c = {...a, j: 6}\n\
         p = (c.id)(1)\n\
         q = (c.id)(true)\n\
         q",
    );
}

#[test]
fn a_spread_with_a_computed_field_keeps_one_type() {
    let errors = errors_of(
        "b = {id: program(v) do v done}\n\
         mk = program(n) do {n: n} done\n\
         a = {...b, k: mk(1).n}\n\
         p = (a.id)(1)\n\
         q = (a.id)(true)\n\
         q",
    );
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].message.contains("type mismatch"), "{errors:?}");
}

#[test]
fn a_spread_with_a_computed_base_keeps_one_type() {
    let errors = errors_of(
        "mk = program(n) do {id: program(v) do v done, n: n} done\n\
         a = {...mk(1), k: 5}\n\
         p = (a.id)(1)\n\
         q = (a.id)(true)\n\
         q",
    );
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].message.contains("type mismatch"), "{errors:?}");
}
