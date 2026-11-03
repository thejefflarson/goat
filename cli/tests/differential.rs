//! Differential tests: every program runs through the MIR interpreter (the
//! oracle) and through the compiled wasm under wasmtime, and both must print
//! the same thing. The interpreter must also leave no heap object live.

use std::fs;

#[allow(dead_code)]
mod support;

use support::run;

#[test]
fn arithmetic() {
    assert_eq!(run("1 + 2 * 3"), "7");
    assert_eq!(run("(1 + 2) * 3"), "9");
    assert_eq!(run("10 / 4"), "2.5");
}

#[test]
fn numbers_print_without_exponent() {
    assert_eq!(run("1000000"), "1000000");
    assert_eq!(run("123456789"), "123456789");
    assert_eq!(run("0.5"), "0.5");
    assert_eq!(run("0.1 + 0.2"), "0.3");
}

#[test]
fn booleans() {
    assert_eq!(run("1 < 2"), "true");
    assert_eq!(run("3 < 2"), "false");
    assert_eq!(run("x = 5  x < 10"), "true");
}

#[test]
fn let_bindings() {
    assert_eq!(run("a = 2  b = 3  a + b"), "5");
}

#[test]
fn functions_and_recursion() {
    assert_eq!(run("add = program(a, b) do a + b done  add(20, 22)"), "42");
    let fib = "fib = program(n) do if n < 2 then n else fib(n - 1) + fib(n - 2) done done fib(10)";
    assert_eq!(run(fib), "55");
}

#[test]
fn higher_order_functions() {
    let src = "apply = program(f, x) do f(x) done \
               double = program(n) do n * 2 done \
               apply(double, 21)";
    assert_eq!(run(src), "42");
}

#[test]
fn identifier_may_start_with_a_keyword() {
    assert_eq!(run("double = program(n) do n * 2 done  double(21)"), "42");
}

#[test]
fn mutual_recursion_either_order() {
    let even_first = "is_even = program(n) do if n < 1 then true else is_odd(n - 1) done done \
                      is_odd = program(n) do if n < 1 then false else is_even(n - 1) done done \
                      is_even(10)";
    let odd_first = "is_odd = program(n) do if n < 1 then false else is_even(n - 1) done done \
                     is_even = program(n) do if n < 1 then true else is_odd(n - 1) done done \
                     is_even(7)";
    assert_eq!(run(even_first), "true");
    assert_eq!(run(odd_first), "false");
}

#[test]
fn shadowing_value_binding() {
    assert_eq!(run("score = 1  score = score + 1  score"), "2");
}

#[test]
fn long_operator_chain() {
    assert_eq!(run(&vec!["1"; 200].join(" + ")), "200");
}

#[test]
fn deep_tail_recursion_runs_in_constant_stack() {
    let src = "sum = program(n, acc) do if n < 1 then acc else sum(n - 1, acc + n) done done \
               sum(1000000, 0)";
    assert_eq!(run(src), "500000500000");
}

#[test]
fn records() {
    assert_eq!(run("p = {x: 1, y: 2}  p.x + p.y"), "3");
    let nested = "line = {from: {x: 1, y: 2}, to: {x: 3, y: 4}}  line.to.x + line.from.y";
    assert_eq!(run(nested), "5");
    let getx = "getx = program(p) do p.x done  \
                getx({x: 1, y: 2}) + getx({a: 0, x: 9, z: true})";
    assert_eq!(run(getx), "10");
    assert_eq!(run("p = {x: 1}"), "");
}

#[test]
fn multi_field_record() {
    assert_eq!(run("p = {a: 1, b: 2, c: 3}  p.a + p.b * p.c"), "7");
}

#[test]
fn deeply_nested_record() {
    let src = "line = {from: {x: 1, y: 2}, to: {x: 10, y: 20}} \
               line.to.x - line.from.x + line.to.y - line.from.y";
    assert_eq!(run(src), "27");
}

#[test]
fn row_polymorphic_field_access() {
    let src = "sum = program(p) do p.x + p.y done \
               sum({x: 1, y: 2}) + sum({x: 3, y: 4, z: 5, w: 6})";
    assert_eq!(run(src), "10");
}

#[test]
fn curried_capture() {
    assert_eq!(
        run("add = program(a) do program(b) do a + b done done  add(1)(2)"),
        "3"
    );
}

#[test]
fn recursive_closure_capturing_an_outer_parameter() {
    let src = "outer = program(n) do \
                 go = program(k) do if k < 1 then 0 else n + go(k - 1) done done \
                 go(3) \
               done \
               outer(10)";
    assert_eq!(run(src), "30");
}

#[test]
fn capturing_closures_through_a_polymorphic_apply() {
    let src = "apply = program(f, x) do f(x) done \
               n = 10 \
               t = true \
               addn = program(x) do x + n done \
               pick = program(b) do if t then b else false done done \
               if apply(pick, true) then apply(addn, 1) else 0 done";
    assert_eq!(run(src), "11");
}

#[test]
fn record_of_capturing_functions() {
    let src = "k = 10 \
               r = {f: program(x) do x + k done, g: program(x) do x * k done} \
               r.f(3) + r.g(2)";
    assert_eq!(run(src), "33");
}

#[test]
fn closures_capture_closures_and_records() {
    let twice = "double = program(n) do n * 2 done \
                 twice = program(f) do program(x) do f(f(x)) done done \
                 twice(double)(5)";
    assert_eq!(run(twice), "20");
    let record = "p = {x: 1, y: 2}  f = program(z) do p.x + p.y + z done  f(3) + f(4)";
    assert_eq!(run(record), "13");
}

#[test]
fn nested_mutual_recursion_with_captures() {
    let src = "outer = program(m) do \
                 is_even = program(n) do if n < m then true else is_odd(n - m) done done \
                 is_odd = program(n) do if n < m then false else is_even(n - m) done done \
                 is_even(10) \
               done \
               outer(1)";
    assert_eq!(run(src), "true");
}

#[test]
fn returned_closure_ignoring_its_parameter() {
    let src = "mk = program(a) do program(b) do a + (6) done done \
               m = mk(2) \
               0 + (m(9))";
    assert_eq!(run(src), "8");
}

#[test]
fn returned_closure_capturing_nothing() {
    let src = "mk = program(a) do program(b) do b done done \
               m = mk(2) \
               0 + (m(9))";
    assert_eq!(run(src), "9");
}

#[test]
fn returned_closure_ignoring_its_parameter_and_capturing_nothing() {
    let src = "mk = program(a) do program(b) do 7 done done \
               m = mk(2) \
               0 + (m(9))";
    assert_eq!(run(src), "7");
}

#[test]
fn recursive_closure_capturing_nothing() {
    let src = "outer = program(a) do \
                 count = program(k) do if k < 1 then 0 else 1 + count(k - 1) done done \
                 count \
               done \
               m = outer(5) \
               0 + (m(4))";
    assert_eq!(run(src), "4");
}

#[test]
fn ignored_parameter_closures_through_apply() {
    let src = "apply = program(f, x) do f(x) done \
               n = 10 \
               const = program(x) do n done \
               apply(const, 1) + apply(program(y) do 3 done, true)";
    assert_eq!(run(src), "13");
}

#[test]
fn polymorphic_value_binding_captured_by_a_closure() {
    let src = "mk = program(a) do program(b) do b done done \
               m = mk(2) \
               g = program(x) do m(x) + 1 done \
               g(4)";
    assert_eq!(run(src), "5");
}

#[test]
fn anonymous_closures_ignoring_their_parameter() {
    let src = "mk = program(a) do program(b) do program(c) do a done done done \
               0 + (mk(4)(5)(6))";
    assert_eq!(run(src), "4");
}

#[test]
fn examples_print_the_expected_output() {
    for (file, expected) in [
        ("fib.goat", "55"),
        ("higher_order.goat", "42"),
        ("records.goat", "7"),
        ("closures.goat", "15"),
        ("closure_shapes.goat", "77"),
    ] {
        let path = format!("{}/../examples/{file}", env!("CARGO_MANIFEST_DIR"));
        let src = fs::read_to_string(&path).unwrap();
        assert_eq!(run(&src), expected, "{file}");
    }
}
