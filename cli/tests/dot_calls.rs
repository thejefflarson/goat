//! Dot calls end to end (ADR 0031): `r.f(a)` passes `r` first, through the
//! interpreter and through wasm.

#[allow(dead_code)]
mod support;

use support::run;

#[test]
fn a_method_reads_its_record() {
    let src = "ball = {x: 3, moved: program(self) do self.x + 1 done};\n\
               print(ball.moved())";
    assert_eq!(run(src), "4");
}

#[test]
fn a_method_takes_arguments_after_the_record() {
    let src = "ball = {x: 3, shifted: program(self, dx, dy) do self.x + dx * dy done};\n\
               print(ball.shifted(2, 5))";
    assert_eq!(run(src), "13");
}

#[test]
fn a_method_on_a_nested_record_gets_the_nested_record() {
    let src = "o = {inner: {x: 4, y: program(self) do self.x done}};\n\
               print(o.inner.y())";
    assert_eq!(run(src), "4");
}

#[test]
fn a_spread_of_values_is_used_at_two_types() {
    let src = "b = {id: program(v) do v done, n: 1};\n\
               a = {...b, k: 5};\n\
               print((a.id)(1));\n\
               print((a.id)(true))";
    assert_eq!(run(src), "1\ntrue");
}

#[test]
fn a_parenthesised_projection_calls_without_the_record() {
    let src = "r = {n: 2, f: program(x) do x * 10 done};\n\
               print((r.f)(4));\n\
               print(r.n)";
    assert_eq!(run(src), "40\n2");
}

#[test]
fn a_dot_call_can_return_a_function_to_call_again() {
    let src = "r = {n: 1, f: program(self, a) do program(b) do self.n + a + b done done};\n\
               print(r.f(10)(100))";
    assert_eq!(run(src), "111");
}

#[test]
fn a_negated_dot_call() {
    let src = "r = {n: 1, f: program(self, a) do self.n + a done};\n\
               print(-r.f(2))";
    assert_eq!(run(src), "-3");
}
