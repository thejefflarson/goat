use goat_checker::check;
use goat_mir::*;

fn run_src(src: &str) -> (Program, Value) {
    let checked = check(src).expect("checks");
    let p = mono(&checked);
    assert_eq!(verify(&p), Ok(()), "{src}");
    let out = run(&p).expect("runs");
    assert_eq!(out.live_allocations, 0);
    (p, out.value)
}

fn value(src: &str) -> Value {
    run_src(src).1
}

fn num(n: f64) -> Value {
    Value::Float(n)
}

#[test]
fn arithmetic() {
    assert_eq!(value("1 + 2 * 3"), num(7.0));
    assert_eq!(value("(1 + 2) * 3"), num(9.0));
    assert_eq!(value("10 / 4"), num(2.5));
    assert_eq!(value("-3 + 5"), num(2.0));
}

#[test]
fn number_literals() {
    assert_eq!(value("1000000"), num(1_000_000.0));
    assert_eq!(value("0.5"), num(0.5));
    assert_eq!(value("0.1 + 0.2"), num(0.1 + 0.2));
}

#[test]
fn booleans_and_unit() {
    assert_eq!(value("1 < 2"), Value::Bool(true));
    assert_eq!(value("3 < 2"), Value::Bool(false));
    assert_eq!(value("x = 5  x < 10"), Value::Bool(true));
    assert_eq!(value(""), Value::Unit);
}

#[test]
fn let_bindings_and_shadowing() {
    assert_eq!(value("a = 2  b = 3  a + b"), num(5.0));
    assert_eq!(value("score = 1  score = score + 1  score"), num(2.0));
    assert_eq!(value("x = 4"), num(4.0));
}

#[test]
fn direct_calls_and_recursion() {
    assert_eq!(
        value("add = program(a, b) do a + b done  add(20, 22)"),
        num(42.0)
    );
    let fib = "fib = program(n) do if n < 2 then n else fib(n - 1) + fib(n - 2) done done fib(10)";
    assert_eq!(value(fib), num(55.0));
}

#[test]
fn mutual_recursion_either_order() {
    let even_first = "is_even = program(n) do if n < 1 then true else is_odd(n - 1) done done \
                      is_odd = program(n) do if n < 1 then false else is_even(n - 1) done done \
                      is_even(10)";
    let odd_first = "is_odd = program(n) do if n < 1 then false else is_even(n - 1) done done \
                     is_even = program(n) do if n < 1 then true else is_odd(n - 1) done done \
                     is_even(7)";
    assert_eq!(value(even_first), Value::Bool(true));
    assert_eq!(value(odd_first), Value::Bool(false));
}

#[test]
fn long_operator_chain() {
    assert_eq!(value(&vec!["1"; 200].join(" + ")), num(200.0));
}

#[test]
fn conditional_without_else_is_unit() {
    let src = "nop = program() do done if true then nop() done";
    assert_eq!(value(src), Value::Unit);
}

#[test]
fn polymorphic_binding_gets_one_function_per_instantiation() {
    let src = "id = program(x) do x done a = id(1) b = id(true) b";
    let (p, v) = run_src(src);
    assert_eq!(v, Value::Bool(true));
    assert_eq!(p.funcs.len(), 3);
    let sigs: Vec<_> = p.funcs[1..]
        .iter()
        .map(|f| (f.params[0].1, f.ret))
        .collect();
    assert!(sigs.contains(&(MTy::Float, MTy::Float)));
    assert!(sigs.contains(&(MTy::Bool, MTy::Bool)));
}

#[test]
fn repeated_instantiation_is_memoized() {
    let src = "id = program(x) do x done id(1) + id(2) + id(3)";
    assert_eq!(run_src(src).0.funcs.len(), 2);
}
