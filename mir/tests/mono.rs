use goat_checker::check;
use goat_mir::*;

fn run_src(src: &str) -> (Program, Value) {
    let checked = check(src).expect("checks");
    let p = mono(&checked).expect("lowers");
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

fn errors(src: &str) -> Vec<String> {
    let checked = check(src).expect("checks");
    mono(&checked)
        .expect_err("rejected")
        .into_iter()
        .map(|e| e.message)
        .collect()
}

fn has_tail_call(e: &Expr) -> bool {
    match e {
        Expr::TailCall(..) => true,
        Expr::Let(_, v, b) => has_tail_call(v) || has_tail_call(b),
        Expr::If(_, t, f) => has_tail_call(t) || has_tail_call(f),
        _ => false,
    }
}

#[test]
fn known_function_passed_as_value() {
    let src = "double = program(x) do x * 2 done \
               apply = program(f, x) do f(x) done \
               apply(double, 21)";
    let (p, v) = run_src(src);
    assert_eq!(v, num(42.0));
    assert!(p.funcs.iter().any(|f| f.env.is_some()));
}

#[test]
fn function_parameter_used_more_than_once_or_not_at_all() {
    let twice = "double = program(x) do x * 2 done \
                 twice = program(f, x) do f(f(x)) done twice(double, 5)";
    assert_eq!(value(twice), num(20.0));
    let skip = "double = program(x) do x * 2 done \
                pick = program(f, c) do if c then f(1) else 0 done done \
                pick(double, false) + pick(double, true)";
    assert_eq!(value(skip), num(2.0));
}

#[test]
fn function_bound_to_a_local_and_returned() {
    let src = "double = program(x) do x * 2 done \
               choose = program(c) do if c then double else double done done \
               g = choose(true)  g(4)";
    assert_eq!(value(src), num(8.0));
    assert_eq!(
        value("double = program(x) do x * 2 done  g = double  g(3)"),
        num(6.0)
    );
}

#[test]
fn polymorphic_function_value_is_specialized_per_use() {
    let src = "id = program(x) do x done \
               apply = program(f, x) do f(x) done \
               n = apply(id, 3) \
               b = apply(id, true) \
               n";
    let (p, v) = run_src(src);
    assert_eq!(v, num(3.0));
    assert!(p.sigs.len() >= 2);
}

#[test]
fn trailing_function_binding_is_a_value() {
    let checked = check("double = program(x) do x * 2 done").expect("checks");
    let p = mono(&checked).expect("lowers");
    assert_eq!(verify(&p), Ok(()));
}

#[test]
fn tail_recursive_accumulator_runs_in_constant_stack() {
    let src = "sum = program(n, acc) do if n < 1 then acc else sum(n - 1, acc + n) done done \
               sum(1000, 0)";
    let checked = check(src).expect("checks");
    let p = mono(&checked).expect("lowers");
    assert_eq!(verify(&p), Ok(()));
    assert!(p.funcs.iter().any(|f| has_tail_call(&f.body)));
    let out = run_with_depth(&p, 8).expect("constant stack");
    assert_eq!(out.value, num(500500.0));
    assert_eq!(out.live_allocations, 0);
}

#[test]
fn tail_call_releases_closure_parameters() {
    let src = "double = program(x) do x * 2 done \
               loop = program(f, n) do if n < 1 then f(n) else loop(f, n - 1) done done \
               loop(double, 500)";
    let checked = check(src).expect("checks");
    let p = mono(&checked).expect("lowers");
    assert_eq!(verify(&p), Ok(()));
    let out = run_with_depth(&p, 8).expect("constant stack");
    assert_eq!(out.value, num(0.0));
    assert_eq!(out.live_allocations, 0);
}

#[test]
fn captured_local_is_a_spanned_error() {
    let src = "make = program(a) do inner = program(x) do x + a done inner(1) done make(2)";
    let checked = check(src).expect("checks");
    let errs = mono(&checked).expect_err("rejected");
    assert_eq!(errs.len(), 1);
    assert_eq!(
        errs[0].message,
        "`a` is captured from an enclosing scope; closures are not supported yet (Phase 4)"
    );
    assert_eq!(&src[errs[0].span.start..errs[0].span.end], "a");
}

#[test]
fn captured_top_level_value_is_a_spanned_error() {
    let errs = errors("a = 2  f = program(x) do x + a done  f(1)");
    assert_eq!(errs.len(), 1);
    assert!(errs[0].starts_with("`a` is captured"), "{errs:?}");
}

#[test]
fn strings_are_not_supported_yet() {
    for src in ["\"hi\"", "id = program(x) do x done  id(\"hi\")"] {
        let errs = errors(src);
        assert!(!errs.is_empty(), "{src}");
        assert!(
            errs.iter().all(|m| m.ends_with("are not supported yet")),
            "{src}: {errs:?}"
        );
    }
}

#[test]
fn record_literal_and_field() {
    assert_eq!(value("p = {x: 1, y: 2}  p.x"), num(1.0));
    assert_eq!(value("p = {y: 2, x: 1}  p.y - p.x"), num(1.0));
    assert_eq!(value("{x: 5}.x"), num(5.0));
}

#[test]
fn record_layout_sorts_labels() {
    let (p, _) = run_src("p = {b: true, a: 1}  p.a");
    assert_eq!(p.layouts, vec![Layout::Record(vec![MTy::Float, MTy::Bool])]);
}

#[test]
fn nested_records() {
    let src = "line = {from: {x: 0, y: 0}, to: {x: 3, y: 4}}  line.to.x + line.from.y";
    assert_eq!(value(src), num(3.0));
    assert_eq!(value("{a: {b: {c: 7}}}.a.b.c"), num(7.0));
}

#[test]
fn top_level_record_result_is_released() {
    let (_, v) = run_src("p = {x: 1}");
    assert_eq!(v, Value::Unit);
    assert_eq!(value("{a: {b: 1}}"), Value::Unit);
}

#[test]
fn records_through_calls() {
    let src = "mk = program(n) do {v: n, w: n + 1} done  r = mk(4)  r.v + r.w";
    assert_eq!(value(src), num(9.0));
    let src = "pick = program(r) do r.b done  pick({a: 1, b: 2})";
    assert_eq!(value(src), num(2.0));
}

#[test]
fn row_polymorphic_access_specializes_per_layout() {
    let src = "getx = program(p) do p.x done  getx({x: 1, y: 2}) + getx({x: 9, z: true})";
    let (p, v) = run_src(src);
    assert_eq!(v, num(10.0));
    assert_eq!(p.layouts.len(), 2);
    let field_indices: Vec<_> = p.funcs.iter().skip(1).map(field_index).collect();
    assert_eq!(field_indices, [Some(0), Some(0)]);
    let param_layouts: Vec<_> = p.funcs.iter().skip(1).map(|f| f.params[0].1).collect();
    assert_ne!(param_layouts[0], param_layouts[1]);
}

#[test]
fn row_polymorphic_access_uses_per_type_index() {
    let src = "getx = program(p) do p.x done  getx({a: 0, x: 3}) + getx({x: 4, z: 1})";
    let (p, v) = run_src(src);
    assert_eq!(v, num(7.0));
    let mut indices: Vec<_> = p.funcs.iter().skip(1).filter_map(field_index).collect();
    indices.sort();
    assert_eq!(indices, [0, 1]);
}

#[test]
fn records_and_field_values_drop_cleanly_in_branches() {
    let src = "f = program(r) do if r.a < 1 then r.b else r.a done done f({a: 0, b: 5})";
    assert_eq!(value(src), num(5.0));
}

fn field_index(f: &Func) -> Option<usize> {
    fn find(e: &Expr) -> Option<usize> {
        match e {
            Expr::Field(_, i) => Some(*i),
            Expr::Let(_, a, b) => find(a).or_else(|| find(b)),
            Expr::If(c, a, b) => find(c).or_else(|| find(a)).or_else(|| find(b)),
            _ => None,
        }
    }
    find(&f.body)
}
