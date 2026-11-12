use goat_checker::{Checked, GoatError, check_with_prelude};
use goat_mir::*;
use std::collections::BTreeMap;

mod common;

use common::{Recorder, foreign_fn};

/// Without the standard prelude, whose tags would join every variant layout.
fn check(src: &str) -> Result<Checked, Vec<GoatError>> {
    check_with_prelude("", src)
}

/// The program and its value, with an `Int` read as the `Float` of the same
/// size, so the layout and closure tests below need not care which number type
/// a whole-number literal took.
fn run_src(src: &str) -> (Program, Value) {
    let checked = check(src).expect("checks");
    let p = mono(&checked).expect("lowers");
    assert_eq!(verify(&p), Ok(()), "{src}");
    let out = run(&p).expect("runs");
    assert_eq!(out.live_allocations, 0);
    (p, as_num(out.value))
}

fn as_num(value: Value) -> Value {
    match value {
        Value::Int(n) => num(n as f64),
        other => other,
    }
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
    assert!(sigs.contains(&(MTy::Int, MTy::Int)));
    assert!(sigs.contains(&(MTy::Bool, MTy::Bool)));
}

#[test]
fn each_use_of_a_generalized_spread_gets_its_own_layout() {
    let src = "b = {mk: program(v) do {w: v} done, n: 1}\n\
               a = {...b, k: 5}\n\
               x = (a.mk)(1)\n\
               y = (a.mk)(true)\n\
               y.w";
    let (p, v) = run_src(src);
    assert_eq!(v, Value::Bool(true));
    for ty in [MTy::Int, MTy::Bool] {
        let wrapped = Layout::Record(vec![ty]);
        assert!(p.layouts.contains(&wrapped), "{:?}", p.layouts);
    }
}

#[test]
fn repeated_instantiation_is_memoized() {
    let src = "id = program(x) do x done id(1) + id(2) + id(3)";
    assert_eq!(run_src(src).0.funcs.len(), 2);
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
    assert_eq!(as_num(out.value), num(500500.0));
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
    assert_eq!(as_num(out.value), num(0.0));
    assert_eq!(out.live_allocations, 0);
}

fn contains(e: &Expr, pred: &impl Fn(&Expr) -> bool) -> bool {
    if pred(e) {
        return true;
    }
    match e {
        Expr::Let(_, a, b) | Expr::BinFloat(_, a, b) | Expr::Cmp(_, a, b) => {
            contains(a, pred) || contains(b, pred)
        }
        Expr::If(c, a, b) => contains(c, pred) || contains(a, pred) || contains(b, pred),
        Expr::CallDirect(_, args) | Expr::MakeClosure(_, args) => {
            args.iter().any(|a| contains(a, pred))
        }
        Expr::CallClosure(callee, args) => {
            contains(callee, pred) || args.iter().any(|a| contains(a, pred))
        }
        Expr::TailCall(callee, args) => {
            let in_callee = match callee {
                Callee::Closure(c) => contains(c, pred),
                Callee::Direct(_) => false,
            };
            in_callee || args.iter().any(|a| contains(a, pred))
        }
        _ => false,
    }
}

fn capturing(p: &Program) -> impl Iterator<Item = &Func> {
    p.funcs
        .iter()
        .filter(|f| f.env.as_ref().is_some_and(|e| !e.captures.is_empty()))
}

#[test]
fn capturing_literal_emits_make_closure_and_capture() {
    let src = "add = program(a) do program(b) do a + b done done  add(1)(2)";
    let (p, v) = run_src(src);
    assert_eq!(v, num(3.0));

    let adder = capturing(&p).next().expect("a capturing closure body");
    assert_eq!(adder.env.as_ref().unwrap().captures, vec![MTy::Int]);
    assert!(contains(&adder.body, &|e| matches!(e, Expr::Capture(0))));
    let makes = |e: &Expr| matches!(e, Expr::MakeClosure(_, c) if c.len() == 1);
    assert!(p.funcs.iter().any(|f| contains(&f.body, &makes)));
}

#[test]
fn curried_capture() {
    assert_eq!(
        value("add = program(a) do program(b) do a + b done done  add(1)(2)"),
        num(3.0)
    );
}

#[test]
fn returned_closure_ignoring_its_parameter() {
    let src = "mk = program(a) do program(b) do a + (6) done done \
               m = mk(2) \
               0 + (m(9))";
    assert_eq!(run_src(src).1, num(8.0));
}

#[test]
fn returned_closure_capturing_nothing() {
    let src = "mk = program(a) do program(b) do b done done \
               m = mk(2) \
               0 + (m(9))";
    assert_eq!(run_src(src).1, num(9.0));
}

#[test]
fn polymorphic_value_binding_captured_by_a_closure() {
    let src = "mk = program(a) do program(b) do b done done \
               m = mk(2) \
               g = program(x) do m(x) + 1 done \
               g(4)";
    assert_eq!(run_src(src).1, num(5.0));
}

#[test]
fn recursive_closure_calls_itself_through_env() {
    let src = "outer = program(n) do \
                 go = program(k) do if k < 1 then 0 else n + go(k - 1) done done \
                 go(3) \
               done \
               outer(10)";
    let (p, v) = run_src(src);
    assert_eq!(v, num(30.0));
    let go = capturing(&p).next().expect("go captures n");
    assert!(contains(&go.body, &|e| matches!(e, Expr::CallClosure(..))));
    assert!(!contains(&go.body, &|e| matches!(e, Expr::CallDirect(..))));
}

#[test]
fn closures_through_a_polymorphic_apply() {
    let src = "apply = program(f, x) do f(x) done \
               n = 10 \
               t = true \
               addn = program(x) do x + n done \
               pick = program(b) do if t then b else false done done \
               if apply(pick, true) then apply(addn, 1) else 0 done";
    let (p, v) = run_src(src);
    assert_eq!(v, num(11.0));
    let applies = p
        .funcs
        .iter()
        .filter(|f| f.env.is_none() && f.params.len() == 2 && f.params[0].1.is_ptr())
        .count();
    assert_eq!(applies, 2, "one apply per ground type");
}

#[test]
fn record_of_capturing_functions() {
    let src = "k = 10 \
               r = {f: program(x) do x + k done, g: program(x) do x * k done}; \
               (r.f)(3) + (r.g)(2)";
    assert_eq!(value(src), num(33.0));
}

#[test]
fn closure_capturing_a_closure() {
    let src = "double = program(n) do n * 2 done \
               twice = program(f) do program(x) do f(f(x)) done done \
               twice(double)(5)";
    assert_eq!(value(src), num(20.0));
}

#[test]
fn captured_record_is_shared_and_released() {
    let src = "p = {x: 1, y: 2} \
               f = program(z) do p.x + p.y + z done \
               f(3) + f(4)";
    assert_eq!(value(src), num(13.0));
}

#[test]
fn anonymous_literal_as_argument() {
    let src = "apply = program(f, x) do f(x) done \
               k = 3 \
               apply(program(y) do y + 1 done, 2) + apply(program(y) do y * k done, 2)";
    assert_eq!(value(src), num(9.0));
}

#[test]
fn anonymous_literal_specializes_per_ground_type() {
    let src = "make = program(x) do program() do x done done \
               if make(true)() then make(5)() else 0 done";
    assert_eq!(value(src), num(5.0));
}

#[test]
fn nested_mutual_recursion_shares_captures() {
    let src = "outer = program(m) do \
                 is_even = program(n) do if n < m then true else is_odd(n - m) done done \
                 is_odd = program(n) do if n < m then false else is_even(n - m) done done \
                 is_even(10) \
               done \
               outer(1)";
    assert_eq!(value(src), Value::Bool(true));
}

#[test]
fn type_variables_of_the_enclosing_scope_reach_the_body() {
    let src = "outer = program(x) do f = program() do y = x  0 done  f() done \
               outer({a: 1}) + outer(2)";
    assert_eq!(value(src), num(0.0));
}

#[test]
fn closures_in_tail_position_release_their_captures() {
    let src = "p = {x: 1} \
               f = program(y) do p.x + y done \
               f(2)";
    assert_eq!(value(src), num(3.0));
}

#[test]
fn unused_capturing_closure_is_released() {
    let src = "p = {x: 1} \
               f = program(y) do p.x + y done \
               g = f \
               1";
    assert_eq!(value(src), num(1.0));
}

#[test]
fn root_closure_result_is_released() {
    let src = "add = program(a) do program(b) do a + b done done  add(1)";
    assert_eq!(value(src), Value::Unit);
}

#[test]
fn closure_called_once_its_capture_exists_runs() {
    for src in [
        "f = program() do g() done  m = 5  g = program() do m done  f()",
        "f = program() do g() done  m = 5  g = program() do m done  x = f()  x",
        "m = 5  f = program() do g() done  g = program() do m done  f()",
    ] {
        assert_eq!(value(src), num(5.0), "{src}");
    }
}

fn lowered(src: &str) -> Program {
    let p = mono(&check(src).expect("checks")).expect("lowers");
    assert_eq!(verify(&p), Ok(()), "{src}");
    p
}

fn root_string(src: &str) -> Option<Vec<u8>> {
    let out = run(&lowered(src)).expect("runs");
    assert_eq!(out.live_allocations, 0, "{src}");
    out.root_string
}

#[test]
fn string_literal_is_a_data_segment_root() {
    let p = lowered("\"hi\"");
    assert_eq!(p.data, vec![b"hi".to_vec()]);
    let root = &p.funcs[0];
    assert_eq!(root.ret, MTy::Ptr(HeapKind::Str));
    assert_eq!(root.body, Expr::StrLit(DataId(0)));
}

#[test]
fn string_roots_render_through_bindings_and_calls() {
    for src in [
        "\"hi\"",
        "s = \"hi\"  s",
        "id = program(x) do x done  id(\"hi\")",
        "pick = program(b) do if b then \"hi\" else \"yo\" done done  pick(true)",
    ] {
        assert_eq!(root_string(src), Some(b"hi".to_vec()), "{src}");
    }
}

#[test]
fn empty_and_non_ascii_strings_keep_their_bytes() {
    assert_eq!(root_string("\"a\\nb\""), Some(b"a\nb".to_vec()));
    assert_eq!(root_string("\"\""), Some(Vec::new()));
    assert_eq!(
        root_string("\"h\u{e9}\""),
        Some("h\u{e9}".as_bytes().to_vec())
    );
}

#[test]
fn identical_literals_share_one_data_entry() {
    let p = lowered("a = \"x\"  b = \"x\"  c = \"y\"  b");
    assert_eq!(p.data, vec![b"x".to_vec(), b"y".to_vec()]);
}

#[test]
fn strings_inside_records_are_released_with_the_record() {
    let src = "r = {name: \"hi\", n: 1}  r.n";
    assert_eq!(value(src), num(1.0));
    assert_eq!(
        root_string("r = {name: \"hi\", n: 1}  r.name"),
        Some(b"hi".to_vec())
    );
    let p = lowered("{name: \"hi\"}");
    assert_eq!(
        p.layouts,
        vec![Layout::Record(vec![MTy::Ptr(HeapKind::Str)])]
    );
    assert_eq!(run(&p).expect("runs").root_string, None);
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
    assert_eq!(p.layouts, vec![Layout::Record(vec![MTy::Int, MTy::Bool])]);
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

const LENGTH: &str = "length = program(xs) do match xs do Empty then 0 \
                      Link(first, rest) then 1 + length(rest) done done ";

#[test]
fn nullary_and_unary_tags_match() {
    assert_eq!(
        value("tag Circle match Circle(5) do Circle(r) then r else 0 done"),
        num(5.0)
    );
    let pick = "tag A tag B f = program(s) do match s do A then 1 B then 2 done done ";
    assert_eq!(value(&format!("tag A {pick} f(A)")), num(1.0));
    assert_eq!(value(&format!("tag B {pick} f(B)")), num(2.0));
}

#[test]
fn a_recursive_list_is_measured() {
    let src = format!("{LENGTH} length(Link(1, Link(2, Link(3, Empty))))");
    assert_eq!(value(&src), num(3.0));
    assert_eq!(value(&format!("{LENGTH} length(Empty)")), num(0.0));
}

#[test]
fn multi_field_payloads_bind_by_position() {
    let src =
        "tag Pair sum = program(p) do match p do Pair(a, b) then a + b done done sum(Pair(3, 4))";
    assert_eq!(value(src), num(7.0));
}

#[test]
fn a_whole_payload_is_rebuilt_as_a_record_and_taken_apart_again() {
    let src = "tag Pair rewrap = program(p) do match p do Pair(r) then Pair(r) done done \
               sum = program(p) do match p do Pair(a, b) then a - b done done \
               sum(rewrap(Pair(10, 3)))";
    assert_eq!(value(src), num(7.0));
}

#[test]
fn a_tree_is_summed_and_a_list_mapped() {
    let tree = "tag Leaf tag Node sum = program(t) do match t do Leaf(n) then n \
                Node(l, r) then sum(l) + sum(r) done done \
                sum(Node(Node(Leaf(1), Leaf(2)), Leaf(3)))";
    assert_eq!(value(tree), num(6.0));
    let map = "map = program(f, xs) do match xs do Empty then Empty \
               Link(x, rest) then Link(f(x), map(f, rest)) done done \
               total = program(xs) do match xs do Empty then 0 \
               Link(x, rest) then x + total(rest) done done \
               double = program(n) do n * 2 done \
               total(map(double, Link(1, Link(2, Link(3, Empty)))))";
    assert_eq!(value(map), num(12.0));
}

#[test]
fn binders_are_captured_by_closures_in_an_arm() {
    let src = "tag Box f = program(x) do match x do Box(n) then program(k) do n + k done done done \
               add = f(Box(10)) \
               add(5)";
    assert_eq!(value(src), num(15.0));
}

#[test]
fn an_open_match_with_else_ignores_other_tags() {
    let src = "tag A tag B tag C f = program(x) do match x do A(n) then n else 0 done done \
               f(A(4)) + f(B) + f(C(1))";
    assert_eq!(value(src), num(4.0));
}

#[test]
fn alpha_equivalent_recursive_types_specialize_once() {
    let one = format!("{LENGTH} length(Link(1, Empty)) + length(Link(2, Link(3, Empty)))");
    let (p, v) = run_src(&one);
    assert_eq!(v, num(3.0));
    let two = format!("{LENGTH} length(Link(1, Empty))");
    assert_eq!(p.funcs.len(), run_src(&two).0.funcs.len());
}

#[test]
fn the_same_list_through_two_polymorphic_helpers_shares_one_layout() {
    let src = format!(
        "{LENGTH} id = program(x) do x done \
         length(id(Link(1, Empty))) + length(id(id(Link(2, Link(3, Empty)))))"
    );
    let (p, v) = run_src(&src);
    assert_eq!(v, num(3.0));
    let variants = p
        .layouts
        .iter()
        .filter(|l| matches!(l, Layout::Variant(_)))
        .count();
    assert_eq!(variants, 1);
}

#[test]
fn a_recursive_layout_refers_to_itself() {
    let (p, _) = run_src(&format!("{LENGTH} length(Link(1, Empty))"));
    let [Layout::Variant(tags)] = &p.layouts[..] else {
        panic!("one variant layout: {:?}", p.layouts);
    };
    let link = &tags[&1];
    assert_eq!(link[0], MTy::Int);
    assert_eq!(link[1], MTy::Ptr(HeapKind::Variant(LayoutId(0))));
    assert!(tags[&0].is_empty());
}

#[test]
fn a_long_chain_is_built_and_dropped_without_leaking() {
    let src = "build = program(n, acc) do if n < 1 then acc else build(n - 1, Link(n, acc)) done done \
               build(3000, Empty)";
    assert_eq!(value(src), Value::Unit);
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

fn variant_layouts(p: &Program) -> Vec<&BTreeMap<u32, Vec<MTy>>> {
    p.layouts
        .iter()
        .filter_map(|l| match l {
            Layout::Variant(tags) => Some(tags),
            Layout::Record(_) => None,
        })
        .collect()
}

#[test]
fn a_tag_matched_at_two_widths_has_one_layout() {
    let src = "tag Circle tag Square s = Circle(5) \
               narrow = program(v) do match v do Circle(r) then r done done \
               wide = program(v) do match v do Circle(r) then r Square(w) then w done done \
               narrow(s) + wide(s)";
    let (p, v) = run_src(src);
    assert_eq!(v, num(10.0));
    let [tags] = variant_layouts(&p)[..] else {
        panic!("one variant layout: {:?}", p.layouts);
    };
    assert_eq!(
        tags,
        &BTreeMap::from([(0, vec![MTy::Int]), (1, vec![MTy::Int])])
    );
}

#[test]
fn the_order_of_the_two_widths_does_not_matter() {
    let src = "tag Circle tag Square s = Circle(5) \
               narrow = program(v) do match v do Circle(r) then r done done \
               wide = program(v) do match v do Circle(r) then r Square(w) then w done done \
               wide(s) + narrow(s)";
    let (p, v) = run_src(src);
    assert_eq!(v, num(10.0));
    assert_eq!(variant_layouts(&p).len(), 1);
}

#[test]
fn a_nested_tag_matched_at_two_widths_has_one_layout_per_level() {
    let src = "tag Box tag Circle tag Square s = Box(Circle(5)) \
               narrow = program(v) do match v do Box(c) then match c do Circle(r) then r done done done \
               wide = program(v) do match v do Box(c) then \
                 match c do Circle(r) then r Square(w) then w done done done \
               narrow(s) + wide(s)";
    let (p, v) = run_src(src);
    assert_eq!(v, num(10.0));
    assert_eq!(variant_layouts(&p).len(), 2);
}

#[test]
fn a_recursive_value_matched_at_two_widths_has_one_layout() {
    let src = "xs = Link(1, Empty) \
               narrow = program(l) do match l do Empty then 0 Link(a, r) then a done done \
               wide = program(l) do match l do Empty then 0 Link(a, r) then a Other(n) then n done done \
               narrow(xs) + wide(xs)";
    let (p, v) = run_src(src);
    assert_eq!(v, num(2.0));
    assert_eq!(variant_layouts(&p).len(), 1);
}

#[test]
fn a_tag_with_two_payload_types_gets_two_layouts() {
    let src = "tag Some num = program(v) do match v do Some(n) then n else 0 done done \
               flag = program(v) do match v do Some(b) then if b then 1 else 0 done else 0 done done \
               num(Some(4)) + flag(Some(true))";
    let (p, v) = run_src(src);
    assert_eq!(v, num(5.0));
    let layouts = variant_layouts(&p);
    assert_eq!(layouts.len(), 2);
    assert_ne!(layouts[0], layouts[1]);
}

fn record_layouts(p: &Program) -> Vec<&Vec<MTy>> {
    p.layouts
        .iter()
        .filter_map(|l| match l {
            Layout::Record(fields) => Some(fields),
            Layout::Variant(_) => None,
        })
        .collect()
}

#[test]
fn spread_update_and_override_values() {
    assert_eq!(
        value("p = {x: 1, y: 2} q = {...p, x: 5} q.x + q.y"),
        num(7.0)
    );
    assert_eq!(value("p = {x: 1} q = {...p, y: 4} q.x + q.y"), num(5.0));
    assert_eq!(
        value("p = {x: 1} q = {...p, x: true} q.x"),
        Value::Bool(true)
    );
}

#[test]
fn a_known_override_leaves_one_slot_for_the_label() {
    let (p, v) = run_src("p = {x: 1, y: 2} q = {...p, x: true} q.y");
    assert_eq!(v, num(2.0));
    assert!(
        record_layouts(&p).contains(&&vec![MTy::Bool, MTy::Int]),
        "{:?}",
        p.layouts
    );
}

#[test]
fn a_shadowed_field_behind_a_row_variable_is_dropped_from_the_layout() {
    let src = "bump = program(m) do {...m, x: true} done \
               q = bump({x: 1, y: 2}) \
               q.y";
    let (p, v) = run_src(src);
    assert_eq!(v, num(2.0));
    let layouts = record_layouts(&p);
    assert!(layouts.contains(&&vec![MTy::Bool, MTy::Int]), "{layouts:?}");
    assert!(layouts.iter().all(|l| l.len() <= 2), "{layouts:?}");
}

#[test]
fn rest_copies_the_remaining_fields_into_a_smaller_record() {
    let src = "{x, ...rest} = {x: 1, y: 2, z: true} rest.y";
    let (p, v) = run_src(src);
    assert_eq!(v, num(2.0));
    assert!(record_layouts(&p).contains(&&vec![MTy::Int, MTy::Bool]));
}

#[test]
fn destructuring_reads_fields_by_label() {
    assert_eq!(value("{y, x} = {x: 1, y: 10} y - x"), num(9.0));
    let param = "norm = program({x, y}) do x * x + y * y done norm({y: 4, x: 3})";
    assert_eq!(value(param), num(25.0));
}

const DECLS: &str = "forward = foreign \"test\" \"forward\" (Number) -> Unit\n\
                     double = foreign \"test\" \"double\" (Number) -> Number\n\
                     shout = foreign \"test\" \"shout\" (String) -> String\n\
                     say = foreign \"test\" \"say\" (String) -> Unit\n";

fn hosted(body: &str) -> (Program, Outcome, Recorder) {
    let src = format!("{DECLS}{body}");
    let p = mono(&check(&src).expect("checks")).expect("lowers");
    assert_eq!(verify(&p), Ok(()), "{src}");
    let mut host = Recorder::default();
    let out = run_with_host(&p, &mut host).expect("runs");
    assert_eq!(out.live_allocations, 0, "{src}");
    (p, out, host)
}

fn names(host: &Recorder) -> Vec<&str> {
    host.calls.iter().map(|(n, _)| n.as_str()).collect()
}

#[test]
fn a_declaration_nothing_uses_adds_no_import() {
    assert!(hosted("1 + 2").0.foreign.is_empty());
    assert!(
        hosted("go = program() do forward(1) done\n1")
            .0
            .foreign
            .is_empty()
    );
}

#[test]
fn only_the_foreign_functions_a_program_uses_become_imports() {
    let (p, _, _) = hosted("forward(double(1))");
    assert_eq!(p.foreign.len(), 2);
}

#[test]
fn a_call_lowers_to_call_foreign_of_one_import() {
    let (p, out, host) = hosted("forward(10)");
    assert_eq!(
        p.foreign,
        [foreign_fn("forward", vec![MTy::Float], MTy::Unit)]
    );
    assert_eq!(effects(&p.funcs[0].body), [Effect::Foreign(ForeignId(0))]);
    assert_eq!(out.value, Value::Unit);
    assert_eq!(
        host.calls,
        [("forward".into(), vec![HostValue::Number(10.0)])]
    );
}

#[test]
fn a_foreign_function_used_twice_shares_its_import() {
    let (p, _, host) = hosted("forward(1); forward(2); forward(3)");
    assert_eq!(p.foreign.len(), 1);
    assert_eq!(
        effects(&p.funcs[0].body),
        [Effect::Foreign(ForeignId(0)); 3]
    );
    assert_eq!(names(&host), ["forward"; 3]);
}

#[test]
fn a_discarded_unit_call_survives_in_order_through_reference_counting() {
    let (p, out, host) = hosted("r = forward(1); forward(2); forward(double(3)); 0");
    assert_eq!(
        effects(&p.funcs[0].body),
        [
            Effect::Foreign(ForeignId(0)),
            Effect::Foreign(ForeignId(0)),
            Effect::Foreign(ForeignId(1)),
            Effect::Foreign(ForeignId(0)),
        ]
    );
    assert_eq!(as_num(out.value), num(0.0));
    let args: Vec<_> = host.calls.iter().map(|(_, a)| a.clone()).collect();
    assert_eq!(
        args,
        [
            vec![HostValue::Number(1.0)],
            vec![HostValue::Number(2.0)],
            vec![HostValue::Number(3.0)],
            vec![HostValue::Number(6.0)],
        ]
    );
}

#[test]
fn arguments_are_evaluated_left_to_right_before_the_call() {
    let (_, out, host) = hosted("say(shout(\"a\")); double(double(1) + double(2))");
    assert_eq!(as_num(out.value), num(12.0));
    assert_eq!(names(&host), ["shout", "say", "double", "double", "double"]);
}

#[test]
fn a_string_argument_is_borrowed_and_a_returned_string_is_owned() {
    let (_, out, host) = hosted("s = shout(\"hi\")\nsay(s); say(s); say(shout(s)); 1");
    assert_eq!(as_num(out.value), num(1.0));
    let said: Vec<_> = host
        .calls
        .iter()
        .filter(|(n, _)| n == "say")
        .map(|(_, a)| a[0].clone())
        .collect();
    assert_eq!(
        said,
        [
            HostValue::Str("hi!".into()),
            HostValue::Str("hi!".into()),
            HostValue::Str("hi!!".into()),
        ]
    );
}

#[test]
fn a_foreign_function_is_a_value() {
    let (p, out, host) = hosted("g = double\ng(4)");
    assert_eq!(as_num(out.value), num(8.0));
    assert_eq!(names(&host), ["double"]);
    assert_eq!(p.foreign.len(), 1);

    let apply = "apply = program(f, x) do f(x) done\napply(double, 5)";
    assert_eq!(as_num(hosted(apply).1.value), num(10.0));

    let unit = "h = forward\nh(1); h(2); 0";
    assert_eq!(names(&hosted(unit).2), ["forward", "forward"]);

    let strings = "apply = program(f, x) do f(x) done\nsay(apply(shout, \"a\")); 0";
    assert_eq!(as_num(hosted(strings).1.value), num(0.0));
}

#[test]
fn a_foreign_binding_can_be_the_value_of_the_program() {
    let src = "f = foreign \"test\" \"double\" (Number) -> Number";
    let p = mono(&check(src).expect("checks")).expect("lowers");
    assert_eq!(verify(&p), Ok(()));
    let out = run_with_host(&p, &mut Recorder::default()).expect("runs");
    assert_eq!(out.live_allocations, 0);
}

#[test]
fn a_foreign_call_inside_a_function_and_a_loop_runs_each_time() {
    let (_, _, host) = hosted(
        "go = program(n) do forward(n) done\nrepeat 3 times do go(7) done;\nfor i from 1 to 2 do forward(i) done;\n0",
    );
    assert_eq!(names(&host), ["forward"; 5]);
}

/// Each level calls the next at two different types, so the leaf needs one
/// copy per path of wrappers although every type stays small.
fn branching_chain(levels: usize) -> String {
    let mut src = String::from("f0 = program(x) do 1 done\n");
    for k in 1..=levels {
        src.push_str(&format!(
            "f{k} = program(x) do if true then f{}({{a: x}}) else f{}({{b: x}}) done done\n",
            k - 1,
            k - 1
        ));
    }
    src.push_str(&format!("f{levels}(1)"));
    src
}

#[test]
fn specializations_double_with_each_branching_level() {
    let funcs = |levels| {
        let checked = check(&branching_chain(levels)).expect("checks");
        mono(&checked).expect("lowers").funcs.len()
    };
    assert_eq!(funcs(6) * 4, funcs(8));
}

#[test]
fn a_program_that_needs_too_many_specializations_is_rejected_with_a_span() {
    let src = branching_chain(16);
    let checked = check(&src).expect("checks");
    let errors = mono(&checked).expect_err("too many specializations");
    let [error] = &errors[..] else {
        panic!("one error: {errors:?}");
    };
    assert_eq!(
        error.message,
        "program too complex: it needs too many specialized functions"
    );
    assert!(!error.span.in_prelude() && error.span.end <= src.len());
}

#[test]
fn many_tags_in_many_families_keep_every_layout_sparse() {
    let tags = 300;
    let mut src: String = (0..tags).map(|i| format!("tag T{i}\n")).collect();
    for i in 0..tags {
        src.push_str(&format!("v{i} = T{i}({i})\n"));
    }
    src.push('0');
    let (p, _) = run_src(&src);
    let layouts = variant_layouts(&p);
    assert_eq!(layouts.len(), tags);
    assert!(layouts.iter().all(|table| table.len() == 1));
}

#[test]
fn an_int_literal_past_the_profile_becomes_a_trap() {
    let checked = check("3000000000").expect("checks");
    let desktop = mono(&checked).expect("lowers");
    assert_eq!(desktop.profile, Profile::Desktop);
    assert_eq!(
        run(&desktop).expect("runs").value,
        Value::Int(3_000_000_000)
    );
    let embedded = mono_for(&checked, Profile::Embedded).expect("lowers");
    assert_eq!(embedded.profile, Profile::Embedded);
    assert_eq!(verify(&embedded), Ok(()));
    assert_eq!(run(&embedded), Err(InterpError::Trap(INT_OVERFLOW.into())));
}

#[test]
fn a_literal_that_fits_the_profile_stays_a_constant() {
    let checked = check("2147483647").expect("checks");
    let embedded = mono_for(&checked, Profile::Embedded).expect("lowers");
    assert_eq!(
        run(&embedded).expect("runs").value,
        Value::Int(2_147_483_647)
    );
}
