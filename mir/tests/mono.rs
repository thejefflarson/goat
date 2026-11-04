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
    assert_eq!(adder.env.as_ref().unwrap().captures, vec![MTy::Float]);
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
               r = {f: program(x) do x + k done, g: program(x) do x * k done} \
               r.f(3) + r.g(2)";
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

#[test]
fn well_typed_variants_are_a_staged_diagnostic_not_a_panic() {
    let programs = [
        "Circle(5)",
        "match Circle(5) do Circle(r) then r else 0 done",
        "f = program(s) do match s do A then 1 B then 2 done done f(A)",
    ];
    for src in programs {
        let checked = check(src).expect("checks");
        let errors = mono(&checked).expect_err("variants are not lowered yet");
        assert!(!errors.is_empty(), "{src}");
        for e in &errors {
            assert!(e.message.contains("not supported yet"), "{src}: {e}");
            assert!(e.span.end > e.span.start, "{src}: {e}");
        }
    }
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
