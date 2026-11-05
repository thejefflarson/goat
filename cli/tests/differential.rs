//! Differential tests: every program runs through the MIR interpreter (the
//! oracle) and through the compiled wasm under wasmtime, and both must print
//! the same thing. Neither side may leave a heap object live.

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
        ("hello.goat", "hello, world"),
        ("lists.goat", "15"),
        ("spread.goat", "25"),
        ("list_literals.goat", "29"),
        (
            "stdlib.goat",
            "[1, 4, 7, 9]\n[8, 14, 18]\n9\n4\n[7, 1, 9, 4, 5, 6, 0]\n[9, 7, 4, 1]\n1\n4\n7\n9\ntrue\nfalse\n26",
        ),
        (
            "constraints.goat",
            "{x: 21, y: 42}\n[true, true, false]\ntrue",
        ),
    ] {
        let path = format!("{}/../examples/{file}", env!("CARGO_MANIFEST_DIR"));
        let src = fs::read_to_string(&path).unwrap();
        assert_eq!(run(&src), expected, "{file}");
    }
}

#[test]
fn string_literals_print_verbatim() {
    assert_eq!(run("\"hello\""), "hello");
    assert_eq!(run("s = \"hi\"\ns"), "hi");
    assert_eq!(run("\"a\\nb\\tc\""), "a\nb\tc");
    assert_eq!(run("\"\""), "");
}

const LENGTH: &str = "length = program(xs) do match xs do Empty then 0 \
                      Link(first, rest) then 1 + length(rest) done done ";

#[test]
fn nullary_tags_pick_an_arm() {
    let pick = "f = program(s) do match s do A then 1 B then 2 else 3 done done ";
    assert_eq!(run(&format!("{pick} f(A)")), "1");
    assert_eq!(run(&format!("{pick} f(B)")), "2");
    assert_eq!(run(&format!("{pick} f(C)")), "3");
}

#[test]
fn a_tag_carries_a_payload() {
    assert_eq!(
        run("match Circle(5) do Circle(r) then r * r else 0 done"),
        "25"
    );
    let src = "area = program(s) do match s do Circle(r) then 3 * r * r \
               Rect(w, h) then w * h done done \
               area(Circle(2)) + area(Rect(3, 4))";
    assert_eq!(run(src), "24");
}

#[test]
fn length_of_a_list() {
    assert_eq!(run(&format!("{LENGTH} length(Empty)")), "0");
    assert_eq!(
        run(&format!(
            "{LENGTH} length(Link(1, Link(2, Link(3, Empty))))"
        )),
        "3"
    );
}

#[test]
fn size_of_a_tree() {
    let src = "size = program(t) do match t do Leaf then 1 \
               Node(l, r) then size(l) + size(r) done done \
               size(Node(Node(Leaf, Leaf), Node(Leaf, Node(Leaf, Leaf))))";
    assert_eq!(run(src), "5");
}

#[test]
fn map_over_a_list_shares_nothing_it_should_not() {
    let src = "map = program(f, xs) do match xs do Empty then Empty \
               Link(x, rest) then Link(f(x), map(f, rest)) done done \
               total = program(xs) do match xs do Empty then 0 \
               Link(x, rest) then x + total(rest) done done \
               xs = Link(1, Link(2, Link(3, Empty))) \
               double = program(n) do n * 2 done \
               total(map(double, xs)) + total(xs)";
    assert_eq!(run(src), "18");
}

#[test]
fn a_closure_captures_a_pattern_binder() {
    let src = "f = program(x) do match x do Box(n) then program(k) do n + k done done done \
               add = f(Box(10)) \
               add(5)";
    assert_eq!(run(src), "15");
}

#[test]
fn a_multi_field_payload_drops_every_field() {
    let src = "f = program(t) do match t do Pair(a, b) then 1 done done \
               f(Pair(Link(1, Empty), Link(2, Link(3, Empty))))";
    assert_eq!(run(src), "1");
}

#[test]
fn a_million_link_chain_is_dropped_in_constant_stack() {
    let src = "build = program(n, acc) do \
                 if n < 1 then acc else build(n - 1, Link(n, acc)) done done \
               build(1000000, Empty)";
    assert_eq!(run(src), "");
}

#[test]
fn a_million_link_list_is_counted_and_then_dropped() {
    let src = "build = program(n, acc) do \
                 if n < 1 then acc else build(n - 1, Link(n, acc)) done done \
               count = program(xs, n) do match xs do Empty then n \
                 Link(first, rest) then count(rest, n + 1) done done \
               count(build(1000000, Empty), 0)";
    assert_eq!(run(src), "1000000");
}

#[test]
fn a_deep_left_leaning_tree_is_dropped_in_constant_stack() {
    let src = "grow = program(n, t) do \
                 if n < 1 then t else grow(n - 1, Node(t, Leaf)) done done \
               grow(500000, Leaf)";
    assert_eq!(run(src), "");
}

#[test]
fn a_chain_through_a_second_type_is_dropped_in_constant_stack() {
    let src = "grow = program(n, t) do \
                 if n < 1 then t else grow(n - 1, Node(Cons(t, Nil))) done done \
               grow(200000, Leaf)";
    assert_eq!(run(src), "");
}

#[test]
fn a_chain_through_records_and_closures_is_dropped_in_constant_stack() {
    let src = "grow = program(n, t) do if n < 1 then t \
               else grow(n - 1, Wrap({a: t, b: program(x) do x done})) done done \
               grow(100000, Stop)";
    assert_eq!(run(src), "");
    let closures = "chain = program(n, f) do \
                      if n < 1 then f else chain(n - 1, program(x) do f(x) + 1 done) done done \
                    chain(200000, program(x) do x done)";
    assert_eq!(run(closures), "");
}

#[test]
fn variants_hold_closures_strings_records_and_other_variants() {
    let apply = "apply = program(c, x) do match c do Fn(f) then f(x) done done \
                 apply(Fn(program(n) do n * 3 done), 4)";
    assert_eq!(run(apply), "12");
    assert_eq!(
        run("g = program(x) do match x do Name(s) then s done done g(Name(\"hi\"))"),
        "hi"
    );
    let point = "g = program(x) do match x do Pt(p) then p.a + p.b done done g(Pt({a: 1, b: 2}))";
    assert_eq!(run(point), "3");
    let nested = format!("{LENGTH} length(Link(Link(1, Empty), Link(Link(2, Empty), Empty)))");
    assert_eq!(run(&nested), "2");
}

#[test]
fn two_types_may_refer_to_each_other() {
    let src = "len_t = program(t) do match t do Leaf then 0 Node(f) then 1 + len_f(f) done done \
               len_f = program(f) do match f do Nil then 0 \
                 Cons(t, r) then len_t(t) + len_f(r) done done \
               len_t(Node(Cons(Node(Nil), Cons(Leaf, Nil))))";
    assert_eq!(run(src), "2");
}

#[test]
fn a_list_changes_its_element_type_through_map() {
    let src = "map = program(f, xs) do match xs do Empty then Empty \
               Link(x, r) then Link(f(x), map(f, r)) done done \
               anytrue = program(xs) do match xs do Empty then false \
                 Link(x, r) then if x then true else anytrue(r) done done done \
               anytrue(map(program(n) do n < 2 done, Link(1, Link(2, Empty))))";
    assert_eq!(run(src), "true");
}

#[test]
fn tags_flow_through_branches_and_nested_matches() {
    let pick = "pick = program(b) do if b then A(1) else B(2) done done \
                f = program(x) do match x do A(n) then n B(n) then n * 10 done done \
                f(pick(true)) + f(pick(false))";
    assert_eq!(run(pick), "21");
    let nested = "f = program(x) do match (match x do A then B else C done) do \
                  B then 1 C then 2 done done f(A) + f(Q)";
    assert_eq!(run(nested), "3");
    let shadow = "f = program(x) do match x do Pair(a, b) then \
                  match a do Pair(a, c) then a + b + c done done done f(Pair(Pair(1, 2), 3))";
    assert_eq!(run(shadow), "6");
}

#[test]
fn a_tail_call_in_an_arm_runs_in_constant_stack() {
    let src = "go = program(xs, acc) do match xs do Empty then acc \
               Link(x, r) then go(r, acc + x) done done \
               build = program(n, acc) do \
                 if n < 1 then acc else build(n - 1, Link(n, acc)) done done \
               go(build(100000, Empty), 0)";
    assert_eq!(run(src), "5000050000");
}

#[test]
fn a_tag_bound_once_and_matched_at_two_widths_still_runs() {
    let src = "s = Circle(5) \
               narrow = program(v) do match v do Circle(r) then r done done \
               wide = program(v) do match v do Circle(r) then r Square(w) then w done done \
               narrow(s) + wide(s)";
    assert_eq!(run(src), "10");
}

#[test]
fn spread_adds_overrides_and_retypes_fields() {
    assert_eq!(run("p = {x: 1} q = {...p, y: 2} q.x + q.y"), "3");
    assert_eq!(run("p = {x: 1, y: 2} q = {...p, x: 10} q.x + q.y"), "12");
    assert_eq!(run("p = {x: 1, y: 2} q = {...p, x: \"one\"} q.x"), "one");
    assert_eq!(run("p = {x: 1, y: 2} q = {...p, x: true} q.y"), "2");
    assert_eq!(run("p = {x: 1} {...p}.x"), "1");
}

#[test]
fn spread_in_a_function_over_records_of_different_shapes() {
    let src = "bump = program(m) do {...m, x: m.x + 1} done \
               a = bump({x: 1, y: 10}) \
               b = bump(bump({x: 5, z: true})) \
               a.x + a.y + b.x";
    assert_eq!(run(src), "19");
}

#[test]
fn spread_shadowing_a_field_hidden_behind_a_row_variable_frees_it() {
    let src = "retag = program(m) do {...m, x: 1} done \
               r = retag({x: \"hidden\", y: \"kept\"}) \
               r.y";
    assert_eq!(run(src), "kept");
    let numbers = "retag = program(m) do {...m, x: true} done \
                   r = retag({x: 1, y: 2}) \
                   if r.x then r.y else 0 done";
    assert_eq!(run(numbers), "2");
}

#[test]
fn spread_copies_heap_fields_and_the_original_survives() {
    let src = "p = {name: \"goat\", tags: {a: 1}, n: 1} \
               q = {...p, n: 2} \
               r = {...q, name: \"kid\"} \
               p.name";
    assert_eq!(run(src), "goat");
    let both = "p = {name: \"goat\", n: 1} q = {...p, n: 2} q.name";
    assert_eq!(run(both), "goat");
    let nested = "p = {inner: {v: 1}, n: 1} q = {...p, n: 2} q.inner.v + p.n + q.n";
    assert_eq!(run(nested), "4");
}

#[test]
fn spread_of_a_call_and_of_a_captured_record() {
    let src = "mk = program(n) do {x: n, y: n * 2} done \
               q = {...mk(3), x: 0} \
               q.x + q.y";
    assert_eq!(run(src), "6");
    let closure = "p = {x: 2} f = program(k) do {...p, x: p.x + k} done f(5).x + f(1).x";
    assert_eq!(run(closure), "10");
}

#[test]
fn spread_update_in_a_loop() {
    let src = "step = program(s) do {...s, n: s.n - 1, acc: s.acc + s.n} done \
               go = program(s) do if s.n < 1 then s.acc else go(step(s)) done done \
               go({n: 100, acc: 0, label: \"sum\"})";
    assert_eq!(run(src), "5050");
}

#[test]
fn destructuring_binds_fields() {
    assert_eq!(
        run("point = {x: 3, y: 4} {x, y} = point x * x + y * y"),
        "25"
    );
    assert_eq!(run("{x, y} = {x: 3, y: 4, z: 5} x + y"), "7");
    assert_eq!(run("{name} = {name: \"goat\", age: 3} name"), "goat");
    assert_eq!(run("{x} = {x: 1} {x} = {x: x + 1} x"), "2");
}

#[test]
fn destructuring_parameters() {
    let norm = "norm = program({x, y}) do x * x + y * y done norm({y: 4, x: 3})";
    assert_eq!(run(norm), "25");
    let mixed = "f = program(a, {x, y}, b) do a + x * y + b done f(1, {x: 2, y: 3, z: 0}, 4)";
    assert_eq!(run(mixed), "11");
    let closure = "add = program({x}) do program({y}) do x + y done done add({x: 1})({y: 2})";
    assert_eq!(run(closure), "3");
    let strings = "first = program({name}) do name done first({name: \"goat\", n: 1})";
    assert_eq!(run(strings), "goat");
}

#[test]
fn rest_binds_the_record_without_the_named_fields() {
    assert_eq!(
        run("{x, ...rest} = {x: 1, y: 2, z: 3} rest.y + rest.z"),
        "5"
    );
    assert_eq!(run("{x, y, ...rest} = {x: 1, y: 2, z: 3} rest.z"), "3");
    assert_eq!(run("{...rest} = {x: 1} rest.x"), "1");
    let heap = "{id, ...rest} = {id: \"a\", name: \"goat\", pals: {n: 1}} rest.name";
    assert_eq!(run(heap), "goat");
    let param = "drop = program({x, ...r}) do r done \
                 a = drop({x: 1, y: 7}) \
                 b = drop({x: true, y: 8, z: 9}) \
                 a.y + b.y + b.z";
    assert_eq!(run(param), "24");
    let unused = "{x, ...rest} = {x: \"gone\", y: \"kept\"} x";
    assert_eq!(run(unused), "gone");
}

#[test]
fn rest_and_spread_round_trip() {
    let src = "{x, ...rest} = {x: 1, y: 2} back = {...rest, x: 10} back.x + back.y";
    assert_eq!(run(src), "12");
}

#[test]
fn spread_and_destructuring_beside_variants() {
    let src = "area = program({shape, scale}) do \
                 match shape do Circle(r) then r * r * scale Square(w) then w * w * scale done done \
               cfg = {shape: Circle(2), scale: 3} \
               big = {...cfg, shape: Square(5)} \
               area(cfg) + area(big)";
    assert_eq!(run(src), "87");
    let positional = "{tag, ...r} = {tag: Link(1, Empty), n: 2} \
                      match tag do Link(a, rest) then a + r.n done";
    assert_eq!(run(positional), "3");
}

const SUM: &str = "sum = program(xs) do match xs do [] then 0 \
                   [first, ...rest] then first + sum(rest) done done ";

#[test]
fn list_literals_build_lists() {
    assert_eq!(run(&format!("{SUM} sum([])")), "0");
    assert_eq!(run(&format!("{SUM} sum([7])")), "7");
    assert_eq!(run(&format!("{SUM} sum([1, 2, 3, 4, 5])")), "15");
    assert_eq!(run(&format!("{SUM} sum([1, 2, 3,])")), "6");
    assert_eq!(run(&format!("{SUM} n = 4 sum([n, n * 2, n + 1])")), "17");
}

#[test]
fn list_literals_are_the_link_and_empty_tags() {
    let src = format!("{LENGTH} length([1, 2, 3]) + length(Link(1, Link(2, [])))");
    assert_eq!(run(&src), "5");
    assert_eq!(run(&format!("{SUM} sum(Link(1, [2, 3]))")), "6");
}

#[test]
fn nested_and_heap_lists_drop_cleanly() {
    let total = "total = program(xss) do match xss do [] then 0 \
                 [xs, ...more] then sum(xs) + total(more) done done ";
    assert_eq!(
        run(&format!("{SUM} {total} total([[1, 2], [], [3, 4, 5]])")),
        "15"
    );
    let words = "len = program(xs) do match xs do [] then 0 \
                 [w, ...more] then 1 + len(more) done done \
                 len([\"a\", \"b\", \"c\"])";
    assert_eq!(run(words), "3");
}

#[test]
fn fixed_length_list_patterns() {
    let src = "f = program(xs) do match xs do \
                 [a, b] then a * 100 + b \
                 [a] then a \
                 [] then 0 \
                 [a, ...rest] then 7 \
               done done \
               f([1, 2]) + f([5]) + f([]) + f([1, 2, 3])";
    assert_eq!(run(src), "114");
}

#[test]
fn a_list_pattern_with_an_else() {
    let src = "f = program(xs) do match xs do [a, b] then a + b else 0 done done \
               f([1, 2]) + f([1]) + f([1, 2, 3]) + f([])";
    assert_eq!(run(src), "3");
}

#[test]
fn a_rest_pattern_alone_matches_anything() {
    let src = format!(
        "{LENGTH} f = program(xs) do match xs do [] then 0 [...all] then length(all) done done \
         f([4, 5, 6]) + f([])"
    );
    assert_eq!(run(&src), "3");
}

#[test]
fn a_list_pattern_matches_a_computed_scrutinee() {
    let src = format!("{SUM} match [1, 2, 3] do [] then 0 [a, ...rest] then a + sum(rest) done");
    assert_eq!(run(&src), "6");
}

#[test]
fn list_destructuring_and_parameters() {
    assert_eq!(run("[a, b] = [3, 4] a * b"), "12");
    assert_eq!(run("[first, ...rest] = [3, 4, 5] first"), "3");
    let rest = format!("{SUM} [first, ...rest] = [3, 4, 5] sum(rest)");
    assert_eq!(run(&rest), "9");
    assert_eq!(
        run("second = program([a, b]) do b done second([8, 9])"),
        "9"
    );
    let two = "add = program([a, b], [c, ...rest]) do a + b + c done add([1, 2], [10, 20])";
    assert_eq!(run(two), "13");
}

#[test]
fn list_patterns_close_over_their_bindings() {
    let src = "adder = program(xs) do match xs do \
                 [n, ...rest] then program(k) do n + k done \
                 [] then program(k) do k done \
               done done \
               adder([10, 20])(5) + adder([])(1)";
    assert_eq!(run(src), "16");
}
