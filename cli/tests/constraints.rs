//! `==`, field-wise arithmetic on records, and `print`: every program runs
//! through the interpreter and through wasm under wasmtime, which must print
//! the same lines and leave no heap object live. The MIR verifier runs on
//! every program too (see `support::interpret`).

#[allow(dead_code)]
mod support;

use support::run;

/// A list of `1..=n` built in constant stack.
const BUILD: &str = "build = program(n, acc) do \
                       if n < 1 then acc else build(n - 1, Link(n, acc)) done \
                     done ";

#[test]
fn equality_on_scalars() {
    assert_eq!(run("1 == 1"), "true");
    assert_eq!(run("1 == 2"), "false");
    assert_eq!(run("1 != 2"), "true");
    assert_eq!(run("1 != 1"), "false");
    assert_eq!(run("true == true"), "true");
    assert_eq!(run("true == false"), "false");
    assert_eq!(run("false == false"), "true");
    assert_eq!(run("false != true"), "true");
    assert_eq!(run("1 + 1 == 2"), "true");
    assert_eq!(run("1 < 2 == true"), "true");
}

#[test]
fn equality_on_strings_compares_bytes() {
    assert_eq!(run("\"abc\" == \"abc\""), "true");
    assert_eq!(run("\"abc\" == \"abd\""), "false");
    assert_eq!(run("\"abc\" == \"ab\""), "false");
    assert_eq!(run("\"\" == \"\""), "true");
    assert_eq!(run("\"abc\" != \"abd\""), "true");
    assert_eq!(run("s = \"hello\"  s == s"), "true");
}

#[test]
fn equality_on_records() {
    assert_eq!(run("{x: 1, y: 2} == {x: 1, y: 2}"), "true");
    assert_eq!(run("{x: 1, y: 2} == {x: 1, y: 3}"), "false");
    assert_eq!(run("{y: 2, x: 1} == {x: 1, y: 2}"), "true");
    assert_eq!(
        run("{a: {b: 1}, c: \"s\"} == {a: {b: 1}, c: \"s\"}"),
        "true"
    );
    assert_eq!(
        run("{a: {b: 1}, c: \"s\"} == {a: {b: 2}, c: \"s\"}"),
        "false"
    );
    assert_eq!(
        run("{a: {b: 1}, c: \"s\"} != {a: {b: 1}, c: \"t\"}"),
        "true"
    );
    assert_eq!(run("{ok: true, n: 1} == {ok: false, n: 1}"), "false");
    assert_eq!(run("{} == {}"), "true");
}

#[test]
fn equality_on_variants() {
    assert_eq!(run("tag Circle Circle(1) == Circle(1)"), "true");
    assert_eq!(run("tag Circle Circle(1) == Circle(2)"), "false");
    assert_eq!(
        run(
            "tag Circle tag Square a = if 1 < 2 then Circle(1) else Square(1) done  a == Circle(1)"
        ),
        "true"
    );
    assert_eq!(
        run(
            "tag Circle tag Square a = if 1 < 2 then Circle(1) else Square(1) done  a == Square(1)"
        ),
        "false"
    );
    assert_eq!(run("tag Pair Pair(1, \"a\") == Pair(1, \"a\")"), "true");
    assert_eq!(run("tag Pair Pair(1, \"a\") == Pair(1, \"b\")"), "false");
    assert_eq!(run("tag Pair Pair(1, \"a\") != Pair(2, \"a\")"), "true");
    assert_eq!(run("tag Wrap Wrap({x: 1}) == Wrap({x: 1})"), "true");
    let src = "tag None tag Some a = if 1 < 2 then None else Some(1) done  b = if 2 < 1 then None else Some(1) done \
               a == b";
    assert_eq!(run(src), "false");
}

#[test]
fn equality_on_lists() {
    assert_eq!(run("[1, 2, 3] == [1, 2, 3]"), "true");
    assert_eq!(run("[1, 2, 3] == [1, 2, 4]"), "false");
    assert_eq!(run("[1, 2, 3] == [1, 2]"), "false");
    assert_eq!(run("[1, 2] == [1, 2, 3]"), "false");
    assert_eq!(run("[] == []"), "true");
    assert_eq!(run("[\"a\", \"b\"] == [\"a\", \"b\"]"), "true");
    assert_eq!(run("[{x: 1}, {x: 2}] == [{x: 1}, {x: 2}]"), "true");
    assert_eq!(run("[[1], [2, 3]] == [[1], [2, 3]]"), "true");
    assert_eq!(run("[[1], [2, 3]] != [[1], [2, 4]]"), "true");
}

#[test]
fn equality_on_long_lists_uses_constant_stack() {
    let src = format!("{BUILD} build(50000, []) == build(50000, [])");
    assert_eq!(run(&src), "true");
    let src = format!("{BUILD} build(50000, []) == build(49999, [])");
    assert_eq!(run(&src), "false");
}

#[test]
fn equality_on_trees() {
    let tree = "tag Leaf tag Node leaf = Leaf \
                node = program(l, v, r) do Node(l, v, r) done ";
    let src = format!(
        "{tree} a = node(node(leaf, 1, leaf), 2, node(leaf, 3, leaf)) \
         b = node(node(leaf, 1, leaf), 2, node(leaf, 3, leaf)) a == b"
    );
    assert_eq!(run(&src), "true");
    let src = format!(
        "{tree} a = node(node(leaf, 1, leaf), 2, node(leaf, 3, leaf)) \
         b = node(node(leaf, 1, leaf), 2, node(leaf, 4, leaf)) a == b"
    );
    assert_eq!(run(&src), "false");
}

#[test]
fn equality_inside_a_polymorphic_function() {
    let src = "same = program(a, b) do a == b done \
               n = same(1, 1) s = same(\"x\", \"y\") r = same({p: 1}, {p: 1}) l = same([1], [2]) \
               if n then if s then 0 else if r then if l then 1 else 2 done else 3 done done else 4 done";
    assert_eq!(run(src), "2");
}

#[test]
fn has_by_equality() {
    let src = "has = program(xs, x) do \
                 match xs do \
                   Empty then false \
                   Link(first, rest) then if first == x then true else has(rest, x) done \
                 done \
               done \
               has([1, 2, 3], 3)";
    assert_eq!(run(src), "true");
    let src = "has = program(xs, x) do \
                 match xs do \
                   Empty then false \
                   Link(first, rest) then if first == x then true else has(rest, x) done \
                 done \
               done \
               has([\"a\", \"b\"], \"c\")";
    assert_eq!(run(src), "false");
}

#[test]
fn record_arithmetic_is_field_wise() {
    assert_eq!(run("print({x: 1, y: 2} + {x: 3, y: 4})"), "{x: 4, y: 6}");
    assert_eq!(run("print({x: 5, y: 7} - {x: 3, y: 4})"), "{x: 2, y: 3}");
    assert_eq!(run("print({x: 5, y: 7} * {x: 3, y: 2})"), "{x: 15, y: 14}");
    assert_eq!(run("print({x: 9, y: 8} / {x: 3, y: 2})"), "{x: 3, y: 4}");
    assert_eq!(
        run("print({p: {x: 1, y: 2}, n: 3} + {p: {x: 10, y: 20}, n: 30})"),
        "{n: 33, p: {x: 11, y: 22}}"
    );
    assert_eq!(run("p = {x: 1, y: 2}  q = p + p  q.x + q.y"), "6");
    assert_eq!(run("{x: 1, y: 2} + {x: 3, y: 4} == {x: 4, y: 6}"), "true");
}

#[test]
fn arithmetic_in_a_polymorphic_function_works_at_every_numeric_type() {
    let src = "add = program(a, b) do a + b done \
               a = print(add(1, 2)) \
               b = print(add({x: 1}, {x: 2})) 0";
    assert_eq!(run(src), "3\n{x: 3}\n0");
}

#[test]
fn record_arithmetic_through_a_function_and_a_spread() {
    let src = "move = program(p, d) do p + d done \
               start = {x: 1, y: 1, name: \"a\"} \
               print(move({x: start.x, y: start.y}, {x: 2, y: 3}))";
    assert_eq!(run(src), "{x: 3, y: 4}");
    let src = "scale = program(p, k) do p * {x: k, y: k} done  print(scale({x: 2, y: 3}, 10))";
    assert_eq!(run(src), "{x: 20, y: 30}");
}

#[test]
fn plain_number_arithmetic_is_unchanged() {
    assert_eq!(run("1 + 2 * 3 - 4 / 8"), "6.5");
    assert_eq!(run("add = program(a, b) do a + b done  add(20, 22)"), "42");
    assert_eq!(
        run("fib = program(n) do if n < 2 then n else fib(n - 1) + fib(n - 2) done done fib(10)"),
        "55"
    );
}

#[test]
fn print_scalars() {
    assert_eq!(run("print(42)"), "42");
    assert_eq!(run("print(2.5)"), "2.5");
    assert_eq!(run("print(true)"), "true");
    assert_eq!(run("print(false)"), "false");
    assert_eq!(run("print(\"hello\")"), "hello");
    assert_eq!(run("print(1 + 2)"), "3");
}

#[test]
fn print_runs_mid_program_in_order() {
    let src = "a = print(1)  b = print(\"two\")  c = print(true)  4";
    assert_eq!(run(src), "1\ntwo\ntrue\n4");
}

#[test]
fn print_returns_unit_and_runs_even_when_unused() {
    assert_eq!(run("ignored = print(7)  8"), "7\n8");
    let src = "twice = program(x) do a = print(x)  b = print(x)  x done  twice(3)";
    assert_eq!(run(src), "3\n3\n3");
}

#[test]
fn print_records() {
    assert_eq!(run("print({x: 1, y: 2})"), "{x: 1, y: 2}");
    assert_eq!(
        run("print({name: \"goat\", age: 3, ok: true})"),
        "{age: 3, name: \"goat\", ok: true}"
    );
    assert_eq!(run("print({a: {b: {c: 1}}})"), "{a: {b: {c: 1}}}");
    assert_eq!(run("print({})"), "{}");
}

#[test]
fn print_variants() {
    assert_eq!(run("tag Circle print(Circle(5))"), "Circle(5)");
    assert_eq!(run("print(Empty)"), "[]");
    assert_eq!(run("tag Pair print(Pair(1, \"a\"))"), "Pair(1, \"a\")");
    assert_eq!(run("tag Wrap print(Wrap({x: 1}))"), "Wrap({x: 1})");
    assert_eq!(run("tag Wrap print(Wrap(Wrap(1)))"), "Wrap(Wrap(1))");
    let src = "tag Circle tag Square s = if 1 < 2 then Circle(1) else Square(2) done  print(s)";
    assert_eq!(run(src), "Circle(1)");
    let src = "tag Circle tag Square s = if 2 < 1 then Circle(1) else Square(2) done  print(s)";
    assert_eq!(run(src), "Square(2)");
    assert_eq!(run("tag Done print(Done)"), "Done");
}

#[test]
fn print_lists() {
    assert_eq!(run("print([1, 2, 3])"), "[1, 2, 3]");
    assert_eq!(run("print([])"), "[]");
    assert_eq!(run("print([\"a\", \"b\"])"), "[\"a\", \"b\"]");
    assert_eq!(run("print([{x: 1}, {x: 2}])"), "[{x: 1}, {x: 2}]");
    assert_eq!(run("print([[1], [], [2, 3]])"), "[[1], [], [2, 3]]");
    assert_eq!(run("print({xs: [1, 2]})"), "{xs: [1, 2]}");
    assert_eq!(
        run("tag Wrap print(Wrap([true, false]))"),
        "Wrap([true, false])"
    );
}

#[test]
fn print_a_long_list_uses_constant_stack() {
    let src = format!("{BUILD} xs = build(2000, [])  a = print(xs == xs)  print(xs)");
    let printed = run(&src);
    let mut lines = printed.lines();
    assert_eq!(lines.next(), Some("true"));
    let list = lines.next().expect("the list line");
    assert!(list.starts_with("[1, 2, 3, "), "{list}");
    assert!(list.ends_with(", 1999, 2000]"), "{list}");
}

#[test]
fn print_a_tree() {
    let src = "tag Node tag Leaf t = Node(Node(Leaf, 1, Leaf), 2, Leaf)  print(t)";
    assert_eq!(run(src), "Node(Node(Leaf, 1, Leaf), 2, Leaf)");
}

#[test]
fn print_functions_and_units() {
    assert_eq!(run("print(program(x) do x done)"), "<function>");
    assert_eq!(run("print({f: program(x) do x done})"), "{f: <function>}");
    assert_eq!(run("print(print(1))"), "1\nUnit");
}

#[test]
fn print_as_a_value() {
    let src = "apply = program(f, x) do f(x) done  apply(print, 5)";
    assert_eq!(run(src), "5");
    let src = "apply = program(f, x) do f(x) done \
               a = apply(print, \"s\") b = apply(print, [1]) c = apply(print, {p: 1}) 0";
    assert_eq!(run(src), "s\n[1]\n{p: 1}\n0");
}

#[test]
fn print_inside_a_recursive_function() {
    let src = "count = program(n) do \
                 if n < 1 then 0 else a = print(n) count(n - 1) done \
               done \
               count(3)";
    assert_eq!(run(src), "3\n2\n1\n0");
}

#[test]
fn print_works_at_a_polymorphic_function_type() {
    let src = "show = program(x) do print(x) done \
               a = show(1) b = show(\"s\") c = show({k: [true]}) 0";
    assert_eq!(run(src), "1\ns\n{k: [true]}\n0");
}

#[test]
fn a_user_print_replaces_the_builtin() {
    assert_eq!(run("print = program(x) do x + 1 done  print(1)"), "2");
}

#[test]
fn string_literals_beyond_one_page_compile_and_run() {
    let big = "x".repeat(70_000);
    let src = format!("a = \"{big}\"  b = \"{big}y\"  a == b");
    assert_eq!(run(&src), "false");
    assert_eq!(run(&format!("\"{big}\" == \"{big}\"")), "true");
}
