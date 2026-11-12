//! `<`, `<=`, `>` and `>=` on more than numbers (ADR 0036): every program runs
//! through the interpreter and through wasm under wasmtime, which must print
//! the same lines and leave no heap object live.

#[allow(dead_code)]
mod support;

use support::run;

/// A list of `1..=n` built in constant stack.
const BUILD: &str = "build = program(n, acc) do \
                       if n < 1 then acc else build(n - 1, Link(n, acc)) done \
                     done ";

/// All four operators on `a` and `b`, as `lt le gt ge`.
fn all(a: &str, b: &str) -> String {
    ["<", "<=", ">", ">="]
        .iter()
        .map(|op| run(&format!("{a} {op} {b}")))
        .collect::<Vec<_>>()
        .join(" ")
}

#[test]
fn numbers_keep_their_semantics() {
    assert_eq!(all("1", "2"), "true true false false");
    assert_eq!(all("2", "2"), "false true false true");
    assert_eq!(all("3", "2"), "false false true true");
    assert_eq!(all("1", "1.5"), "true true false false");
    assert_eq!(all("-1.5", "-2"), "false false true true");
}

#[test]
fn strings_order_by_code_point() {
    assert_eq!(all("\"apple\"", "\"banana\""), "true true false false");
    assert_eq!(all("\"same\"", "\"same\""), "false true false true");
    assert_eq!(all("\"b\"", "\"a\""), "false false true true");
    assert_eq!(all("\"\"", "\"a\""), "true true false false");
    assert_eq!(all("\"\"", "\"\""), "false true false true");
    assert_eq!(all("\"ab\"", "\"abc\""), "true true false false");
    assert_eq!(all("\"abc\"", "\"ab\""), "false false true true");
    assert_eq!(all("\"Z\"", "\"a\""), "true true false false");
    assert_eq!(all("\"z\"", "\"é\""), "true true false false");
    assert_eq!(all("\"é\"", "\"€\""), "true true false false");
    assert_eq!(all("\"€\"", "\"🐐\""), "true true false false");
}

#[test]
fn bools_put_false_first() {
    assert_eq!(all("false", "true"), "true true false false");
    assert_eq!(all("true", "false"), "false false true true");
    assert_eq!(all("true", "true"), "false true false true");
    assert_eq!(all("false", "false"), "false true false true");
}

#[test]
fn records_order_field_by_field_in_label_order() {
    assert_eq!(all("{x: 1, y: 2}", "{x: 1, y: 3}"), "true true false false");
    assert_eq!(all("{x: 1, y: 9}", "{x: 2, y: 0}"), "true true false false");
    assert_eq!(all("{x: 1, y: 2}", "{x: 1, y: 2}"), "false true false true");
    assert_eq!(all("{y: 2, x: 1}", "{x: 1, y: 1}"), "false false true true");
    assert_eq!(
        all("{a: \"x\", b: 1}", "{a: \"x\", b: 2}"),
        "true true false false"
    );
    assert_eq!(
        all("{a: {b: 1}, c: 2}", "{a: {b: 1}, c: 1}"),
        "false false true true"
    );
    assert_eq!(all("{}", "{}"), "false true false true");
    assert_eq!(
        all("{ok: false, n: 5}", "{ok: true, n: 1}"),
        "false false true true"
    );
}

#[test]
fn tags_order_by_declaration_then_payload() {
    let tags = "tag Circle tag Square tag Dot \
                pick = program(n) do \
                  if n == 1 then Circle(5) else if n == 2 then Circle(7) else \
                  if n == 3 then Square(1) else Dot done done done \
                done ";
    let cmp = |a: u32, b: u32, op: &str| run(&format!("{tags} pick({a}) {op} pick({b})"));
    assert_eq!(cmp(1, 2, "<"), "true");
    assert_eq!(cmp(2, 1, "<"), "false");
    assert_eq!(cmp(1, 1, "<="), "true");
    assert_eq!(cmp(1, 1, "<"), "false");
    assert_eq!(cmp(1, 3, "<"), "true");
    assert_eq!(cmp(3, 1, ">"), "true");
    assert_eq!(cmp(4, 1, ">"), "true");
    assert_eq!(cmp(3, 4, "<"), "true");
    assert_eq!(cmp(3, 4, ">="), "false");
    assert_eq!(cmp(4, 4, ">="), "true");
    assert_eq!(cmp(4, 4, ">"), "false");
}

#[test]
fn a_group_orders_left_to_right() {
    let level = "tag Level = Low | Medium | High ";
    for (a, b) in [("Low", "Medium"), ("Medium", "High"), ("Low", "High")] {
        assert_eq!(run(&format!("{level} {a} < {b}")), "true", "{a} < {b}");
        assert_eq!(run(&format!("{level} {b} > {a}")), "true", "{b} > {a}");
        assert_eq!(run(&format!("{level} {b} < {a}")), "false", "{b} < {a}");
        assert_eq!(run(&format!("{level} {a} >= {b}")), "false", "{a} >= {b}");
    }
    assert_eq!(run(&format!("{level} Medium <= Medium")), "true");
    assert_eq!(run(&format!("{level} Medium < Medium")), "false");
    assert_eq!(
        run(&format!("{level} print(sort([High, Low, Medium]))")),
        "[Low, Medium, High]"
    );
    assert_eq!(
        run(&format!("{level} print(biggest([Medium, High, Low]))")),
        "High"
    );
    assert_eq!(
        run(&format!("{level} print(smallest([Medium, High, Low]))")),
        "Low"
    );
}

#[test]
fn a_group_with_payloads_orders_by_position_then_payload() {
    let size = "tag Size = Tiny | Some(Number) | Huge(Number) ";
    assert_eq!(run(&format!("{size} Some(1) < Some(2)")), "true");
    assert_eq!(run(&format!("{size} Some(2) < Some(1)")), "false");
    assert_eq!(run(&format!("{size} Some(9) < Huge(1)")), "true");
    assert_eq!(run(&format!("{size} Tiny < Some(0)")), "true");
    assert_eq!(run(&format!("{size} Huge(1) > Tiny")), "true");
}

#[test]
fn one_key_tag_outside_an_interactive_program_numbers_its_whole_group() {
    assert_eq!(run("print(Up)"), "Up");
    assert_eq!(run("Up < Down"), "true");
    assert_eq!(run("Right > Left"), "true");
}

#[test]
fn individually_declared_tags_order_by_first_appearance() {
    let src = "tag Zebra tag Apple tag Mango ";
    assert_eq!(run(&format!("{src} Zebra < Apple")), "true");
    assert_eq!(run(&format!("{src} Apple < Mango")), "true");
    assert_eq!(run(&format!("{src} Mango > Zebra")), "true");
}

#[test]
fn a_group_after_other_tags_keeps_its_own_order() {
    let src = "tag Zebra tag Apple tag Rank = Beta | Alpha ";
    assert_eq!(run(&format!("{src} Beta < Alpha")), "true");
    assert_eq!(run(&format!("{src} Zebra < Apple")), "true");
}

#[test]
fn list_tags_stay_empty_before_link_whatever_the_program_declares() {
    let src = "tag Aaa tag Zzz ";
    assert_eq!(run(&format!("{src} [] < [0]")), "true");
    assert_eq!(run(&format!("{src} [1, 2] < [1, 3]")), "true");
    assert_eq!(run(&format!("{src} [5] > []")), "true");
}

#[test]
fn tags_with_several_arguments_compare_left_to_right() {
    let src = "tag Pair Pair(1, \"b\") < Pair(1, \"c\")";
    assert_eq!(run(src), "true");
    assert_eq!(run("tag Pair Pair(2, \"a\") < Pair(1, \"c\")"), "false");
    assert_eq!(run("tag Pair Pair(1, \"a\") >= Pair(1, \"a\")"), "true");
}

#[test]
fn lists_order_lexicographically() {
    assert_eq!(all("[1, 2, 3]", "[1, 2, 4]"), "true true false false");
    assert_eq!(all("[1, 2]", "[1, 2, 3]"), "true true false false");
    assert_eq!(all("[2]", "[1, 2, 3]"), "false false true true");
    assert_eq!(all("[1, 2]", "[1, 2]"), "false true false true");
    assert_eq!(all("[]", "[1]"), "true true false false");
    assert_eq!(all("[]", "[]"), "false true false true");
    assert_eq!(
        all("[\"a\", \"b\"]", "[\"a\", \"c\"]"),
        "true true false false"
    );
    assert_eq!(
        all("[[1], [2, 3]]", "[[1], [2, 4]]"),
        "true true false false"
    );
    assert_eq!(all("[{x: 1}]", "[{x: 2}]"), "true true false false");
}

#[test]
fn ordering_long_lists_uses_constant_stack() {
    let src = format!("{BUILD} build(50000, []) < build(50001, [])");
    assert_eq!(run(&src), "true");
    let src = format!("{BUILD} build(50000, []) >= build(50000, [])");
    assert_eq!(run(&src), "true");
}

#[test]
fn ordering_long_strings_walks_every_byte() {
    let (long, longer) = ("a".repeat(5000), "a".repeat(5001));
    assert_eq!(run(&format!("\"{long}\" < \"{longer}\"")), "true");
    assert_eq!(run(&format!("\"{long}b\" > \"{longer}\"")), "true");
    assert_eq!(run(&format!("\"{long}\" >= \"{long}\"")), "true");
}

#[test]
fn ordering_trees() {
    let tree = "tag Leaf tag Node leaf = Leaf \
                node = program(l, v, r) do Node(l, v, r) done ";
    let src = format!(
        "{tree} a = node(node(leaf, 1, leaf), 2, node(leaf, 3, leaf)) \
         b = node(node(leaf, 1, leaf), 2, node(leaf, 4, leaf)) a < b"
    );
    assert_eq!(run(&src), "true");
    let src =
        format!("{tree} a = node(leaf, 2, leaf) b = node(node(leaf, 1, leaf), 2, leaf) a < b");
    assert_eq!(run(&src), "true");
}

#[test]
fn ordering_inside_a_polymorphic_function() {
    let src = "less = program(a, b) do a < b done \
               n = less(1, 2) s = less(\"y\", \"x\") r = less({p: 1}, {p: 2}) l = less([2], [1]) \
               if n then if s then 0 else if r then if l then 1 else 2 done else 3 done done else 4 done";
    assert_eq!(run(src), "2");
}

#[test]
fn floats_inside_records_order_by_value() {
    assert_eq!(
        all("{x: 1.5, y: 2}", "{x: 1.5, y: 3}"),
        "true true false false"
    );
    assert_eq!(all("{x: 2.5}", "{x: 1.5}"), "false false true true");
    assert_eq!(all("[0.5, 1.5]", "[0.5, 1.5]"), "false true false true");
}

#[test]
fn the_prelude_sorts_anything_ordered() {
    assert_eq!(
        run("print(sort([\"pear\", \"apple\", \"fig\"]))"),
        "[\"apple\", \"fig\", \"pear\"]"
    );
    assert_eq!(
        run("print(sort([{x: 2, y: 1}, {x: 1, y: 9}, {x: 1, y: 3}]))"),
        "[{x: 1, y: 3}, {x: 1, y: 9}, {x: 2, y: 1}]"
    );
    assert_eq!(
        run("print(sort([[2, 1], [1, 5, 5], [1]]))"),
        "[[1], [1, 5, 5], [2, 1]]"
    );
    assert_eq!(run("print(biggest([\"b\", \"c\", \"a\"]))"), "c");
    assert_eq!(run("print(smallest([\"b\", \"c\", \"a\"]))"), "a");
    assert_eq!(
        run("print(insert_sorted(\"b\", [\"a\", \"c\"], []))"),
        "[\"a\", \"b\", \"c\"]"
    );
    assert_eq!(run("print(sort([3, 1, 2]))"), "[1, 2, 3]");
}
