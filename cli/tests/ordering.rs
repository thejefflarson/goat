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

/// `all`, with `defs` (tag declarations) ahead of the comparison.
fn all_in(defs: &str, a: &str, b: &str) -> String {
    ["<", "<=", ">", ">="]
        .iter()
        .map(|op| run(&format!("{defs}{a} {op} {b}")))
        .collect::<Vec<_>>()
        .join(" ")
}

/// The booleans `a < b`, `a <= b`, `a > b`, `a >= b`, from one program.
fn verdicts(a: &str, b: &str) -> Vec<bool> {
    let tests = ["<", "<=", ">", ">="].map(|op| format!("{a} {op} {b}"));
    let printed = run(&format!("print([{}])", tests.join(", ")));
    printed
        .trim_matches(['[', ']'])
        .split(", ")
        .map(|word| word == "true")
        .collect()
}

const NAN: &str = "(0.0 / 0.0)";

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
    let tags = "tag Shape = Ring(_) | Square(_) | Dot \
                pick = program(n) do \
                  if n == 1 then Ring(5) else if n == 2 then Ring(7) else \
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
fn a_group_orders_by_declaration_not_by_name() {
    let src = "tag Fruit = Zebra | Apple | Mango ";
    assert_eq!(run(&format!("{src} Zebra < Apple")), "true");
    assert_eq!(run(&format!("{src} Apple < Mango")), "true");
    assert_eq!(run(&format!("{src} Mango > Zebra")), "true");
}

#[test]
fn a_group_after_other_tags_keeps_its_own_order() {
    let src = "tag Zebra tag Apple tag Rank = Beta | Alpha ";
    assert_eq!(run(&format!("{src} Beta < Alpha")), "true");
    assert_eq!(run(&format!("{src} Zebra == Zebra")), "true");
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
    let src = "tag Pair(_) Pair(1, \"b\") < Pair(1, \"c\")";
    assert_eq!(run(src), "true");
    assert_eq!(run("tag Pair(_) Pair(2, \"a\") < Pair(1, \"c\")"), "false");
    assert_eq!(run("tag Pair(_) Pair(1, \"a\") >= Pair(1, \"a\")"), "true");
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
    let tree = "tag Tree = Leaf | Node(_) leaf = Leaf \
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

#[test]
fn a_nan_inside_a_compound_is_after_every_float_and_equal_to_itself() {
    let nan = |shape: &str| shape.replace('N', NAN);
    let table = [
        ("{x: N}", "{x: 0.0}", "false false true true"),
        ("{x: 0.0}", "{x: N}", "true true false false"),
        ("{x: N}", "{x: N}", "false true false true"),
        ("{x: N}", "{x: 1.0 / 0.0}", "false false true true"),
        ("{x: 1.0 / 0.0}", "{x: N}", "true true false false"),
        ("{x: N, y: 1}", "{x: N, y: 2}", "true true false false"),
        ("{x: 1, y: N}", "{x: 2, y: 0.0}", "true true false false"),
        ("[1.0, N]", "[1.0, 5.0]", "false false true true"),
        ("[1.0, 5.0]", "[1.0, N]", "true true false false"),
        ("[N]", "[N, 0.0]", "true true false false"),
        ("[N]", "[N]", "false true false true"),
    ];
    for (a, b, want) in table {
        assert_eq!(all(&nan(a), &nan(b)), want, "{a} vs {b}");
    }
}

#[test]
fn a_nan_inside_a_tag_orders_like_one_inside_a_record() {
    let defs = "tag Box(_) tag Pair(_) ";
    let nan = |shape: &str| shape.replace('N', NAN);
    let table = [
        ("Box(N)", "Box(0.0)", "false false true true"),
        ("Box(0.0)", "Box(N)", "true true false false"),
        ("Pair(N, 1)", "Pair(N, 2)", "true true false false"),
    ];
    for (a, b, want) in table {
        assert_eq!(all_in(defs, &nan(a), &nan(b)), want, "{a} vs {b}");
    }
}

#[test]
fn a_nan_deep_in_a_recursive_type_orders_consistently() {
    let defs = "tag Tree = Leaf | Node(_) ";
    let node = |v: &str| format!("Node(Leaf, {v}, Leaf)");
    assert_eq!(
        all_in(defs, &node(NAN), &node("0.0")),
        "false false true true"
    );
    assert_eq!(
        all_in(defs, &node("0.0"), &node(NAN)),
        "true true false false"
    );
    assert_eq!(
        all_in(defs, &node(NAN), &node(NAN)),
        "false true false true"
    );
}

#[test]
fn bare_float_operators_stay_ieee() {
    assert_eq!(all(NAN, "0.0"), "false false false false");
    assert_eq!(all("0.0", NAN), "false false false false");
    assert_eq!(all(NAN, NAN), "false false false false");
}

#[test]
fn sort_places_nan_records_last_and_breaks_ties_on_later_fields() {
    let src = format!(
        "print(sort([{{x: {NAN}, y: 2}}, {{x: 3.0, y: 0}}, {{x: {NAN}, y: 1}}, {{x: 1.0, y: 9}}]))"
    );
    assert_eq!(
        run(&src),
        "[{x: 1, y: 9}, {x: 3, y: 0}, {x: nan, y: 1}, {x: nan, y: 2}]"
    );
    let src = format!("print(sort([[{NAN}], [2.0], [{NAN}, 0.0], [1.0]]))");
    assert_eq!(run(&src), "[[1], [2], [nan], [nan, 0]]");
}

#[test]
fn the_derived_order_is_antisymmetric_and_total_over_nan_shapes() {
    let leaves = [NAN, "0.0", "-2.5", "1.0 / 0.0"];
    let mut records = Vec::new();
    let mut lists = Vec::new();
    for a in leaves {
        lists.push(format!("[{a}, 1.0]"));
        for b in &leaves[..2] {
            records.push(format!("{{x: {a}, y: {b}}}"));
        }
    }
    for group in [records, lists] {
        for (i, a) in group.iter().enumerate() {
            for b in &group[i..] {
                let (ab, ba) = (verdicts(a, b), verdicts(b, a));
                assert_eq!(ab[0], ba[2], "{a} < {b} must match {b} > {a}");
                assert_eq!(ab[2], ba[0], "{a} > {b} must match {b} < {a}");
                assert!(
                    !(ab[0] && ab[2]),
                    "{a} and {b} are each bigger than the other"
                );
                assert_eq!(ab[1], !ab[2], "{a} <= {b}");
                assert_eq!(ab[3], !ab[0], "{a} >= {b}");
            }
        }
    }
}
