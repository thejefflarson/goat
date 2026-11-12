//! What the grammar accepts, rejects and builds, one construct at a time.

use goat_parser::cst::Node;
use goat_parser::interp::parse;

fn accepts(source: &str) -> bool {
    parse(source).is_ok()
}

fn assert_accepts(sources: &[&str]) {
    for source in sources {
        assert!(accepts(source), "rejected: {source}");
    }
}

fn assert_rejects(sources: &[&str]) {
    for source in sources {
        assert!(!accepts(source), "accepted: {source}");
    }
}

/// The node kinds under `goat`, pre-order, each with its text when it has no
/// node children.
fn shape(source: &str) -> String {
    fn walk(node: Node) -> String {
        let inner: Vec<String> = node.children().map(walk).collect();
        if inner.is_empty() {
            format!("{}({:?})", node.kind(), node.text())
        } else {
            format!("{}[{}]", node.kind(), inner.join(" "))
        }
    }
    walk(
        parse(source)
            .unwrap_or_else(|e| panic!("{source}: {e}"))
            .root(),
    )
}

/// Every node kind in the tree, pre-order.
fn kinds(source: &str) -> Vec<String> {
    fn walk(node: Node, out: &mut Vec<String>) {
        out.push(node.kind().to_string());
        node.children().for_each(|c| walk(c, out));
    }
    let mut out = Vec::new();
    walk(parse(source).unwrap().root(), &mut out);
    out
}

fn contains_kind(source: &str, kind: &str) -> bool {
    kinds(source).iter().any(|k| k == kind)
}

/// Whether the bare word is a name rather than a keyword.
fn is_name(word: &str) -> bool {
    accepts(word) && shape(word) == format!("goat[expr[name({word:?})]]")
}

#[test]
fn the_empty_program_and_a_comment_parse_to_a_bare_goat_node() {
    assert_eq!(shape(""), "goat(\"\")");
    assert_eq!(shape("# comment"), "goat(\"# comment\")");
}

#[test]
fn the_tree_of_a_whole_program_is_pinned() {
    assert_eq!(
        shape(
            "tag Shape = Circle(Number) | Dot\n# c\nx = 1 + f(2).y;\nmatch x do 0 then 1 else 2 done"
        ),
        "goat[tag_decl[tag_kw(\"tag\") group_name[name(\"Shape\")] tag_case[name(\"Circle\") \
         type_name(\"Number\")] tag_case[name(\"Dot\")]] \
         expr[declaration[name(\"x\") value[number(\"1\") plus(\"+\") name(\"f\") \
         call[arguments[expr[number(\"2\")]]] access[name(\"y\")]]] \
         match_expr[expr[name(\"x\")] arm[literal_pattern[number(\"0\")] expr[number(\"1\")]] expr[number(\"2\")]]]]"
    );
}

#[test]
fn records_and_field_access() {
    assert_accepts(&[
        "{x: 1, y: 2}",
        "{}",
        "p.x",
        "p.x.y",
        "{a: {b: 1}}",
        "f(1).x",
        "{point: {x: 1, y: 2}}.point.x",
        "{x: 1,}",
    ]);
    assert_rejects(&["{,}", "{x:}", "p."]);
}

#[test]
fn a_take_is_a_postfix_beside_access_and_call() {
    assert_accepts(&[
        "r::f",
        "r::f(1)",
        "r::a::b(1)(2)",
        "r.a::f()",
        "r::a.b",
        "(r)::f",
    ]);
    assert_rejects(&["r::", "r:: f g", "::f", "r:f"]);
    assert_eq!(
        shape("r::f(1)"),
        "goat[expr[name(\"r\") take[name(\"f\")] call[arguments[expr[number(\"1\")]]]]]"
    );
}

#[test]
fn words_that_merely_begin_with_a_keyword_are_names() {
    for word in [
        "double",
        "doner",
        "ifx",
        "thenable",
        "truthy",
        "programmer",
        "functions",
        "tagline",
        "tags",
        "tag_",
        "matchbox",
        "nothing",
        "android",
        "order",
        "format",
        "forty",
        "nothing2",
        "circle",
        "Circle",
        "X",
        "Éclair",
        "éclair",
        "from",
        "to",
        "in",
        "foreign",
    ] {
        assert!(is_name(word), "{word} should be a name");
    }
    for word in [
        "do", "done", "if", "then", "program", "function", "fn", "match", "and", "or", "not",
        "for", "repeat", "times", "tag",
    ] {
        assert!(!accepts(word), "{word} should be reserved");
    }
}

#[test]
fn numbers_strings_and_booleans() {
    assert_eq!(shape("1.1"), "goat[expr[number(\"1.1\")]]");
    for number in ["1e3", "2.5E-2", "1e+9", ".5e1", ".5", "007", "0.5"] {
        assert_eq!(shape(number), format!("goat[expr[number({number:?})]]"));
    }
    assert_rejects(&["2e"]);
    assert_accepts(&[r#""hello""#, r#""""#]);
    assert!(contains_kind("true", "true_lit"));
    assert!(contains_kind("false", "false_lit"));
}

#[test]
fn division_is_one_operator_and_floor_division_another() {
    assert!(contains_kind("7 // 2", "floor_divide"));
    assert!(contains_kind("7 / 2", "divide"));
    assert!(contains_kind("7 % 2", "remainder"));
}

#[test]
fn a_number_has_no_sign() {
    assert_eq!(
        shape("5 -1"),
        "goat[expr[number(\"5\") minus(\"-\") number(\"1\")]]"
    );
    assert_eq!(
        shape("-3"),
        "goat[expr[negation[minus(\"-\") number(\"3\")]]]"
    );
    assert_accepts(&["-f(x).y", "--3"]);
}

#[test]
fn identifiers_take_letters_digits_underscores_and_unicode() {
    for name in ["a", "a_", "a9", "نامهای"] {
        assert!(is_name(name), "{name}");
    }
}

#[test]
fn bindings_are_siblings_and_an_operand_binding_scopes_over_the_rest() {
    assert!(contains_kind("a = b", "declaration"));
    assert_eq!(
        kinds("a = 1 b = 2; a")
            .iter()
            .filter(|k| *k == "declaration")
            .count(),
        2
    );
    assert!(contains_kind("1 + a = 2 a", "local"));
    assert_accepts(&["a = b = 1 b", "p; a = 1"]);
}

#[test]
fn a_chain_of_thousands_of_bindings_parses_on_the_default_stack() {
    let source: String = (0..4000).map(|i| format!("a{i} = {i}\n")).collect();
    assert!(accepts(&format!("{source}a0")));
}

#[test]
fn functions_and_calls() {
    for source in [
        "program(a) do a done",
        "function(a) do a done",
        "fn(a) do a done",
    ] {
        assert!(contains_kind(source, "function"), "{source}");
    }
    assert_eq!(
        shape("a(1, true, b, program(a) do a done)"),
        "goat[expr[name(\"a\") call[arguments[expr[number(\"1\")] expr[boolean[true_lit(\"true\")]] \
         expr[name(\"b\")] expr[function[params[name(\"a\")] expr[name(\"a\")]]]]]]]"
    );
    assert_eq!(shape("a()"), "goat[expr[name(\"a\") call(\"()\")]]");
    assert_eq!(
        kinds("s.f(1)(2)"),
        [
            "goat",
            "expr",
            "name",
            "access",
            "name",
            "call",
            "arguments",
            "expr",
            "number",
            "call",
            "arguments",
            "expr",
            "number"
        ]
    );
    assert_accepts(&["f(1,)", "f(1, 2,)"]);
    assert_rejects(&["f(,)"]);
}

#[test]
fn without_a_semicolon_a_paren_is_a_call_and_a_minus_is_subtraction() {
    assert_eq!(kinds("f(1) (2)").iter().filter(|k| *k == "call").count(), 2);
    assert!(contains_kind("f(1) -2", "minus"));
    assert_rejects(&["f(1) g(2)"]);
}

#[test]
fn a_parenthesized_expression_is_not_a_call() {
    assert_eq!(
        shape("(1 + 2) < 3"),
        "goat[expr[expr[number(\"1\") plus(\"+\") number(\"2\")] lt(\"<\") number(\"3\")]]"
    );
}

#[test]
fn a_semicolon_sequences_expressions() {
    assert_eq!(
        shape("a; b; c"),
        "goat[expr[name(\"a\") sequel(\";\") name(\"b\") sequel(\";\") name(\"c\")]]"
    );
    assert_accepts(&[
        "a;",
        "f(1); g(2);",
        "x = 1; x",
        "x = 1  f(x); g(x)",
        "{a} = r; a",
    ]);
    assert_rejects(&["a;;"]);
}

#[test]
fn foreign_declarations() {
    assert_accepts(&[
        r#"f = foreign "m" "f" (Number) -> Unit"#,
        r#"f = foreign "m" "f" () -> Bool"#,
        r#"f = foreign "m" "f" (Number, String,) -> Unit f(1, "a")"#,
        r#"f = foreign "m" "f" ({x: Number}) -> [Bool]"#,
        r#"f = foreign "m" "f" ((Number) -> Unit) -> Unit"#,
        r#"f = foreign m "f" (Number) -> Unit"#,
        "foreign = 1 foreign + 1",
    ]);
    assert_rejects(&[
        r#"f = foreign "m" "f" (Number)"#,
        r#"f = foreign "m" "f" Number -> Unit"#,
        r#"f = foreign "m" (Number) -> Unit"#,
    ]);
    assert_eq!(
        shape(r#"f = foreign "m" "g" (Number) -> Unit"#),
        "goat[expr[declaration[name(\"f\") foreign_decl[foreign_kw(\"foreign\") \
         foreign_name[string(\"\\\"m\\\"\")] foreign_name[string(\"\\\"g\\\"\")] \
         fn_type[type_name(\"Number\") type_name(\"Unit\")]]]]]"
    );
}

#[test]
fn list_literals_and_list_patterns() {
    assert_accepts(&["[]", "[1,]", "[[1], [], [2, 3]]", "[f(1), a + 1]", "[1].x"]);
    assert_rejects(&["[,]", "[1,,2]", "[1", "1]"]);
    assert_accepts(&[
        "[a] = xs a",
        "[a, b] = xs a",
        "[a, ...rest] = xs a",
        "[...rest] = xs rest",
        "[a, b,] = xs a",
        "[] = xs 1",
    ]);
    assert_rejects(&[
        "[...a, b] = xs a",
        "[a, ...b, ...c] = xs a",
        "[1] = xs 1",
        "[a b] = xs a",
    ]);
}

#[test]
fn a_bracket_is_a_pattern_only_where_a_pattern_goes() {
    assert!(contains_kind("[a, b] = xs a", "destructure"));
    assert!(contains_kind("[a, b]", "list"));
    assert!(!contains_kind("[a, b]", "destructure"));
    assert_accepts(&[
        "match xs do [] then 0 [a, ...r] then a done",
        "program([a, b], {x}, y) do a done",
        "[first, ...rest] = [1, 2, 3] first",
    ]);
}

#[test]
fn conditionals_and_math() {
    assert_eq!(
        shape("if true then 1 else 0 done"),
        "goat[expr[conditional[expr[boolean[true_lit(\"true\")]] expr[number(\"1\")] \
         expr[number(\"0\")]]]]"
    );
    assert_eq!(
        shape("1 + (3 - 5)"),
        "goat[expr[number(\"1\") plus(\"+\") expr[number(\"3\") minus(\"-\") number(\"5\")]]]"
    );
}

#[test]
fn operator_words_need_a_word_boundary() {
    assert_eq!(
        shape("not a and b or c"),
        "goat[expr[not_op(\"not\") name(\"a\") and_op(\"and\") name(\"b\") or_op(\"or\") \
         name(\"c\")]]"
    );
    assert_rejects(&["a andb"]);
    assert_accepts(&["a and(b)"]);
}

#[test]
fn tag_declarations_come_before_the_program() {
    assert_eq!(
        shape("tag Circle tag Square 1"),
        "goat[tag_decl[tag_kw(\"tag\") tag_case[name(\"Circle\")]] \
         tag_decl[tag_kw(\"tag\") tag_case[name(\"Square\")]] expr[number(\"1\")]]"
    );
    assert_accepts(&["tagCircle", "tag Circle"]);
    assert_rejects(&["1 tag Circle"]);
}

#[test]
fn grouped_tag_declarations() {
    assert_eq!(
        shape("tag T = A | B(Number)"),
        "goat[tag_decl[tag_kw(\"tag\") group_name[name(\"T\")] tag_case[name(\"A\")] \
         tag_case[name(\"B\") type_name(\"Number\")]]]"
    );
    assert_accepts(&[
        "tag A | B",
        "tag A(Number, String) | B",
        "tag T = A | B({x: Number, y: T}) 1",
        "tag A tag B | C a = 1",
    ]);
    assert_rejects(&["tag", "tag A |", "tag T = ", "tag A | | B"]);
}

#[test]
fn a_tag_construction_is_a_name_and_a_call() {
    assert_eq!(
        shape("Circle(5)"),
        "goat[expr[name(\"Circle\") call[arguments[expr[number(\"5\")]]]]]"
    );
}

#[test]
fn match_arms() {
    let source = "match s do Circle(r) then r Empty then 0 else 1 done";
    let tree = parse(source).unwrap();
    let m = tree
        .root()
        .child("expr")
        .unwrap()
        .child("match_expr")
        .unwrap();
    let parts: Vec<_> = m.children().map(|n| n.kind()).collect();
    assert_eq!(parts, ["expr", "arm", "arm", "expr"]);
    let arm = m.child("arm").unwrap();
    let parts: Vec<_> = arm.children().map(|n| n.kind()).collect();
    assert_eq!(parts, ["pattern", "expr"]);

    for source in [
        "match x do 0 then 1 done",
        "match x do \"go\" then 1 done",
        "match x do true then 1 done",
        "match x do 2.5 then 1 done",
    ] {
        let tree = parse(source).unwrap();
        let arm = tree
            .root()
            .child("expr")
            .and_then(|e| e.child("match_expr"))
            .and_then(|m| m.child("arm"))
            .unwrap();
        assert_eq!(
            arm.children().next().unwrap().kind(),
            "literal_pattern",
            "{source}"
        );
    }
}

#[test]
fn match_programs() {
    assert_accepts(&[
        "match x do done",
        "match x do else 0 done",
        "match x do A then 1 done",
        "match x do Link(a, b) then a\n  Empty then 0\n  else 2 done",
        "match Circle(5) do Circle(r) then r * r done",
        "match x do A then match y do B then 1 else 2 done else 3 done",
        "area = program(s) do match s do Circle(r) then r Square(w, h) then w * h done done\narea(Circle(2))",
        "f(Link(1, Empty))",
        "Circle(5).x",
        "{shape: Empty}",
    ]);
}

#[test]
fn record_spread() {
    assert_eq!(
        shape("{...p, x: 1}"),
        "goat[expr[record[spread[expr[name(\"p\")]] field[name(\"x\") expr[number(\"1\")]]]]]"
    );
    assert_eq!(
        shape("{...p}"),
        "goat[expr[record[spread[expr[name(\"p\")]]]]]"
    );
    assert_accepts(&["{...a, ...b}", "{x: 1, ...a}", "{...a.b, y: f(1),}"]);
    assert_rejects(&["{...}", "{,...a}", "{.. a}"]);
}

#[test]
fn destructuring() {
    assert_eq!(
        shape("{x, y} = p"),
        "goat[expr[destructure[record_pattern[name(\"x\") name(\"y\")] value[name(\"p\")]]]]"
    );
    assert_eq!(
        shape("{x, ...rest} = p x"),
        "goat[expr[destructure[record_pattern[name(\"x\") rest_binding[name(\"rest\")]] \
         value[name(\"p\")] expr[name(\"x\")]]]]"
    );
}

#[test]
fn destructuring_does_not_capture_record_literals() {
    assert_rejects(&["{x: 1} = 2"]);
    for source in [
        "{x}",
        "{x, y}",
        "{x, ...r}",
        "{...r} = p",
        "{...r, } = p",
        "{x,} = p",
    ] {
        assert_eq!(accepts(source), source.contains('='), "{source}");
    }
    assert_rejects(&[
        "{} = p",
        "{...a, x} = p",
        "{...a, ...b} = p",
        "{x, ...r, y} = p",
    ]);
}

#[test]
fn destructuring_parameters() {
    let tree = parse("program({x, y}) do x + y done").unwrap();
    let function = tree
        .root()
        .child("expr")
        .unwrap()
        .child("function")
        .unwrap();
    let params = function.child("params").unwrap();
    let kinds: Vec<_> = params.children().map(|n| n.kind()).collect();
    assert_eq!(kinds, ["record_pattern"]);
    assert_accepts(&[
        "program(a, {x, ...r}, b) do a done",
        "program({...r}) do r done",
        "function({x}) do x done",
    ]);
}

#[test]
fn loops() {
    for (source, kind) in [
        ("repeat 3 times do done", "repeat_loop"),
        ("repeat n + 1 times do f(); g() done", "repeat_loop"),
        ("for i from 1 to 10 do f(i) done", "count_loop"),
        ("for i from a.from to a.to do done", "count_loop"),
        ("for x in xs do f(x) done", "each_loop"),
        ("for x in [1, 2] do done", "each_loop"),
    ] {
        assert!(contains_kind(source, kind), "{source}");
    }
    assert_rejects(&[
        "repeat 3 do done",
        "for i from 1 do done",
        "for i 1 to 2 do done",
        "for i in do done",
        "for x in xs done",
        "for i fromm 1 to 2 do done",
    ]);
}
