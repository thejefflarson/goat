//! `scope_at`, `type_of` and `complete` on buffers that do not parse: every
//! source here is incomplete, and `|` marks the cursor.

use goat_checker::query::{Analysis, Binding, Completions, Item, ItemKind, Origin, complete};
use goat_checker::{PRELUDE, Vocab};
use goat_parser::interp::parse_recovering;

/// The source and the cursor: the last `|`, since a tag declaration has its own.
fn split(marked: &str) -> (String, usize) {
    let at = marked.rfind('|').expect("a cursor");
    (format!("{}{}", &marked[..at], &marked[at + 1..]), at)
}

fn analyze(marked: &str) -> (Analysis, String, usize) {
    let (source, cursor) = split(marked);
    let cst = parse_recovering(&source).cst;
    (
        Analysis::new(PRELUDE, &Vocab::turtle(), cst, cursor),
        source,
        cursor,
    )
}

fn scope(marked: &str) -> Vec<Binding> {
    let (analysis, _, cursor) = analyze(marked);
    analysis.scope_at(cursor)
}

/// The program's own names in scope, with their types.
fn own(marked: &str) -> Vec<(String, String)> {
    scope(marked)
        .into_iter()
        .filter(|b| b.origin == Origin::Program)
        .map(|b| (b.name, b.ty.map_or("?".into(), |t| t.to_string())))
        .collect()
}

fn own_names(marked: &str) -> Vec<String> {
    own(marked).into_iter().map(|(name, _)| name).collect()
}

fn pair(name: &str, ty: &str) -> (String, String) {
    (name.into(), ty.into())
}

fn complete_at(marked: &str) -> Option<Completions> {
    let (source, cursor) = split(marked);
    complete(PRELUDE, &Vocab::turtle(), &source, cursor)
}

fn labels(marked: &str) -> Vec<String> {
    complete_at(marked)
        .unwrap_or_else(|| panic!("{marked:?} completes"))
        .items
        .into_iter()
        .map(|i| i.label)
        .collect()
}

fn item(marked: &str, label: &str) -> Item {
    complete_at(marked)
        .unwrap_or_else(|| panic!("{marked:?} completes"))
        .items
        .into_iter()
        .find(|i| i.label == label)
        .unwrap_or_else(|| panic!("{label} offered at {marked:?}"))
}

#[test]
fn scope_lists_earlier_bindings_latest_first_with_their_types() {
    assert_eq!(
        own("a = 1\nb = \"x\"\n|"),
        [pair("b", "String"), pair("a", "Number")]
    );
}

#[test]
fn scope_leaves_out_a_later_binding_and_the_one_being_defined() {
    assert_eq!(own_names("a = 1\nb = |\nc = 3"), ["a"]);
    assert_eq!(own_names("a = 1\nb = |"), ["a"]);
}

#[test]
fn scope_shadows_an_earlier_binding_with_a_later_one() {
    assert_eq!(own("a = 1\na = \"s\"\n|"), [pair("a", "String")]);
}

#[test]
fn scope_includes_the_prelude_and_the_builtins() {
    let found = scope("|");
    let get = |name: &str| found.iter().find(|b| b.name == name).unwrap();
    assert_eq!(get("forward").origin, Origin::Prelude);
    assert_eq!(
        get("forward").ty.as_ref().unwrap().to_string(),
        "(Number) -> Unit"
    );
    assert_eq!(
        get("item").params.as_deref(),
        Some(&["xs".into(), "n".into()][..])
    );
    assert_eq!(get("print").origin, Origin::Builtin);
    assert!(!found.iter().any(|b| b.name == "_"));
}

#[test]
fn a_user_binding_shadows_a_prelude_name() {
    let found = scope("color = 7\n|");
    let colors: Vec<_> = found.iter().filter(|b| b.name == "color").collect();
    assert_eq!(colors.len(), 1);
    assert_eq!(colors[0].origin, Origin::Program);
}

#[test]
fn scope_shows_a_parameter_only_inside_its_function() {
    let found = own("f = program(s, k) do\n  s == \"a\" and |\ndone");
    assert_eq!(found.len(), 2, "{found:?}");
    assert_eq!(found[0].0, "k");
    assert_eq!(found[1], pair("s", "String"));
    assert_eq!(own_names("f = program(n, m) do\n  n\ndone\n|"), ["f"]);
    assert_eq!(
        own_names("f = program(n|, m) do\n  n\ndone"),
        Vec::<String>::new()
    );
}

#[test]
fn a_function_is_in_scope_inside_its_own_body_after_it_is_defined() {
    let names = own_names("f = program(n) do\n  1\ndone\ng = program(k) do\n  |\ndone");
    assert_eq!(names, ["k", "f"]);
}

#[test]
fn scope_shows_a_pattern_binding_in_its_arm_with_the_payload_type() {
    let found = own("tag Shape = Circle(Number) | Dot\ns = Circle(1)\n\
         match s do\n  Circle(r) then r + |\n  Dot then 0\ndone");
    assert_eq!(found[0], pair("r", "Number"));
    assert!(
        own_names(
            "tag Shape = Circle(Number) | Dot\nmatch Dot do\n  Circle(r) then 1\n  Dot then |\ndone"
        )
        .iter()
        .all(|n| n != "r")
    );
}

#[test]
fn scope_shows_a_loop_variable_only_inside_the_loop() {
    assert_eq!(own_names("for i from 1 to 3 do\n  |\ndone"), ["i"],);
    assert!(own_names("for i from 1 to 3 do\n  i\ndone\n|").is_empty());
}

#[test]
fn scope_works_on_a_buffer_that_does_not_parse() {
    assert_eq!(
        own("a = 1\nb = {x: 2\nc = |"),
        [pair("b", "{x: Number}"), pair("a", "Number")]
    );
}

#[test]
fn type_of_an_expression_before_a_dot_on_a_broken_buffer() {
    let (analysis, source, _) = analyze("p = {x: 1, y: \"s\"}\nq = p.|");
    let at = source.find("p.").unwrap();
    let node = analysis.cst().root();
    let found = analysis.type_of_span(at..at + 1);
    assert_eq!(found.unwrap().to_string(), "{x: Number, y: String}");
    assert!(node.span().len() == source.len());
}

#[test]
fn type_of_a_node_matches_type_of_its_span() {
    let (analysis, source, _) = analyze("n = 1 + 2\nm = |");
    let root = analysis.cst().root();
    let value = root
        .children()
        .flat_map(|c| c.children())
        .find(|c| c.is("declaration"))
        .and_then(|d| d.child("value"))
        .unwrap();
    assert_eq!(&source[value.trimmed_span()], "1 + 2");
    assert_eq!(analysis.type_of(value).unwrap().to_string(), "Number");
}

#[test]
fn type_of_is_none_where_nothing_was_settled() {
    let (analysis, _, _) = analyze("a = |");
    assert_eq!(analysis.type_of_span(100..101), None);
}

#[test]
fn a_type_error_elsewhere_does_not_hide_the_types_of_what_is_fine() {
    let found = own("a = 1\nb = a + \"x\"\nc = {k: 2}\n|");
    assert_eq!(found[0], pair("c", "{k: Number}"));
    assert_eq!(found[2], pair("a", "Number"));
}

#[test]
fn a_field_offers_the_members_of_the_base_type_and_nothing_else() {
    let marked = "p = {x: 1, y: \"s\"}\nturtle = {heading: 90, pen_up: true}\np.|";
    let found = complete_at(marked).unwrap();
    let labels: Vec<_> = found.items.iter().map(|i| i.label.as_str()).collect();
    assert_eq!(labels, ["x", "y"]);
    assert!(found.items.iter().all(|i| i.kind == ItemKind::Field));
    assert_eq!(item(marked, "x").detail, "Number");
    assert_eq!(item(marked, "y").detail, "String");
    assert_eq!(found.from, marked.replace('|', "").len());
}

#[test]
fn a_half_typed_field_filters_by_prefix_and_ignores_the_unfinished_access() {
    let marked = "turtle = {heading: 90, height: 2, pen: true}\nturtle.he|";
    let found = complete_at(marked).unwrap();
    assert_eq!(
        found
            .items
            .iter()
            .map(|i| i.label.as_str())
            .collect::<Vec<_>>(),
        ["heading", "height"]
    );
    assert_eq!(found.from, marked.len() - 3);
}

#[test]
fn a_field_of_a_chain_uses_the_type_at_each_step() {
    let marked = "w = {pos: {x: 1, y: 2}, name: \"w\"}\nw.pos.|";
    assert_eq!(labels(marked), ["x", "y"]);
}

#[test]
fn a_field_of_something_with_no_members_offers_nothing() {
    assert_eq!(complete_at("n = 1\nn.|").map(|c| c.items), None);
}

#[test]
fn a_field_survives_junk_after_the_dot() {
    let marked = "p = {x: 1, y: 2}\nforward(p.|\nback(3";
    assert_eq!(labels(marked), ["x", "y"]);
}

#[test]
fn a_binding_value_offers_scope_prelude_builtins_and_tags() {
    let marked = "size = 40\nname = \"goat\"\nc = |";
    let found = labels(marked);
    let at = |l: &str| {
        found
            .iter()
            .position(|x| x == l)
            .unwrap_or_else(|| panic!("{l}"))
    };
    assert!(at("name") < at("size"), "latest first");
    assert!(at("size") < at("forward"), "the program's names first");
    for label in [
        "forward", "print", "sort", "Tick", "Empty", "if", "match", "program",
    ] {
        at(label);
    }
    assert!(at("forward") < at("Tick") && at("Tick") < at("if"));
    assert_eq!(item(marked, "size").detail, "Number");
    assert_eq!(item(marked, "size").kind, ItemKind::Variable);
    assert_eq!(item(marked, "forward").kind, ItemKind::Function);
    assert_eq!(item(marked, "forward").detail, "(Number) -> Unit");
    assert_eq!(item(marked, "item").detail, "(xs, n)");
    assert_eq!(item(marked, "Tick").kind, ItemKind::Tag);
    assert_eq!(item(marked, "if").kind, ItemKind::Keyword);
    assert!(
        !found
            .iter()
            .any(|l| l == "then" || l == "done" || l == "tag")
    );
}

#[test]
fn a_binding_value_leaves_out_the_name_being_defined_and_later_names() {
    let found = labels("a = 1\nb = |\nlater = 2");
    assert!(found.contains(&"a".to_string()));
    assert!(!found.contains(&"b".to_string()));
    assert!(!found.contains(&"later".to_string()));
}

#[test]
fn declared_tags_are_offered_ahead_of_the_hosts() {
    let found = labels("tag Blob\ntag Shape = Circle(Number) | Dot\nx = |");
    let at = |l: &str| found.iter().position(|x| x == l).unwrap();
    assert!(at("Blob") < at("Empty") && at("Circle") < at("Tick"));
}

#[test]
fn a_prefix_narrows_the_list_and_a_complete_word_is_not_offered_again() {
    let found = labels("size = 4\nx = si|");
    assert_eq!(found[0], "size");
    assert!(found.iter().all(|l| l.to_lowercase().starts_with("si")));
    assert!(!labels("size = 4\nx = size|").contains(&"size".to_string()));
}

#[test]
fn a_match_arm_offers_the_scrutinees_tags() {
    let marked = "tag Shape = Circle(Number) | Square(Number) | Dot\ns = Dot\nmatch s do\n  |";
    let found = complete_at(marked).unwrap();
    let tags: Vec<_> = found
        .items
        .iter()
        .filter(|i| i.kind == ItemKind::Tag)
        .map(|i| i.label.as_str())
        .collect();
    assert_eq!(tags, ["Circle", "Square", "Dot"]);
    assert_eq!(item(marked, "Circle").detail, "Number");
    assert_eq!(item(marked, "Dot").detail, "");
    assert!(!tags.contains(&"Tick"), "host tags are not this value's");
}

#[test]
fn a_match_arm_leaves_out_the_tags_already_matched() {
    let marked = "tag Shape = Circle(Number) | Square(Number) | Dot\ns = Dot\n\
        match s do\n  Circle(r) then 1\n  |";
    let found = labels(marked);
    assert!(!found.contains(&"Circle".to_string()));
    assert!(found.contains(&"Square".to_string()) && found.contains(&"Dot".to_string()));
}

#[test]
fn a_match_arm_filters_a_half_typed_tag() {
    let marked = "tag Shape = Circle(Number) | Square(Number) | Dot\ns = Dot\nmatch s do\n  Sq|";
    let found = complete_at(marked).unwrap();
    assert_eq!(
        found
            .items
            .iter()
            .map(|i| i.label.as_str())
            .collect::<Vec<_>>(),
        ["Square"]
    );
    assert_eq!(found.from, marked.len() - 3);
}

#[test]
fn a_match_arm_on_a_parameter_offers_the_rest_of_the_group_an_arm_names() {
    let marked =
        "tag T = A | B(String)\nf = program(t) do\n  match t do\n    A then 1\n    |\ndone";
    let found = complete_at(marked).unwrap();
    let tags: Vec<_> = found
        .items
        .iter()
        .filter(|i| i.kind == ItemKind::Tag)
        .map(|i| (i.label.as_str(), i.detail.as_str()))
        .collect();
    assert_eq!(tags, [("B", "String")]);
}

#[test]
fn a_match_arm_on_a_parameter_with_open_tags_offers_every_tag() {
    let marked = "f = program(s) do\n  match s do\n    Tick(r) then 1\n    |\ndone";
    let found = labels(marked);
    assert!(found.contains(&"KeyDown".to_string()) && !found.contains(&"Tick".to_string()));
}

#[test]
fn a_match_arm_after_a_list_scrutinee_offers_the_list_tags() {
    let marked = "xs = [1, 2]\nmatch xs do\n  |";
    let tags = labels(marked);
    assert!(tags.contains(&"Empty".to_string()) && tags.contains(&"Link".to_string()));
}

#[test]
fn nothing_completes_where_a_name_is_introduced_or_in_text() {
    for marked in [
        "# fo|",
        "x = \"fo|",
        "x = 12|",
        "f = program(a, |",
        "for |",
        "tag |",
    ] {
        assert_eq!(complete_at(marked), None, "{marked:?}");
    }
}

#[test]
fn a_construct_waiting_for_a_keyword_offers_it() {
    assert_eq!(labels("if x |"), ["then", "done"]);
    assert_eq!(labels("if x th|"), ["then"]);
}

#[test]
fn completing_never_panics_on_any_prefix_of_a_program() {
    let source = "tag Shape = Circle(Number) | Dot\n\
        area = program(s) do\n  match s do\n    Circle(r) then r * r\n    Dot then 0\n  done\ndone\n\
        p = {x: 1, y: [1, 2]}\nfor i from 1 to 3 do\n  area(Circle(i)) + p.x\ndone\n";
    let vocab = Vocab::turtle();
    for end in (0..=source.len())
        .filter(|&i| source.is_char_boundary(i))
        .step_by(3)
    {
        let _ = complete(PRELUDE, &vocab, &source[..end], end);
    }
    let _ = complete(PRELUDE, &vocab, "é = 1\né.", 7);
}
