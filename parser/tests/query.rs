//! The cursor queries on broken buffers: every source here is incomplete, and
//! `|` marks the cursor.

use goat_parser::interp::parse_recovering;
use goat_parser::query::{Role, TokenContext};

/// The source and the cursor: the last `|`, since a tag declaration has its own.
fn split(marked: &str) -> (String, usize) {
    let at = marked.rfind('|').expect("a cursor");
    (format!("{}{}", &marked[..at], &marked[at + 1..]), at)
}

fn path(marked: &str) -> Vec<String> {
    let (source, cursor) = split(marked);
    let recovered = parse_recovering(&source);
    recovered
        .cst
        .enclosing_path(cursor)
        .iter()
        .map(|n| n.kind().to_string())
        .collect()
}

fn ctx(marked: &str) -> (String, TokenContext) {
    let (source, cursor) = split(marked);
    let context = parse_recovering(&source).cst.token_context(cursor);
    (source, context)
}

fn role(marked: &str) -> Role {
    ctx(marked).1.role
}

#[test]
fn a_binding_without_a_value_is_enclosed_by_the_declaration_and_the_missing_value() {
    assert_eq!(path("a = |"), ["goat", "expr", "declaration", "MISSING"]);
    assert_eq!(
        path("a =\n\n  |"),
        ["goat", "expr", "declaration", "MISSING"]
    );
}

#[test]
fn a_dot_with_nothing_after_it_is_an_access_missing_its_name() {
    assert_eq!(
        path("p = {x: 1}\np.|"),
        ["goat", "expr", "access", "MISSING"]
    );
    assert_eq!(
        path("q = p.fo|"),
        ["goat", "expr", "declaration", "value", "access", "name"]
    );
}

#[test]
fn a_take_with_nothing_after_it_is_a_take_missing_its_name() {
    assert_eq!(
        path("p = {x: 1}\np::|"),
        ["goat", "expr", "take", "MISSING"]
    );
    assert_eq!(
        path("q = p::fo|"),
        ["goat", "expr", "declaration", "value", "take", "name"]
    );
}

#[test]
fn an_unterminated_match_encloses_a_cursor_in_its_trailing_space() {
    assert_eq!(
        path("match s do\n  |"),
        ["goat", "expr", "match_expr", "MISSING"]
    );
    assert_eq!(
        path("match s do\n  Circle(r) then 1\n  |")[..4],
        ["goat", "expr", "match_expr", "arm"]
    );
}

#[test]
fn a_cursor_inside_a_closed_node_does_not_reach_a_later_one() {
    let path = path("a = {x: |1}\nb = 2");
    assert_eq!(path[..3], ["goat", "expr", "declaration"]);
    assert_eq!(path.last().unwrap(), "number");
}

#[test]
fn the_path_always_starts_at_the_root_even_past_the_end() {
    let recovered = parse_recovering("x = 1");
    let kinds: Vec<_> = recovered
        .cst
        .enclosing_path(500)
        .iter()
        .map(|n| n.kind())
        .collect();
    assert_eq!(kinds, ["goat"]);
}

#[test]
fn after_a_dot_the_base_is_the_operand_before_it() {
    let (source, context) = ctx("p = {x: 1}\nq = p.|");
    let Role::Field { base } = context.role else {
        panic!("{:?}", context.role)
    };
    assert_eq!(&source[base], "p");
    assert_eq!(context.prefix, source.len()..source.len());
}

#[test]
fn a_chain_of_accesses_has_the_whole_chain_before_the_last_dot_as_its_base() {
    let (source, context) = ctx("q = a.b(1).c.|");
    let Role::Field { base } = context.role else {
        panic!("{:?}", context.role)
    };
    assert_eq!(&source[base], "a.b(1).c");
}

#[test]
fn a_half_typed_field_is_a_prefix_after_a_dot() {
    let (source, context) = ctx("q = p.fo|");
    assert_eq!(&source[context.prefix.clone()], "fo");
    let Role::Field { base } = context.role else {
        panic!("{:?}", context.role)
    };
    assert_eq!(&source[base], "p");
}

#[test]
fn a_binding_value_and_an_argument_are_operand_positions() {
    for marked in [
        "a = |",
        "a = 1\nb = |",
        "f(|",
        "x = 1 + |",
        "if |",
        "q = if c then |",
    ] {
        assert_eq!(role(marked), Role::Operand, "{marked:?}");
    }
    let (source, context) = ctx("size = 40\nforward(si|");
    assert_eq!(context.role, Role::Operand);
    assert_eq!(&source[context.prefix], "si");
}

#[test]
fn the_head_of_an_arm_names_the_scrutinee_and_the_tags_already_matched() {
    for marked in [
        "match shape do\n  |",
        "match shape do\n  Circle(r) then 1\n  |",
        "match shape do\n  Circle(r) then 1\n  Do|",
        "x = match shape do\n  Circle(r) then 1\n  [a, ...b] then 2\n  |",
    ] {
        let (source, context) = ctx(marked);
        let Role::ArmPattern { scrutinee, covered } = context.role else {
            panic!("{marked:?}: {:?}", context.role)
        };
        assert_eq!(
            &source[scrutinee.expect("scrutinee")],
            "shape",
            "{marked:?}"
        );
        assert!(covered.len() <= 2, "{covered:?}");
    }
    let Role::ArmPattern { covered, .. } =
        role("match s do\n  Circle(r) then 1\n  Dot then 2\n  |")
    else {
        panic!()
    };
    assert_eq!(covered, ["Circle", "Dot"]);
}

#[test]
fn the_arm_being_typed_is_not_one_the_others_cover() {
    let Role::ArmPattern { covered, .. } = role("match s do\n  Circle(r) then 1\n  Ci|") else {
        panic!()
    };
    assert_eq!(covered, ["Circle"]);
}

#[test]
fn an_arm_body_is_an_operand_position_not_an_arm_head() {
    assert_eq!(role("match s do\n  Circle(r) then |"), Role::Operand);
    assert_eq!(role("match s do\n  Circle(r) then f(|"), Role::Operand);
    assert_eq!(role("match s do\n  Circle(r) then 1 +\n  |"), Role::Operand);
}

#[test]
fn a_finished_match_has_no_arm_heads() {
    assert_eq!(role("match s do\n  A then 1\ndone\n|"), Role::Operand);
    assert!(!matches!(
        role("match s do A then 1 done|"),
        Role::ArmPattern { .. }
    ));
}

#[test]
fn a_nested_unfinished_construct_in_an_arm_body_keeps_the_cursor_in_the_body() {
    assert_eq!(
        role("match s do\n  A then if c then 1\n  |"),
        Role::Nothing,
        "the `if` still waits for its `done`"
    );
}

#[test]
fn names_being_introduced_complete_nothing() {
    for marked in [
        "f = program(|",
        "f = program(a, |",
        "f = fn(|",
        "f = fn(a, |",
        "for |",
        "match s do\n  Circle(r) then 1\n  Dot(|) then 2",
        "tag |",
        "tag Shape = Circle(Number) | |",
        "{x, |",
        "r = {|",
    ] {
        assert_eq!(role(marked), Role::Nothing, "{marked:?}");
    }
}

#[test]
fn comments_strings_and_numbers_complete_nothing() {
    for marked in [
        "# fo|",
        "x = \"fo|",
        "x = \"fo|\"",
        "x = 12|",
        "x = 1.5|",
        "x = $fo|",
    ] {
        assert_eq!(role(marked), Role::Nothing, "{marked:?}");
    }
    assert_eq!(role("x = \"done\" |"), Role::Operand);
}

#[test]
fn a_construct_waiting_for_a_keyword_names_it() {
    let (_, context) = ctx("if x |");
    assert_eq!(context.expected, ["then", "done"]);
    assert_eq!(context.role, Role::Nothing);
    let (_, context) = ctx("match s do\n  |");
    assert_eq!(context.expected, ["done"]);
    let (_, context) = ctx("repeat 3 |");
    assert_eq!(context.expected.first(), Some(&"times"));
    let (_, context) = ctx("a = |");
    assert!(context.expected.is_empty());
}

#[test]
fn the_prefix_is_the_word_up_to_the_cursor() {
    let (source, context) = ctx("x = 1\nfor|ward(1)");
    assert_eq!(&source[context.prefix], "for");
    let (source, context) = ctx("fo|");
    assert_eq!(&source[context.prefix.clone()], "fo");
    assert_eq!(context.previous, None);
}

#[test]
fn every_prefix_of_a_program_answers_without_panicking() {
    let source = "tag Shape = Circle(Number) | Dot\n\
        area = program(s) do\n  match s do\n    Circle(r) then r * r\n    Dot then 0\n  done\ndone\n\
        p = {x: 1, y: [1, 2]}\nfor i from 1 to 3 do\n  area(Circle(i)) + p.x\ndone\n";
    for end in (0..=source.len()).filter(|&i| source.is_char_boundary(i)) {
        let recovered = parse_recovering(&source[..end]);
        for offset in [0, end / 2, end.saturating_sub(1), end] {
            let _ = recovered.cst.enclosing_path(offset);
            let _ = recovered.cst.token_context(offset);
        }
    }
}
