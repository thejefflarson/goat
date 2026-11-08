use goat_parser::parser::{GoatParser, Rule};
use pest::Parser;
use rowan_slice::{SyntaxKind, ast, enclosing_kinds, parse};

const GOOD: &str = r#"
# areas
tag_unused = 0
area = shape.size * 2 + 1;
total = match shape do
  Circle(r) then r * r * 3
  Square(s) then s * s
  0 then 0
  else -1
done;
f(area, total) + g.h
"#;

fn pest_errors(src: &str) -> usize {
    // pest returns at most one error: it stops at the first failure.
    usize::from(GoatParser::parse(Rule::goat, src).is_err())
}

#[test]
fn valid_program_has_no_diagnostics_and_round_trips() {
    let p = parse(GOOD);
    assert_eq!(p.diagnostics, vec![]);
    assert_eq!(p.syntax().text().to_string(), GOOD);
    assert!(
        GoatParser::parse(Rule::goat, GOOD).is_ok(),
        "pest accepts it too"
    );
    let lets = ast::lets(&p.syntax());
    let names: Vec<_> = lets.iter().filter_map(|l| l.name()).collect();
    assert_eq!(names, ["tag_unused", "area", "total"]);
}

#[test]
fn match_arms_are_reachable_through_the_typed_view() {
    let p = parse(GOOD);
    let m = p
        .syntax()
        .descendants()
        .find_map(ast::MatchExpr::cast)
        .expect("a match");
    assert!(m.has_done());
    assert!(m.scrutinee().is_some());
    let heads: Vec<_> = m.arms().filter_map(|a| a.pattern_head()).collect();
    assert_eq!(heads, ["Circle", "Square", "0"]);
}

#[test]
fn missing_value_after_equals_keeps_the_binding_and_the_rest() {
    let src = "a = ;\nb = 2;\nb";
    let p = parse(src);
    assert_eq!(p.diagnostics.len(), 1, "{:?}", p.diagnostics);
    assert!(p.diagnostics[0].message.contains("a value after `=`"));
    assert_eq!(&src[p.diagnostics[0].range.clone()], ";");
    assert_eq!(p.syntax().text().to_string(), src);
    let names: Vec<_> = ast::lets(&p.syntax())
        .iter()
        .filter_map(|l| l.name())
        .collect();
    assert_eq!(names, ["a", "b"], "both bindings survive");
    assert_eq!(pest_errors(src), 1);
}

#[test]
fn dangling_equals_at_eof() {
    let src = "a = ";
    let p = parse(src);
    assert_eq!(p.diagnostics.len(), 1);
    assert_eq!(p.diagnostics[0].range, 4..4, "empty span at end of file");
    assert_eq!(ast::lets(&p.syntax()).len(), 1);
}

#[test]
fn trailing_operator_reports_and_continues() {
    let src = "x = 1 + ; y = 2 * ; z = 3";
    let p = parse(src);
    assert_eq!(p.diagnostics.len(), 2, "{:?}", p.diagnostics);
    assert_eq!(
        ast::lets(&p.syntax()).len(),
        3,
        "all three bindings survive"
    );
}

#[test]
fn match_with_no_arms_and_no_done() {
    let src = "match x do";
    let p = parse(src);
    let msgs: Vec<_> = p.diagnostics.iter().map(|d| d.message.as_str()).collect();
    assert_eq!(
        msgs,
        ["expected `done` to close `match`, found end of file"]
    );
    // The editor asks "what is at the cursor?" at the end of the line.
    let kinds = enclosing_kinds(&p.syntax(), src.len());
    assert!(kinds.contains(&SyntaxKind::MatchExpr), "{kinds:?}");
    assert_eq!(pest_errors(src), 1);
}

#[test]
fn arm_without_a_body() {
    let src = "match s do\n  Circle(r) then\ndone";
    let p = parse(src);
    assert_eq!(p.diagnostics.len(), 1, "{:?}", p.diagnostics);
    assert!(
        p.diagnostics[0]
            .message
            .starts_with("expected an expression")
    );
    let m = p
        .syntax()
        .descendants()
        .find_map(ast::MatchExpr::cast)
        .unwrap();
    assert!(m.has_done(), "done is still matched to its match");
    assert_eq!(m.arms().count(), 1);
}

#[test]
fn arm_missing_then() {
    let src = "match s do\n  Circle(r) r * r\n  Square(s) then s\ndone";
    let p = parse(src);
    assert_eq!(p.diagnostics.len(), 1, "{:?}", p.diagnostics);
    assert!(p.diagnostics[0].message.starts_with("expected `then`"));
    let m = p
        .syntax()
        .descendants()
        .find_map(ast::MatchExpr::cast)
        .unwrap();
    assert_eq!(m.arms().count(), 2, "the second arm is unaffected");
}

#[test]
fn unterminated_match_does_not_swallow_following_bindings() {
    let src = "m = match x do\n  A then 1\ny = 2;\ny";
    let p = parse(src);
    assert_eq!(p.diagnostics.len(), 1, "{:?}", p.diagnostics);
    assert!(p.diagnostics[0].message.contains("`done`"));
    let names: Vec<_> = ast::lets(&p.syntax())
        .iter()
        .filter_map(|l| l.name())
        .collect();
    assert_eq!(names, ["m", "y"]);
}

#[test]
fn several_independent_errors_in_one_file() {
    let src = "a = ;\nb = (1 + ;\nc = match z do\n  X then done;\nd = 4";
    let p = parse(src);
    assert!(p.diagnostics.len() >= 3, "{:?}", p.diagnostics);
    let names: Vec<_> = ast::lets(&p.syntax())
        .iter()
        .filter_map(|l| l.name())
        .collect();
    assert_eq!(names, ["a", "b", "c", "d"]);
    assert_eq!(p.syntax().text().to_string(), src);
    assert_eq!(pest_errors(src), 1, "pest reports one error, then stops");
}

#[test]
fn every_prefix_of_a_valid_program_parses_losslessly() {
    // The real editor workload: the buffer is a prefix of the program while
    // the user types. Count how many prefixes each parser can hand a tree for.
    let (mut pest_ok, mut total) = (0, 0);
    for end in GOOD.char_indices().map(|(i, _)| i).chain([GOOD.len()]) {
        let prefix = &GOOD[..end];
        let p = parse(prefix);
        assert_eq!(p.syntax().text().to_string(), prefix, "lossless at {end}");
        total += 1;
        pest_ok += usize::from(GoatParser::parse(Rule::goat, prefix).is_ok());
    }
    eprintln!("prefixes: {total}; pest yields a tree for {pest_ok}, rowan for {total}");
    assert!(pest_ok < total / 2, "most prefixes are invalid to pest");
}

#[test]
fn hostile_input_does_not_overflow_the_stack() {
    for src in [
        "(".repeat(100_000),
        "-".repeat(100_000),
        "match ".repeat(50_000),
    ] {
        let p = parse(&src);
        assert!(!p.diagnostics.is_empty());
        assert_eq!(p.syntax().text().to_string(), src);
    }
}

#[test]
fn unknown_characters_become_error_nodes() {
    let p = parse("a = 1 @ 2");
    assert!(!p.diagnostics.is_empty());
    assert_eq!(p.syntax().text().to_string(), "a = 1 @ 2");
}
