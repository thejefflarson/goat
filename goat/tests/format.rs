//! The formatter is a goat program (`editor/format.goat`, ADR 0041). It must
//! change whitespace and nothing else: on every goat file in the repo, and on
//! every string the Rust tests quote, the output lexes to the same tokens
//! (comments included), parses to the same tree, formats to itself again and
//! type-checks the same.
#![cfg(feature = "native")]

use goat::format::{Edit, Formatter, apply};
use goat::{GoatError, HostInterface};
use goat_parser::cst::{Child, Node};
use goat_parser::interp::parse;
use goat_parser::lexer::{self, TokenKind};
use std::fs;

#[allow(dead_code)]
#[path = "../../parser/tests/corpus/mod.rs"]
mod corpus;

fn tokens(source: &str) -> Vec<(TokenKind, String)> {
    lexer::lex(source)
        .into_iter()
        .filter(|token| token.kind != TokenKind::Whitespace)
        .map(|token| (token.kind, source[token.start..token.end].to_string()))
        .collect()
}

fn shape(node: Node, out: &mut Vec<String>) {
    out.push(format!("({}", node.kind()));
    for child in node.elements() {
        match child {
            Child::Node(inner) => shape(inner, out),
            Child::Token(token) if token.kind == TokenKind::Whitespace => {}
            Child::Token(token) => {
                let start = node.span().start;
                let text = &node.text()[token.start - start..token.end - start];
                out.push(format!("{:?} {text}", token.kind));
            }
        }
    }
    out.push(")".to_string());
}

/// The parse of `source` with the whitespace left out, or that it does not parse (an error's offset moves with the whitespace).
fn parsed(source: &str) -> Result<Vec<String>, String> {
    match parse(source) {
        Ok(cst) => {
            let mut out = Vec::new();
            shape(cst.root(), &mut out);
            Ok(out)
        }
        Err(_) => Err("does not parse".to_string()),
    }
}

fn messages(errors: &[GoatError]) -> Vec<String> {
    errors.iter().map(|e| e.message.clone()).collect()
}

/// What the checker says of `source` against the turtle host, spans left out.
fn checked(source: &str) -> Result<(String, usize), Vec<String>> {
    goat::check(source, &HostInterface::turtle())
        .map(|(ty, warnings)| (ty.to_string(), warnings.len()))
        .map_err(|errors| messages(&errors))
}

fn assert_preserved(formatter: &mut Formatter, name: &str, source: &str) -> String {
    let formatted = formatter.format(source).unwrap();
    assert_eq!(tokens(source), tokens(&formatted), "{name}: tokens changed");
    assert_eq!(parsed(source), parsed(&formatted), "{name}: parse changed");
    assert_eq!(
        formatter.format(&formatted).unwrap(),
        formatted,
        "{name}: not idempotent"
    );
    formatted
}

#[test]
fn every_goat_file_keeps_its_tokens_parse_and_type_and_formats_to_itself() {
    let files = corpus::files_with("goat");
    assert!(files.len() > 25, "{} goat files", files.len());
    let mut formatter = Formatter::new().unwrap();
    for file in &files {
        let name = file.display().to_string();
        let source = fs::read_to_string(file).unwrap();
        let formatted = assert_preserved(&mut formatter, &name, &source);
        assert_eq!(
            checked(&source),
            checked(&formatted),
            "{name}: type changed"
        );
        assert_eq!(formatted, source, "{name} is not formatted: run `goat fmt`");
    }
}

#[test]
fn the_strings_the_tests_quote_keep_their_tokens_and_parse() {
    let literals: Vec<String> = corpus::rust_sources()
        .iter()
        .flat_map(|source| corpus::string_literals(source))
        .filter(|text| text.is_ascii() && text.len() < 4000)
        .collect();
    assert!(literals.len() > 1000, "{} literals", literals.len());
    let mut formatter = Formatter::new().unwrap();
    for text in &literals {
        assert_preserved(&mut formatter, &format!("{text:?}"), text);
    }
}

fn formats(source: &str) -> String {
    Formatter::new().unwrap().format(source).unwrap()
}

#[test]
fn indentation_follows_blocks_and_brackets() {
    let source = "f = program(x) do\nif x then\n1\nelse\n2 done\ndone\n\nxs = [\n1,\n2\n]\n";
    let expected =
        "f = program(x) do\n  if x then\n    1\n  else\n    2 done\ndone\n\nxs = [\n  1,\n  2\n]\n";
    assert_eq!(formats(source), expected);
}

#[test]
fn match_arms_line_up_with_the_else_arm() {
    let source = "m = program(k) do\nmatch k do\nUp then 1\nelse 0 done\ndone\n";
    let expected = "m = program(k) do\n  match k do\n    Up then 1\n    else 0 done\ndone\n";
    assert_eq!(formats(source), expected);
}

#[test]
fn an_else_if_chain_adds_one_indent() {
    let source = "x = if a then 1\nelse if b then 2\nelse 3 done done\n";
    assert_eq!(formats(source), source);
    let flat = "x = if a then 1\n  else if b then 2\n          else 3 done done\n";
    assert_eq!(
        formats(flat),
        "x = if a then 1\nelse if b then 2\nelse 3 done done\n"
    );
}

#[test]
fn an_if_whose_head_runs_over_lines_indents_its_branches() {
    let source = "f = program(x) do\n  if x > 1\n  then 2\n  else\n  y = 3\n  y done\ndone\n";
    let expected =
        "f = program(x) do\n  if x > 1\n    then 2\n    else\n      y = 3\n      y done\ndone\n";
    assert_eq!(formats(source), expected);
    assert_eq!(formats(expected), expected);
}

#[test]
fn a_match_arm_whose_body_starts_on_the_next_line_indents_it() {
    let source = "m = program(k) do\nmatch k do\nUp then\ny = 1\ny + 1\nelse 0 done\ndone\n";
    let expected = "m = program(k) do\n  match k do\n    Up then\n      y = 1\n      y + 1\n    else 0 done\ndone\n";
    assert_eq!(formats(source), expected);
}

#[test]
fn names_that_would_read_as_one_keyword_stay_apart() {
    assert_eq!(
        formats("start  at 1\nstart   at\n"),
        "start  at 1\nstart   at\n"
    );
}

#[test]
fn trailing_comments_keep_their_alignment() {
    assert_eq!(
        formats("a = 1   # one\nbb = 2 # two\nc = 3\t# three\n"),
        "a = 1   # one\nbb = 2 # two\nc = 3 # three\n"
    );
}

#[test]
fn spacing_is_one_space_between_tokens_and_none_inside_brackets() {
    assert_eq!(
        formats("x=f( 1,2 ,{a:1 ,b : [ 3 ]} ) +  2*3\n"),
        "x = f(1, 2, {a: 1, b: [3]}) + 2 * 3\n"
    );
    assert_eq!(
        formats("f = program(a) do a . b  done\n"),
        "f = program(a) do a.b done\n"
    );
}

#[test]
fn a_minus_that_is_a_sign_keeps_its_number() {
    assert_eq!(
        formats("x = f(-3, 1 -2, a - -1)\n"),
        "x = f(-3, 1 - 2, a - -1)\n"
    );
}

#[test]
fn a_dotted_number_is_not_pulled_apart_or_together() {
    assert_eq!(formats("x = 1 .y\n"), "x = 1 .y\n");
    assert_eq!(formats("x = 1.5   +   .5\n"), "x = 1.5 + .5\n");
}

#[test]
fn blank_lines_are_capped_and_the_text_ends_in_one_line_break() {
    assert_eq!(formats("\n\n  a = 1   \n\n\n\nb = 2"), "a = 1\n\nb = 2\n");
    assert_eq!(
        formats("f = program() do\n\n1\n\ndone"),
        "f = program() do\n  1\ndone\n"
    );
    assert_eq!(formats(" \n\t\n"), "");
    assert_eq!(formats(""), "");
}

#[test]
fn comments_are_kept_and_indented_with_the_code_around_them() {
    let source = "# top\nf = program() do\n# inside\n1 # after\n    # last\ndone\n";
    let expected = "# top\nf = program() do\n  # inside\n  1 # after\n  # last\ndone\n";
    assert_eq!(formats(source), expected);
}

#[test]
fn a_continued_expression_is_indented_once() {
    let source = "x = 1 +\n2\ny = a\nand b\n";
    assert_eq!(formats(source), "x = 1 +\n  2\ny = a\n  and b\n");
}

#[test]
fn crlf_line_endings_become_line_feeds() {
    assert_eq!(formats("a = 1\r\nb = 2\r\n"), "a = 1\nb = 2\n");
}

#[test]
fn a_text_that_does_not_lex_is_left_alone() {
    let source = "x   =  \"never closed\n  y";
    let mut formatter = Formatter::new().unwrap();
    assert_eq!(formatter.edits(source).unwrap(), []);
    assert_eq!(formatter.format("a =   1 @  2").unwrap(), "a =   1 @  2");
}

#[test]
fn edits_are_the_gaps_that_differ_and_nothing_else() {
    let mut formatter = Formatter::new().unwrap();
    let edits = formatter.edits("a  =1\n").unwrap();
    assert_eq!(
        edits,
        [
            Edit {
                from: 1,
                to: 3,
                newlines: 0,
                indent: 1
            },
            Edit {
                from: 4,
                to: 4,
                newlines: 0,
                indent: 1
            },
        ]
    );
    assert_eq!(formatter.edits("a = 1\n").unwrap(), []);
}

#[test]
fn applying_edits_refuses_to_touch_anything_but_whitespace() {
    let edit = |from, to| Edit {
        from,
        to,
        newlines: 0,
        indent: 0,
    };
    assert!(apply("a b", &[edit(0, 1)]).is_err());
    assert!(apply("a b", &[edit(1, 9)]).is_err());
    assert!(apply("a  b", &[edit(2, 3), edit(1, 2)]).is_err());
    assert_eq!(apply("a  b", &[edit(1, 3)]).unwrap(), "ab");
    let huge = |newlines, indent| Edit {
        from: 1,
        to: 2,
        newlines,
        indent,
    };
    assert!(apply("a b", &[huge(0, 1 << 40)]).is_err());
    assert!(apply("a b", &[huge(1 << 40, 0)]).is_err());
}

#[test]
fn a_record_that_would_end_past_column_80_breaks_one_field_per_line() {
    let source =
        "x = {alpha: 1000000, beta: 2000000, gamma: 3000000, delta: 4000000, epsilon: 5000000}\n";
    let expected = "x = {\n  alpha: 1000000,\n  beta: 2000000,\n  gamma: 3000000,\n  delta: 4000000,\n  epsilon: 5000000\n}\n";
    assert_eq!(formats(source), expected);
    assert_eq!(formats(expected), expected);
}

#[test]
fn a_record_that_fits_stays_on_one_line() {
    let source = "x = {alpha: 1, beta: 2}\n";
    assert_eq!(formats(source), source);
    let exact = format!("x = {{s: \"{}\"}}\n", "a".repeat(80 - 11));
    assert_eq!(formats(&exact), exact);
    let over = format!("x = {{s: \"{}\"}}\n", "a".repeat(80 - 10));
    assert!(formats(&over).starts_with("x = {\n  s: "));
}

#[test]
fn the_width_is_in_characters_not_bytes() {
    let source = format!("v = {{s: \"{}\"}}\n", "é".repeat(65));
    assert_eq!(formats(&source), source);
}

#[test]
fn only_the_records_that_are_too_long_break_inside_a_long_record() {
    let source = "x = {a: {p: 1, q: 2}, b: {rrrrrrrrrrrrrrrrrrrrrrrrr: 111111111111111, sssssssssssssssssssssss: 22222222222222}, c: 3}\n";
    let expected = "x = {\n  a: {p: 1, q: 2},\n  b: {\n    rrrrrrrrrrrrrrrrrrrrrrrrr: 111111111111111,\n    sssssssssssssssssssssss: 22222222222222\n  },\n  c: 3\n}\n";
    assert_eq!(formats(source), expected);
    assert_eq!(formats(expected), expected);
}

#[test]
fn a_record_written_across_lines_stays_broken_one_field_to_a_line() {
    assert_eq!(
        formats("y = {a: 1,\n  b: 2}\n"),
        "y = {\n  a: 1,\n  b: 2\n}\n"
    );
    let broken = "y = {\n  a: 1,\n  b: 2\n}\n";
    assert_eq!(formats(broken), broken);
}

#[test]
fn a_long_list_breaks_like_a_record() {
    let source = "xs = [111111111111, 222222222222, 333333333333, 444444444444, 555555555555, 666666666666]\n";
    let expected = "xs = [\n  111111111111,\n  222222222222,\n  333333333333,\n  444444444444,\n  555555555555,\n  666666666666\n]\n";
    assert_eq!(formats(source), expected);
}

#[test]
fn a_comment_inside_a_record_breaks_it_and_stays_on_its_line() {
    assert_eq!(
        formats("x = {a: 1, # first\nb: 2}\n"),
        "x = {\n  a: 1, # first\n  b: 2\n}\n"
    );
}

#[test]
fn call_arguments_are_never_broken() {
    let source = "w = f(111111111111111, 222222222222222, 333333333333333, 444444444444444, 55555555555555)\n";
    assert_eq!(formats(source), source);
}

#[test]
fn a_broken_record_inside_a_call_closes_at_the_indent_of_the_line_that_opened_it() {
    let source = "f = program(a) do\nlexed(a, if a then Link({kind: aaaaaaaaaaaaaaaaaaaa, start: bbbbbbbbbbbbbbbbbbbbbbb, stop: cccccccccccccccc}, a) else a done)\ndone\n";
    let expected = "f = program(a) do\n  lexed(a, if a then Link({\n    kind: aaaaaaaaaaaaaaaaaaaa,\n    start: bbbbbbbbbbbbbbbbbbbbbbb,\n    stop: cccccccccccccccc\n  }, a) else a done)\ndone\n";
    assert_eq!(formats(source), expected);
    assert_eq!(formats(expected), expected);
}
