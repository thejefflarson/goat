//! A program with syntax errors reports each one, spanned, from the
//! recovering parse instead of stopping at the first.

use goat_checker::check_with_prelude;

fn errors_of(source: &str) -> Vec<(String, String)> {
    let errors = check_with_prelude("", source)
        .err()
        .expect("should not check");
    errors
        .iter()
        .map(|e| (e.message.clone(), source[e.span.start..e.span.end].into()))
        .collect()
}

fn pair(message: &str, text: &str) -> (String, String) {
    (format!("parse error: {message}"), text.into())
}

#[test]
fn several_syntax_errors_are_each_reported_at_their_own_span() {
    assert_eq!(
        errors_of("f(a b); g(c d); 1"),
        [
            pair("unexpected input, expected `)`", "b"),
            pair("unexpected input, expected `)`", "d"),
        ]
    );
    assert_eq!(
        errors_of("x = 1 \u{1} y = 2; z = 3 ? 4; 5"),
        [
            pair("unexpected input", "\u{1} y = 2;"),
            pair("unexpected input", "? 4;"),
        ]
    );
}

#[test]
fn a_missing_token_is_a_zero_width_span_at_the_gap() {
    let errors = check_with_prelude("", "x = (1").err().expect("errors");
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].message, "parse error: expected `)`");
    assert_eq!((errors[0].span.start, errors[0].span.end), (6, 6));
}

#[test]
fn a_single_syntax_error_is_a_single_diagnostic() {
    assert_eq!(
        errors_of("f(a b)"),
        [pair("unexpected input, expected `)`", "b")]
    );
}

#[test]
fn syntax_errors_are_not_mixed_with_type_errors() {
    let errors = errors_of("1 + true; f(a b)");
    assert!(errors.iter().all(|(m, _)| m.starts_with("parse error")));
}

const SEMICOLON: &str = "parse error: put a `;` after";

fn semicolon_hint(source: &str) -> (String, usize) {
    let errors = check_with_prelude("", source).err().expect("errors");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].span.start, errors[0].span.end,
        "a gap, not a range"
    );
    (errors[0].message.clone(), errors[0].span.start)
}

#[test]
fn a_statement_on_the_next_line_wants_a_semicolon_where_the_last_one_ends() {
    let (message, at) = semicolon_hint("print(1)\nprint(2)\n");
    assert_eq!(
        message,
        format!("{SEMICOLON} `print(1)` to start a new statement")
    );
    assert_eq!(at, 9, "the start of the next line");
}

#[test]
fn the_missing_semicolon_is_found_inside_a_block_after_a_record_and_after_a_call() {
    let (message, at) = semicolon_hint("f = fn(x) do\n  print(x)\n  print(x)\ndone; f(1)");
    assert_eq!(
        message,
        format!("{SEMICOLON} `print(x)` to start a new statement")
    );
    assert_eq!(at, 26, "the start of the next line");
    let (message, _) = semicolon_hint("print({a: 1})\nprint(2)");
    assert_eq!(
        message,
        format!("{SEMICOLON} `print({{a: 1}})` to start a new statement")
    );
    let (message, _) = semicolon_hint("print(f(1, 2))\nprint(3)");
    assert!(message.starts_with(SEMICOLON), "{message}");
}

#[test]
fn other_syntax_errors_keep_their_messages() {
    assert_eq!(
        errors_of("f(a\nb)"),
        [pair("unexpected input, expected `)`", "b")]
    );
    assert_eq!(errors_of("1 ?\n2"), [pair("unexpected input", "?\n2")]);
}
