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
