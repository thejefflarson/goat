//! A list holds one kind of thing: the first element that does not fit those
//! before it is blamed, where it is written.

use goat_checker::hir::Span;
use goat_checker::{GoatError, check_with_prelude};

fn first_error(source: &str) -> GoatError {
    match check_with_prelude(goat_checker::PRELUDE, source) {
        Ok(_) => panic!("should not check: {source}"),
        Err(errors) => errors.into_iter().next().expect("an error"),
    }
}

fn text(source: &str, span: Span) -> &str {
    &source[span.start..span.end]
}

fn assert_blames_element(source: &str, element: &str) -> GoatError {
    let error = first_error(source);
    assert_eq!(text(source, error.span), element, "{error:?}");
    error
}

#[test]
fn a_method_and_a_plain_function_blame_the_element() {
    let source = "xs = [{f: program(self) do 1 done}, {f: program(s) do 1 done}]\nlength(xs)";
    let error = assert_blames_element(source, "{f: program(s) do 1 done}");
    assert_eq!(
        error.message,
        "`f` is a method in one record and a plain function in the other, so they don't have the same shape. \
         Start both with `self`, or neither."
    );
}

#[test]
fn a_string_among_numbers_blames_the_string() {
    let error = assert_blames_element("xs = [1, 2, \"three\"]\nsum(xs)", "\"three\"");
    assert_eq!(
        error.message,
        "a list holds one kind of thing; this is a String but the earlier items are Numbers"
    );
}

#[test]
fn a_record_missing_a_field_blames_that_record() {
    let source = "xs = [{a: 1, b: 2}, {a: 3}]\nkeep(xs, program(r) do r.b > 0 done)";
    assert_blames_element(source, "{a: 3}");
}

#[test]
fn a_clash_inside_a_nested_list_blames_the_inner_element() {
    let source = "xs = [[1], [\"a\"]]\nlength(xs)";
    let error = first_error(source);
    assert_eq!(text(source, error.span), "\"a\"", "{error:?}");
}

#[test]
fn the_first_clash_in_a_long_list_is_the_only_one_reported() {
    let source = "xs = [1, \"a\", 3, true]";
    let errors = goat_checker::check_with_prelude(goat_checker::PRELUDE, source)
        .err()
        .expect("should not check");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(text(source, errors[0].span), "\"a\"");
}

#[test]
fn a_list_of_one_kind_checks_with_any_element() {
    for source in [
        "xs = [1, 2, 3]",
        "xs = [\"a\"]",
        "xs = [[1], [], [2, 3]]",
        "xs = []",
    ] {
        goat_checker::check_with_prelude(goat_checker::PRELUDE, source)
            .unwrap_or_else(|e| panic!("{source}: {e:?}"));
    }
}

#[test]
fn a_link_whose_payload_is_not_an_item_and_a_tail_is_rejected_at_the_check() {
    for (source, blamed) in [
        (
            "xs = Link({a: \"hi\", b: 7})\nn = match xs do [x, ...rest] then x + 1 [] then 0 done\nprint(n)",
            "{a: \"hi\", b: 7}",
        ),
        ("print(length(Link({a: 1, b: 2})))", "{a: 1, b: 2}"),
        ("xs = Link(1)\nlength(xs)", "1"),
    ] {
        let error = first_error(source);
        assert!(!error.span.in_prelude(), "{source}: {error:?}");
        assert!(
            text(source, error.span).contains(blamed),
            "{source}: {error:?}"
        );
    }
}
