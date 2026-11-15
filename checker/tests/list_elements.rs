//! A list whose elements clash is blamed on the element that does not fit,
//! with a note where the list is used.

use goat_checker::hir::Span;
use goat_checker::{GoatError, check_with_prelude};

const NOTE: &str = "…and the list meets here";

fn first_error(source: &str) -> GoatError {
    match check_with_prelude(goat_checker::PRELUDE, source) {
        Ok(_) => panic!("should not check: {source}"),
        Err(errors) => errors.into_iter().next().expect("an error"),
    }
}

fn text(source: &str, span: Span) -> &str {
    &source[span.start..span.end]
}

fn assert_blames_element(source: &str, element: &str, use_site: &str) -> GoatError {
    let error = first_error(source);
    assert_eq!(text(source, error.span), element, "{error:?}");
    let note = error
        .labels
        .iter()
        .find(|l| l.message == NOTE)
        .unwrap_or_else(|| panic!("no use-site note: {error:?}"));
    assert_eq!(text(source, note.span), use_site, "{error:?}");
    error
}

#[test]
fn a_method_and_a_plain_function_blame_the_element() {
    let source = "xs = [{f: program(self) do 1 done}, {f: program(s) do 1 done}]\nlength(xs)";
    let error = assert_blames_element(source, "{f: program(s) do 1 done}", "length(xs)");
    assert_eq!(
        error.message,
        "`f` is a method in one record and a plain function in the other, so they don't have the same shape. \
         Start both with `self`, or neither."
    );
}

#[test]
fn a_string_among_numbers_blames_the_string() {
    assert_blames_element("xs = [1, 2, \"three\"]\nsum(xs)", "\"three\"", "sum(xs)");
}

#[test]
fn a_record_missing_a_field_blames_that_record() {
    let source = "xs = [{a: 1, b: 2}, {a: 3}]\nkeep(xs, program(r) do r.b > 0 done)";
    assert_blames_element(source, "{a: 3}", "keep(xs, program(r) do r.b > 0 done)");
}

#[test]
fn a_clash_inside_a_nested_list_blames_the_inner_element() {
    let source = "xs = [[1], [\"a\"]]\nlength(xs)";
    let error = first_error(source);
    assert_eq!(text(source, error.span), "\"a\"", "{error:?}");
}
