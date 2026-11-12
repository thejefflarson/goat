//! A type error found where a helper is called also points at the code inside
//! the helper whose requirement failed.

use goat_checker::hir::Span;
use goat_checker::{GoatError, check_with_prelude};

fn errors_of(source: &str) -> Vec<GoatError> {
    match check_with_prelude("", source) {
        Ok(_) => panic!("should not check: {source}"),
        Err(errors) => errors,
    }
}

fn text(source: &str, span: Span) -> &str {
    &source[span.start..span.end]
}

fn assert_blames(source: &str, call: &str, origin: &str) {
    let errors = errors_of(source);
    assert!(!errors.is_empty());
    for error in &errors {
        assert_eq!(text(source, error.span), call, "{error:?}");
        assert_eq!(error.labels.len(), 1, "{error:?}");
        assert_eq!(text(source, error.labels[0].span), origin, "{error:?}");
    }
}

const METHOD_RETURN: &str = "step = program(p) do q = p.moved(); q.x done\n\
                             ball = {x: 1, moved: program(self) do self.x done}\n\
                             step(ball)";

#[test]
fn a_methods_return_shape_points_at_the_use_of_the_result() {
    assert_blames(METHOD_RETURN, "step(ball)", "q.x");
}

#[test]
fn a_missing_field_read_inside_a_helper_points_at_the_read() {
    let source = "getx = program(p) do p.x done\ngetx({y: 1})";
    assert_blames(source, "getx({y: 1})", "p.x");
}

#[test]
fn a_wrong_argument_count_inside_a_helper_points_at_the_inner_call() {
    let source = "h = program(f) do f(1, 2) done\nh(program(a) do a done)";
    assert_blames(source, "h(program(a) do a done)", "f(1, 2)");
}

#[test]
fn the_label_names_no_type_variable() {
    for error in errors_of(METHOD_RETURN) {
        let note = &error.labels[0].message;
        assert!(
            !note.contains('μ') && !note.contains(char::is_numeric),
            "{note}"
        );
    }
}

#[test]
fn the_label_renders_with_its_own_location() {
    let source = "getx = program(p) do p.x done\ngetx({y: 1})";
    let shown = errors_of(source)[0].render(source);
    assert!(
        shown.contains("2:1: record is missing field `x`"),
        "{shown}"
    );
    assert!(shown.contains("1:22: note: "), "{shown}");
    assert!(shown.contains("  getx = program(p) do p.x done"), "{shown}");
}

#[test]
fn errors_that_are_not_a_helpers_requirement_carry_no_label() {
    for source in [
        "forward = program(n) do n done\nforward(true) + 1",
        "x = {a: 1}\nx.b",
        "f = program(a, b) do a done\nf(1)",
        "if 1 do 2 else 3 done",
    ] {
        for error in errors_of(source) {
            assert!(error.labels.is_empty(), "{source}: {error:?}");
        }
    }
}

#[test]
fn a_call_whose_requirement_is_inside_it_adds_nothing() {
    let source = "(program(p) do p.x done)({y: 1})";
    for error in errors_of(source) {
        assert!(error.labels.is_empty(), "{error:?}");
    }
}
