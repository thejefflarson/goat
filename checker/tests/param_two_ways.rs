//! A function passed in has one type, so using it two ways says what was found
//! and how to name the function so each use gets its own type.

use goat_checker::{GoatError, check};

fn first_error(source: &str) -> GoatError {
    match check(source) {
        Ok(_) => panic!("should not check: {source}"),
        Err(mut errors) => errors.remove(0),
    }
}

fn text(source: &str, span: goat_checker::hir::Span) -> &str {
    &source[span.start..span.end]
}

#[test]
fn a_function_literal_at_the_call_is_quoted_in_the_suggestion() {
    let source = "(program(f) do {a: f(1), b: f(true)} done)(program(x) do x done)";
    let error = first_error(source);
    assert_eq!(
        error.message,
        "`f` gets a Number here and a Bool there, but a function you pass in can only take one kind of thing.\n\
         Give the function a name first, then use it both ways:\n\
         ```\n\
         f = program(x) do x done\n\
         {a: f(1), b: f(true)}\n\
         ```"
    );
    assert_eq!(text(source, error.span), "f(true)");
    let notes: Vec<_> = error
        .labels
        .iter()
        .map(|l| (text(source, l.span), l.message.as_str()))
        .collect();
    assert_eq!(
        notes,
        [
            ("f(1)", "`f` gets a Number here"),
            ("f(true)", "`f` gets a Bool here")
        ]
    );
}

#[test]
fn a_long_function_literal_is_elided_in_the_suggestion() {
    let source = "(program(f) do\n a = f(1)\n b = f(true)\n {a: a, b: b} done)(program(x) do\n y = x\n y done)";
    let message = first_error(source).message;
    assert!(
        message.ends_with("```\nf = program(x) do … done\n…\n```"),
        "{message}"
    );
}

#[test]
fn a_named_helper_suggests_a_function_for_each_kind() {
    let source = "use_twice = program(f) do {a: f(1), b: f(true)} done\n\
                  use_twice(program(x) do x done)";
    let error = first_error(source);
    assert_eq!(
        error.message,
        "`f` gets a Number here and a Bool there, but a function you pass in can only take one kind of thing.\n\
         Pass a separate function for each kind, or give the function a name with `=` where you use it."
    );
    assert_eq!(text(source, error.span), "f(true)");
    assert_eq!(error.labels.len(), 2);
}

#[test]
fn records_are_named_as_the_type_printer_names_them() {
    let error =
        first_error("use2 = program(g) do a = g({x: 1})\n b = g({x: 2, y: 3})\n b done use2(1)");
    assert!(
        error.message.starts_with(
            "`g` gets `{x: Number}` here and `{x: Number, y: Number}` there, but a function"
        ),
        "{}",
        error.message
    );
}

#[test]
fn a_field_of_a_parameter_used_two_ways_says_a_value() {
    let error =
        first_error("use = program(m) do a = m.id + 1\n if m.id then 1 else 2 done done use(1)");
    assert_eq!(
        error.message,
        "`m.id` gets a Number here and a Bool there, but a value you pass in can only be one kind of thing.\n\
         Pass a separate value for each kind, or give it a name with `=` where you use it."
    );
    assert_eq!(error.labels.len(), 2);
}
