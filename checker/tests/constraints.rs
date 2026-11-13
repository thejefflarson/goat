//! The built-in constraints: `==` needs a type with no function inside it,
//! `+ - * /` need numbers or records of numbers, and `print` takes anything.
//! A violation is a spanned error that says what went wrong in plain words.

use goat_checker::{Checked, GoatError, check_with_prelude};

fn check(source: &str) -> Result<Checked, Vec<GoatError>> {
    check_with_prelude("", source)
}

fn type_of(source: &str) -> Result<String, String> {
    match check(source) {
        Ok(checked) => Ok(checked.typed.root_ty.to_string()),
        Err(errors) => Err(errors[0].message.clone()),
    }
}

fn error_of(source: &str) -> String {
    type_of(source).expect_err("should not check")
}

#[test]
fn equality_works_on_anything_without_a_function() {
    for source in [
        "1 == 1",
        "true != false",
        "\"a\" == \"b\"",
        "{x: 1, y: true} == {x: 1, y: true}",
        "tag Circle Circle(1) == Circle(1)",
        "Empty == Link(1, Empty)",
        "{a: {b: [1, 2]}} == {a: {b: [1, 2]}}",
    ] {
        assert_eq!(type_of(source).unwrap(), "Bool", "{source}");
    }
}

#[test]
fn equality_has_the_lowest_precedence_of_the_comparisons() {
    assert_eq!(type_of("1 + 1 == 2").unwrap(), "Bool");
    assert_eq!(type_of("1 < 2 == true").unwrap(), "Bool");
    assert_eq!(type_of("1 < 2 != 2 < 1").unwrap(), "Bool");
}

#[test]
fn equality_needs_both_sides_to_have_the_same_type() {
    assert_eq!(
        error_of("1 == true"),
        "type mismatch: expected `Number`, found `Bool`"
    );
    assert_eq!(
        error_of("{x: 1} == {y: 1}"),
        "record has an unexpected field `y`"
    );
}

#[test]
fn comparing_functions_is_rejected_plainly() {
    let f = "f = program(x) do x done  g = program(x) do x done";
    assert_eq!(
        error_of(&format!("{f} f == g")),
        "can't compare functions with `==`"
    );
    assert_eq!(
        error_of(&format!("{f} f != g")),
        "can't compare functions with `!=`"
    );
}

#[test]
fn a_function_hidden_inside_a_value_is_found() {
    let f = "tag Wrap f = program(x) do x done  ";
    for source in [
        "{run: f} == {run: f}",
        "Wrap(f) == Wrap(f)",
        "{a: {b: f}} == {a: {b: f}}",
        "Link(f, Empty) == Link(f, Empty)",
    ] {
        let message = error_of(&format!("{f}{source}"));
        assert!(
            message.starts_with("can't compare `") && message.ends_with("it has a function inside"),
            "{source}: {message}"
        );
    }
}

#[test]
fn a_function_used_where_equality_is_demanded_later_is_found_at_the_call() {
    let src = "same = program(a, b) do a == b done  same(program(x) do x done, 1)";
    assert_eq!(error_of(src), "can't compare functions");
    let src = "same = program(a, b) do a == b done  same({f: program(x) do x done}, {f: 1})";
    assert!(
        error_of(src).contains("function inside"),
        "{}",
        error_of(src)
    );
}

#[test]
fn an_equality_function_is_polymorphic_over_eq_types() {
    let src = "same = program(a, b) do a == b done \
               x = same(1, 2)  y = same(\"a\", \"b\")  z = same({p: 1}, {p: 2}) \
               if x then y else z done";
    assert_eq!(type_of(src).unwrap(), "Bool");
    assert_eq!(
        type_of("program(a, b) do a == b done").unwrap(),
        "(t0, t0) -> Bool"
    );
}

#[test]
fn open_rows_inherit_the_equality_constraint() {
    let src = "tag Circle same = program(a, b) do a == b done  \
               same(Circle(1), Circle(2))";
    assert_eq!(type_of(src).unwrap(), "Bool");
    let src = "tag Circle pick = program(s) do match s do Circle(r) then s == s else false done done \
               pick(Circle(program(x) do x done))";
    assert_eq!(error_of(src), "can't compare functions");
}

#[test]
fn recursive_types_compare_when_their_elements_do() {
    let src = "same = program(a, b) do a == b done  same(Link(1, Empty), Link(2, Empty))";
    assert_eq!(type_of(src).unwrap(), "Bool");
    let src = "f = program(x) do x done  Link(f, Empty) == Link(f, Empty)";
    assert!(
        error_of(src).contains("function inside"),
        "{}",
        error_of(src)
    );
}

#[test]
fn arithmetic_still_types_plain_numbers() {
    assert_eq!(type_of("1 + 2 * 3 - 4 / 5").unwrap(), "Number");
    assert_eq!(type_of("-(2)").unwrap(), "Number");
    assert_eq!(type_of("(program(n) do n + 1 done)(2)").unwrap(), "Number");
    assert_eq!(
        type_of("program(n) do n + 1 done").unwrap(),
        "(Number) -> Number"
    );
}

#[test]
fn arithmetic_on_a_parameter_is_polymorphic_over_numeric_types() {
    assert_eq!(
        type_of("program(a, b) do a + b done").unwrap(),
        "(t0, t0) -> t0"
    );
    let src = "add = program(a, b) do a + b done  add({x: 1}, {x: 2})";
    assert_eq!(type_of(src).unwrap(), "{x: Number}");
    let src = "add = program(a, b) do a + b done  p = add(1, 2)  q = add({x: 1}, {x: 2})  p";
    assert_eq!(type_of(src).unwrap(), "Number");
}

#[test]
fn arithmetic_on_records_of_numbers() {
    assert_eq!(
        type_of("{x: 1, y: 2} + {x: 3, y: 4}").unwrap(),
        "{x: Number, y: Number}"
    );
    assert_eq!(
        type_of("{p: {x: 1}, n: 2} * {p: {x: 3}, n: 4}").unwrap(),
        "{p: {x: Number}, n: Number}"
    );
    assert_eq!(
        type_of("p = {x: 1, y: 2}  p - p").unwrap(),
        "{x: Number, y: Number}"
    );
}

#[test]
fn arithmetic_on_something_else_says_what_it_needs() {
    assert_eq!(
        error_of("true + 1"),
        "`+` needs numbers or records of numbers, but this is `Bool`"
    );
    assert_eq!(
        error_of("\"a\" * 2"),
        "`*` needs numbers or records of numbers, but this is `String`"
    );
    assert_eq!(
        error_of("tag Circle Circle(1) - Circle(2)")
            .split(", but")
            .next()
            .unwrap(),
        "`-` needs numbers or records of numbers"
    );
}

#[test]
fn arithmetic_on_a_record_with_a_non_numeric_field_is_rejected() {
    assert_eq!(
        error_of("{x: 1, y: true} + {x: 1, y: true}"),
        "`+` needs numbers or records of numbers, but this is `{x: Number, y: Bool}`"
    );
    assert_eq!(
        error_of("{n: {s: \"a\"}} / {n: {s: \"b\"}}"),
        "`/` needs numbers or records of numbers, but this is `{n: {s: String}}`"
    );
}

#[test]
fn a_number_and_a_record_do_not_mix() {
    assert_eq!(
        error_of("{x: 1} + 1"),
        "type mismatch: expected `{x: Number}`, found `Number`"
    );
    assert_eq!(
        error_of("1 + true"),
        "type mismatch: expected `Number`, found `Bool`"
    );
    assert_eq!(
        error_of("{x: 1} + {y: 1}"),
        "record has an unexpected field `y`"
    );
}

#[test]
fn a_record_that_turns_out_non_numeric_later_is_found_at_the_call() {
    let src = "add = program(a, b) do a + b done  add({x: true}, {x: false})";
    assert_eq!(
        error_of(src),
        "arithmetic needs numbers or records of numbers, but this is `{x: Bool}`"
    );
    let src = "double = program(p) do p + p done  double(\"hi\")";
    assert_eq!(
        error_of(src),
        "arithmetic needs numbers or records of numbers, but this is `String`"
    );
}

#[test]
fn field_access_keeps_a_numeric_operand_numeric() {
    let src = "norm = program(p) do p.x * p.x + p.y * p.y done  norm({x: 3, y: 4})";
    assert_eq!(type_of(src).unwrap(), "Number");
    let src = "norm = program(p) do p.x * p.x done  norm({x: true})";
    assert!(error_of(src).contains("needs numbers"), "{}", error_of(src));
}

#[test]
fn ordering_works_on_anything_without_a_function() {
    for source in [
        "1 < 2",
        "1 <= 2.5",
        "\"apple\" < \"banana\"",
        "false < true",
        "{x: 1, y: 2} >= {x: 1, y: 3}",
        "tag Small | Large  Small < Large",
        "[1, 2] > [1]",
        "{a: [\"x\"], b: true} <= {a: [\"x\"], b: false}",
    ] {
        assert_eq!(type_of(source).unwrap(), "Bool", "{source}");
    }
}

#[test]
fn ordering_needs_both_sides_to_have_the_same_type() {
    assert_eq!(
        error_of("\"a\" < 1"),
        "type mismatch: expected `String`, found `Number`"
    );
    assert_eq!(
        error_of("{x: 1} < 2"),
        "type mismatch: expected `{x: Number}`, found `Number`"
    );
}

#[test]
fn ordering_a_function_is_an_error_that_names_the_comparison() {
    let f = "f = program(x) do x done  ";
    assert_eq!(
        error_of(&format!("{f}f < f")),
        "can't compare functions with `<`"
    );
    assert_eq!(
        error_of("a = {x: 1, f: program(n) do n + 1 done}  a < a"),
        "can't compare `{x: Number, f: (Number) -> Number}` with `<`: it has a function inside"
    );
}

#[test]
fn a_function_used_where_ordering_is_demanded_later_is_found_at_the_call() {
    let src = "least = program(a, b) do if a < b then a else b done done  ";
    assert_eq!(type_of(&format!("{src}least(2, 1)")).unwrap(), "Number");
    assert_eq!(
        type_of(&format!("{src}least(\"b\", \"a\")")).unwrap(),
        "String"
    );
    assert_eq!(
        error_of(&format!("{src}least(program(x) do x done, 1)")),
        "can't compare functions"
    );
}

#[test]
fn print_takes_any_one_value_and_returns_unit() {
    for source in [
        "print(1)",
        "print(\"hi\")",
        "print({x: 1})",
        "tag Circle print(Circle(1))",
        "print([1, 2])",
        "print(program(x) do x done)",
    ] {
        assert_eq!(type_of(source).unwrap(), "Unit", "{source}");
    }
    assert_eq!(type_of("print").unwrap(), "(t0) -> Unit");
    assert_eq!(
        error_of("print(1, 2)"),
        "function expects 1 argument(s) but got 2"
    );
}

#[test]
fn print_is_an_ordinary_function_value() {
    let src = "apply = program(f, x) do f(x) done  apply(print, 1)";
    assert_eq!(type_of(src).unwrap(), "Unit");
}

#[test]
fn a_user_definition_replaces_print_with_a_warning() {
    let checked = check("print = program(x) do x done  print(1)").expect("checks");
    assert_eq!(checked.typed.root_ty.to_string(), "Number");
    assert_eq!(
        checked.typed.warnings[0].message,
        "`print` replaces the built-in `print`"
    );
}

#[test]
fn equality_errors_are_spanned_at_the_comparison() {
    let source = "f = program(x) do x done  f == f";
    let errors = check(source).err().expect("rejected");
    let span = errors[0].span;
    assert_eq!(&source[span.start..span.end], "f == f");
}

#[test]
fn arithmetic_errors_are_spanned_at_the_operand() {
    let source = "x = 1  true + x";
    let errors = check(source).err().expect("rejected");
    let span = errors[0].span;
    assert_eq!(&source[span.start..span.end], "true");
}

#[test]
fn spread_recursion_that_only_adds_a_field_checks() {
    assert!(type_of("go = program(s) do go({...s, stop: true}) done  1").is_ok());
    assert!(type_of("go = program(s) do go({...s, a: 1, b: true}) done  1").is_ok());
}

#[test]
fn spread_recursion_that_reads_a_field_still_checks() {
    let source =
        "go = program(s) do if s.n == 0 then s.n else go({...s, n: s.n - 1}) done done  go({n: 3})";
    assert_eq!(type_of(source).unwrap(), "Number");
}

#[test]
fn other_infinite_record_types_stay_rejected() {
    let message = error_of("f = program(s) do f({a: {...s, b: 1}}) done  1");
    assert!(message.contains("contain itself"), "{message}");
}
