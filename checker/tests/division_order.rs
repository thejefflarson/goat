//! `/` is decided like `+`: after its operands' types settle, so the order the
//! operands are met in cannot change whether a program types (ADR 0012).

use goat_checker::check;

fn exact_type_of(source: &str) -> Result<String, String> {
    match check(source) {
        Ok(checked) => Ok(checked.typed.root_ty.exact().to_string()),
        Err(errors) => Err(errors[0].message.clone()),
    }
}

#[test]
fn a_function_dividing_open_operands_takes_a_record_in_either_statement_order() {
    let record = "{x: Float}";
    for source in [
        "(program(a) do a / a done)({x: 1.0})",
        "f = program(a) do a / a done\nf({x: 1.0})",
        "{x: 1.0} / {x: 3.0}",
        "a = {x: 1.0}\nf = program(b) do b / b done\nf(a)",
        "f = program(a, b) do a / b done\nf({x: 1.0}, {x: 2.0})",
    ] {
        assert_eq!(exact_type_of(source).as_deref(), Ok(record), "{source}");
    }
}

#[test]
fn a_function_dividing_open_operands_takes_a_float() {
    for source in [
        "(program(a) do a / a done)(2.0)",
        "f = program(a) do a / a done\nf(2.0)",
        "f = program(a, b) do a / b done\nf(1.0, 2.0)",
    ] {
        assert_eq!(exact_type_of(source).as_deref(), Ok("Float"), "{source}");
    }
}

#[test]
fn one_function_divides_floats_and_records() {
    let source = "f = program(a) do a / a done\n{p: f(2.0), q: f({x: 1.0})}";
    assert_eq!(
        exact_type_of(source).as_deref(),
        Ok("{p: Float, q: {x: Float}}")
    );
}

#[test]
fn a_numeral_in_a_quotient_record_is_a_float() {
    for source in ["{x: 9} / {x: 3}", "f = program(a) do a / a done\nf({x: 1})"] {
        assert_eq!(
            exact_type_of(source).as_deref(),
            Ok("{x: Float}"),
            "{source}"
        );
    }
}

#[test]
fn a_function_dividing_open_operands_is_polymorphic_in_the_quotient_type() {
    assert_eq!(
        exact_type_of("program(a) do a / a done").as_deref(),
        Ok("(t0) -> t0")
    );
}

#[test]
fn a_quotient_of_a_record_and_a_number_is_refused_in_either_order() {
    for source in [
        "{x: 1.0} / 2.0",
        "2.0 / {x: 2.0}",
        "f = program(a) do a / 1.0 done\nf({x: 1.0})",
        "f = program(a) do 1.0 / a done\nf({x: 1.0})",
    ] {
        let error = exact_type_of(source).expect_err(source);
        assert!(error.contains("expected"), "{source}: {error}");
    }
}

#[test]
fn an_int_field_is_refused_where_a_quotient_type_is_needed() {
    assert_eq!(
        exact_type_of("{x: round(2.5)} / {x: round(1.5)}").unwrap_err(),
        "type mismatch: expected `Float`, found `Int`"
    );
    assert_eq!(
        exact_type_of("f = program(a) do a / a done\nf({x: round(2.5)})").unwrap_err(),
        "arithmetic needs numbers or records of numbers, but this is `{x: Number}`"
    );
}
