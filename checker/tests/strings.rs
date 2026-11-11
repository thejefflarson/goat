//! `byte_length` and `byte_at` read a string's UTF-8 bytes and give `Int`s.

use goat_checker::check;

fn exact_type_of(source: &str) -> Result<String, String> {
    match check(source) {
        Ok(checked) => Ok(checked.typed.root_ty.exact().to_string()),
        Err(errors) => Err(errors[0].message.clone()),
    }
}

#[test]
fn the_byte_functions_give_ints() {
    assert_eq!(exact_type_of("byte_length(\"hi\")").as_deref(), Ok("Int"));
    assert_eq!(exact_type_of("byte_at(\"hi\", 1)").as_deref(), Ok("Int"));
    assert_eq!(
        exact_type_of("byte_length(\"hi\") + byte_at(\"hi\", 2)").as_deref(),
        Ok("Int")
    );
}

#[test]
fn a_position_is_an_int_so_a_counter_works() {
    assert_eq!(
        exact_type_of("for i from 1 to 2 do byte_at(\"hi\", i) done").as_deref(),
        Ok("Unit")
    );
}

#[test]
fn only_a_string_has_bytes() {
    assert_eq!(
        exact_type_of("byte_length(3)"),
        Err("type mismatch: expected `String`, found `Number`".to_string())
    );
    assert_eq!(
        exact_type_of("byte_at(true, 1)"),
        Err("type mismatch: expected `String`, found `Bool`".to_string())
    );
}

#[test]
fn a_position_is_not_a_string_or_a_float() {
    assert!(exact_type_of("byte_at(\"hi\", \"1\")").is_err());
    assert!(exact_type_of("byte_at(\"hi\", 1.5)").is_err());
}

#[test]
fn char_count_gives_an_int_and_char_at_a_string() {
    assert_eq!(exact_type_of("char_count(\"hi\")").as_deref(), Ok("Int"));
    assert_eq!(exact_type_of("char_at(\"hi\", 1)").as_deref(), Ok("String"));
    assert_eq!(
        exact_type_of("char_at(\"hi\", 1) == \"h\"").as_deref(),
        Ok("Bool")
    );
    assert_eq!(
        exact_type_of("for i from 1 to 2 do char_at(\"hi\", i) done").as_deref(),
        Ok("Unit")
    );
}

#[test]
fn the_character_functions_reject_misuse() {
    assert_eq!(
        exact_type_of("char_count(3)"),
        Err("type mismatch: expected `String`, found `Number`".to_string())
    );
    assert_eq!(
        exact_type_of("char_at(true, 1)"),
        Err("type mismatch: expected `String`, found `Bool`".to_string())
    );
    assert!(exact_type_of("char_at(\"hi\", \"1\")").is_err());
    assert!(exact_type_of("char_at(\"hi\", 1.5)").is_err());
    assert_eq!(
        exact_type_of("char_at(\"hi\")"),
        Err("function expects 2 argument(s) but got 1".to_string())
    );
    assert!(exact_type_of("char_at(\"hi\", 1) + 1").is_err());
}

#[test]
fn byte_at_needs_both_arguments() {
    assert_eq!(
        exact_type_of("byte_at(\"hi\")"),
        Err("function expects 2 argument(s) but got 1".to_string())
    );
}
