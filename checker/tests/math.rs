//! The prelude's math: `round`, `floor`, `ceil` and `truncate` are the only way
//! from a `Float` to an `Int`, and trig and `sqrt` give a `Float` (ADR 0017).

use goat_checker::check;

fn exact_type_of(source: &str) -> Result<String, String> {
    match check(source) {
        Ok(checked) => Ok(checked.typed.root_ty.exact().to_string()),
        Err(errors) => Err(errors[0].message.clone()),
    }
}

#[test]
fn a_float_becomes_an_int_through_round_floor_ceil_and_truncate() {
    for function in ["round", "floor", "ceil", "truncate"] {
        for argument in ["2.5", "3", "1 / 3"] {
            let source = format!("{function}({argument})");
            assert_eq!(exact_type_of(&source).as_deref(), Ok("Int"), "{source}");
        }
        assert_eq!(
            exact_type_of(&format!("{function}(7 // 2)")).as_deref(),
            Ok("Int")
        );
    }
}

#[test]
fn a_float_is_never_an_int_without_one_of_them() {
    let take = "take = foreign \"m\" \"take\" (Int) -> Unit\n";
    assert_eq!(
        exact_type_of(&format!("{take}take(2.5)")).unwrap_err(),
        "type mismatch: expected `Int`, found `Float`"
    );
    assert_eq!(
        exact_type_of(&format!("{take}take(round(2.5))")).as_deref(),
        Ok("Unit")
    );
    let message = exact_type_of("7 // (3 / 2)").unwrap_err();
    assert!(message.contains("needs whole numbers"), "{message}");
    assert_eq!(exact_type_of("7 // round(3 / 2)").as_deref(), Ok("Int"));
}

#[test]
fn the_rounding_functions_are_values_from_float_to_int() {
    for function in ["round", "floor", "ceil", "truncate"] {
        let list = exact_type_of(&format!("change_each([1.5, 2.5], {function})")).unwrap();
        assert!(list.contains("0: Int"), "{function}: {list}");
        assert!(!list.contains("Float"), "{function}: {list}");
    }
}

#[test]
fn trig_and_sqrt_give_a_float() {
    for function in ["sin", "cos", "tan", "sqrt"] {
        for argument in ["30", "30.5", "7 // 2"] {
            let source = format!("{function}({argument})");
            assert_eq!(exact_type_of(&source).as_deref(), Ok("Float"), "{source}");
        }
    }
    assert_eq!(exact_type_of("sin(30) + 1").as_deref(), Ok("Float"));
}

#[test]
fn the_turtles_angle_and_division_math_checks() {
    let circle = "sides = 36
side = 2 * 100 * sin(180 / sides)
turn = 360 // sides
for i from 1 to sides do forward(side); right(turn) done";
    assert_eq!(exact_type_of(circle).as_deref(), Ok("Unit"));
    assert_eq!(
        exact_type_of("right(90 % 360); forward(10 // 3)").as_deref(),
        Ok("Unit")
    );
    assert_eq!(
        exact_type_of("for i from 1 to 3 do forward(sqrt(i)); right(i) done").as_deref(),
        Ok("Unit")
    );
}
