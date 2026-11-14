//! The list functions in the prelude type-check against any element type, and
//! misuse is a spanned error in the user's code.

use goat_checker::check;
use goat_checker::hir::FileId;

fn type_of(source: &str) -> Result<String, String> {
    match check(source) {
        Ok(checked) => Ok(checked.typed.root_ty.to_string()),
        Err(errors) => Err(errors[0].message.clone()),
    }
}

#[test]
fn functions_that_answer_with_a_plain_value() {
    for (source, ty) in [
        ("length([1])", "Number"),
        ("length([\"a\", \"b\"])", "Number"),
        ("length([])", "Number"),
        ("item([\"a\"], 1)", "String"),
        ("item([true], 1)", "Bool"),
        ("first([true])", "Bool"),
        ("first([\"a\"])", "String"),
        ("first([{x: 1}])", "{x: Number}"),
        ("each([1], print)", "Unit"),
        ("each([\"a\"], print)", "Unit"),
        ("count([1], program(n) do n > 1 done)", "Number"),
        ("sum([1])", "Number"),
        ("biggest([1])", "Number"),
        ("smallest([1])", "Number"),
        ("has([\"a\"], \"a\")", "Bool"),
        ("has([{x: 1}], {x: 1})", "Bool"),
        ("has([[1]], [1])", "Bool"),
    ] {
        assert_eq!(type_of(source).as_deref(), Ok(ty), "{source}");
    }
}

#[test]
fn functions_that_answer_with_a_list_keep_the_element_type() {
    for (source, element) in [
        ("link(1, [])", "Number"),
        ("link(\"a\", [\"b\"])", "String"),
        ("add([true], false)", "Bool"),
        ("join([\"a\"], [\"b\"])", "String"),
        ("reverse([true])", "Bool"),
        ("rest([\"a\", \"b\"])", "String"),
        ("sort([2, 1])", "Number"),
        ("keep([\"a\"], program(s) do s == \"a\" done)", "String"),
        ("change_each([1], program(n) do n > 1 done)", "Bool"),
        ("change_each([true], program(b) do 1 done)", "Number"),
    ] {
        let ty = type_of(source).unwrap();
        assert!(ty.contains(&format!("{{0: {element}")), "{source} :: {ty}");
    }
}

#[test]
fn one_function_serves_several_element_types_in_one_program() {
    let src = "a = first([\"a\"])\n\
               b = first([1])\n\
               c = reverse([true])\n\
               d = reverse([1])\n\
               length(c) + length(d) + length(join([a], [a])) + b";
    assert_eq!(type_of(src).as_deref(), Ok("Number"));
}

#[test]
fn results_feed_back_into_the_list_functions() {
    for source in [
        "length(rest(rest([1, 2, 3])))",
        "first(add(link(0, [1]), 2))",
        "sum(change_each(keep([1, 2, 3], program(n) do n > 1 done), program(n) do n * 2 done))",
        "item(sort(join([3], [1, 2])), 1)",
        "has(reverse([1]), first([1]))",
    ] {
        assert!(type_of(source).is_ok(), "{source}: {:?}", type_of(source));
    }
}

#[test]
fn numeric_functions_reject_other_elements() {
    for (source, found) in [("sum([\"a\"])", "String"), ("sum([true])", "Bool")] {
        assert_eq!(
            type_of(source).unwrap_err(),
            format!("type mismatch: expected `Number`, found `{found}`"),
            "{source}"
        );
    }
}

#[test]
fn ordering_functions_take_anything_without_a_function() {
    for source in [
        "sort([\"b\", \"a\"])",
        "biggest([true, false])",
        "smallest([{x: 1}, {x: 0}])",
        "insert_sorted(\"b\", [\"a\", \"c\"], [])",
    ] {
        assert!(type_of(source).is_ok(), "{source}");
    }
    assert_eq!(
        type_of("sort([print])").unwrap_err(),
        "can't compare functions"
    );
}

#[test]
fn has_cannot_compare_functions() {
    assert_eq!(
        type_of("has([print], print)").unwrap_err(),
        "can't compare functions"
    );
}

#[test]
fn argument_types_must_line_up() {
    assert_eq!(
        type_of("join([1], [true])").unwrap_err(),
        "type mismatch: expected `Number`, found `Bool`"
    );
    assert_eq!(
        type_of("item([1], true)").unwrap_err(),
        "type mismatch: expected `Number`, found `Bool`"
    );
    assert!(type_of("keep([1], 3)").is_err());
    assert!(type_of("each([1], 3)").is_err());
    assert!(type_of("first(1)").is_err());
    assert!(type_of("length(\"abc\")").is_err());
}

#[test]
fn a_misused_function_is_blamed_on_the_users_call() {
    let src = "x = 1\nsum([\"a\"])";
    let errors = check(src).err().expect("sum of strings is an error");
    assert_eq!(errors[0].span.file, FileId::User);
    assert!(
        src[errors[0].span.start..errors[0].span.end].contains("\"a\""),
        "{:?}",
        errors[0]
    );
}

#[test]
fn trap_stops_the_program_and_fits_any_type() {
    assert!(type_of("trap(\"stop\")").is_ok());
    assert_eq!(type_of("1 + trap(\"stop\")").as_deref(), Ok("Number"));
    assert_eq!(
        type_of("if true then 1 else trap(\"stop\") done").as_deref(),
        Ok("Number")
    );
}

#[test]
fn trap_needs_a_literal_message() {
    let message = "`trap` takes one message, written out in quotes";
    for source in [
        "trap(1)",
        "trap()",
        "trap(\"a\", \"b\")",
        "s = \"a\"  trap(s)",
    ] {
        assert_eq!(type_of(source).unwrap_err(), message, "{source}");
    }
    assert!(
        type_of("a = trap")
            .unwrap_err()
            .contains("call it with a message")
    );
}

#[test]
fn a_user_definition_of_trap_wins() {
    assert_eq!(
        type_of("trap = program(x) do x done  trap(1)").as_deref(),
        Ok("Number")
    );
}

#[test]
fn the_list_functions_are_just_prelude_names_users_may_replace() {
    let src = "first = program(xs) do 7 done\nfirst([])";
    let checked = check(src).unwrap();
    assert_eq!(checked.typed.root_ty.to_string(), "Number");
    assert_eq!(checked.typed.warnings.len(), 1);
}
