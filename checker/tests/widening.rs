//! An `Int` widens to a `Float` where two scalars must agree (ADR 0040), and
//! the answer does not depend on the order the checker met the code in.

use goat_checker::check_with_prelude;

fn check(source: &str) -> Result<String, (String, String)> {
    match check_with_prelude(goat_checker::PRELUDE, source) {
        Ok(checked) => Ok(checked.typed.root_ty.exact().to_string()),
        Err(errors) => {
            let error = &errors[0];
            Err((
                error.message.clone(),
                source[error.span.start..error.span.end].to_string(),
            ))
        }
    }
}

fn type_of(source: &str) -> String {
    check(source).unwrap_or_else(|e| panic!("{source}\n{e:?}"))
}

fn error_of(source: &str) -> (String, String) {
    check(source).expect_err(source)
}

const WHOLE: &str = "whole = foreign \"m\" \"whole\" () -> Int\n\
                     take = foreign \"m\" \"take\" (Int) -> Int\n";

fn with_count(source: &str) -> String {
    format!("{WHOLE}{source}")
}

fn assert_all(sources: &[&str], expected: &str) {
    for source in sources {
        assert_eq!(type_of(&with_count(source)), expected, "{source}");
    }
}

#[test]
fn operands_of_every_operator_widen() {
    for op in ["+", "-", "*", "//", "%"] {
        let source = format!("whole() {op} 2.5");
        assert_all(&[&source, &format!("2.5 {op} whole()")], "Float");
    }
    assert_all(&["whole() / 2", "2 / whole()"], "Float");
}

#[test]
fn comparisons_widen() {
    for op in ["==", "!=", "<", "<=", ">", ">="] {
        let source = format!("whole() {op} 2.5");
        assert_all(&[&source, &format!("2.5 {op} whole()")], "Bool");
    }
}

#[test]
fn a_call_to_a_generic_function_widens_its_arguments_in_either_order() {
    let add = "f = program(a, b) do a + b done  ";
    assert_all(
        &[
            &format!("{add}f(whole(), 2.5)"),
            &format!("{add}f(2.5, whole())"),
        ],
        "Float",
    );
    assert_eq!(
        type_of(&with_count(&format!("{add}f(whole(), whole())"))),
        "Int"
    );
}

#[test]
fn an_argument_widens_to_a_float_parameter() {
    assert_all(
        &[
            "g = program(x) do sqrt(x) done  g(whole())",
            "sqrt(whole())",
            "g = program(x) do x + 1.5 done  g(whole())",
        ],
        "Float",
    );
}

#[test]
fn the_branches_of_an_if_widen_in_either_order() {
    assert_all(
        &[
            "c = true  if c then whole() else 2.5 done",
            "c = true  if c then 2.5 else whole() done",
            "c = true  if c then 1 else if c then whole() else 2.5 done done",
        ],
        "Float",
    );
}

#[test]
fn the_arms_of_a_match_widen_in_either_order() {
    assert_all(
        &[
            "match [whole()] do [x, ...r] then x [] then 2.5 done",
            "match [whole()] do [] then 2.5 [x, ...r] then x done",
        ],
        "Float",
    );
}

#[test]
fn the_elements_of_a_list_literal_widen_in_either_order() {
    for source in ["i = whole()  [i, 2.5]", "i = whole()  [2.5, i]"] {
        let ty = type_of(&with_count(source));
        assert!(
            ty.contains("[Empty, Link: {0: Float, 1: t"),
            "{source}: {ty}"
        );
    }
    assert_eq!(
        type_of(&with_count("i = whole()  sum([2.5, i, 3])")),
        "Float"
    );
    assert_eq!(type_of(&with_count("i = whole()  sum([i, 3])")), "Int");
}

#[test]
fn an_int_pushed_onto_a_float_list_widens() {
    assert_eq!(
        type_of(&with_count("xs = [1.5, 2.5]  sum(Link(whole(), xs))")),
        "Float"
    );
}

#[test]
fn a_free_parameter_takes_the_join_in_either_order() {
    assert_all(
        &[
            "program(p) do {a: whole() + p, b: p + 1.5} done",
            "program(p) do {a: p + whole(), b: 1.5 + p} done",
        ],
        "(Float) -> {a: Float, b: Float}",
    );
    assert_all(
        &["program(p) do {b: p + 1.5, a: whole() + p} done"],
        "(Float) -> {b: Float, a: Float}",
    );
}

#[test]
fn a_computed_number_is_the_same_number_in_either_order() {
    for source in [
        "n = 2 * 3  {a: n + 1.5, b: n // 2}",
        "n = 2 * 3  {b: n // 2, a: n + 1.5}",
    ] {
        let ty = type_of(source);
        assert!(ty.contains("a: Float") && ty.contains("b: Float"), "{ty}");
    }
}

#[test]
fn a_recursive_group_is_solved_as_one() {
    let source = "f = program(a, n) do if n == 0 then a else g(a, n - 1) + 1.5 done done \
                  g = program(b, n) do if n == 0 then b else f(b, n - 1) done done \
                  f(whole(), 3)";
    assert_all(&[source], "Float");
}

#[test]
fn a_binding_inside_a_function_is_solved_before_it_generalizes() {
    let source = "f = program(a, b) do \
                    inner = program(x) do x + a done \
                    inner(b) \
                  done \
                  f(whole(), 2.5)";
    assert_all(&[source], "Float");
}

#[test]
fn a_float_where_an_int_is_needed_names_the_way_out() {
    for source in [
        "f = program(a) do take(a + 2.5) done  f",
        "f = program(a) do take(2.5 + a) done  f",
        "take(first(Link(2.5, [whole()])))",
        "take(first(Link(whole(), [2.5])))",
    ] {
        let (message, at) = error_of(&with_count(source));
        assert_eq!(
            message,
            "this is a `Float`, but an `Int` is needed here; use `round`, `floor` or `truncate`",
            "{source}"
        );
        assert_eq!(at, "2.5", "{source}");
    }
}

#[test]
fn a_float_the_call_site_already_knows_is_a_plain_mismatch() {
    let (message, _) = error_of(&with_count("take(2.5)"));
    assert_eq!(message, "type mismatch: expected `Int`, found `Float`");
}

#[test]
fn nothing_widens_under_a_constructor() {
    let wants_float = "h = program(p) do p.a + 1.5 done  ";
    for source in [
        format!("{wants_float}h({{a: whole()}})"),
        "{x: whole()} + {x: 1.5}".to_string(),
        "total = program(xs) do match xs do [] then 0.5 [x, ...r] then x + 1.5 done done  \
         make = program() do [whole()] done  total(make())"
            .to_string(),
        "if true then {a: whole()} else {a: 2.5} done".to_string(),
    ] {
        let (message, _) = error_of(&with_count(&source));
        assert!(message.contains("expected"), "{source}\n{message}");
    }
}

#[test]
fn the_principality_corner_closes_to_the_float() {
    // Full subtyping would keep `a` an `Int`; closing the edge between two free
    // variables by unification makes it a `Float`. Calls are accepted either way.
    assert_eq!(
        type_of("f = program(c, i) do {a: i, b: if c then i else 1.5 done} done  f"),
        "(Bool, Float) -> {a: Float, b: Float}"
    );
}

#[test]
fn a_list_literal_still_open_when_it_is_used_adapts_to_the_use() {
    // The literal's elements are a join site, and a computed `xs = [whole()]`
    // keeps its element type open until the program's flows are solved, so a
    // use that needs `Float`s gets them. A list built by a function is exact.
    let total = "total = program(xs) do match xs do [] then 0.5 [x, ...r] then x + 1.5 done done  ";
    assert_all(&[&format!("{total}total([whole()])")], "Float");
}

#[test]
fn an_operator_result_joined_later_with_a_float_checks() {
    let source = "f = program(c, x) do \
                    p = if c then truncate(x) else 0 done \
                    r = if c then {x: p + p} else {x: 1.5} done \
                    r.x \
                  done \
                  f(true, 2.5)";
    assert_eq!(type_of(source), "Float");
}
