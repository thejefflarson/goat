//! The prelude is the chain of `Let`s the user's program is the `rest` of:
//! its names are in scope, its spans carry their file, and a diagnostic whose
//! root cause is in it is shown against the user's code.

use goat_checker::hir::{FileId, Span};
use goat_checker::{GoatError, PRELUDE, check, check_with_prelude};

const PRELUDE_SRC: &str = "double = program(n) do n * 2 done\n\
                           identity = program(x) do x done\n\
                           count_down = program(n) do if n < 1 then 0 else count_down(n - 1) done done\n";

fn type_of(prelude: &str, source: &str) -> Result<String, GoatError> {
    match check_with_prelude(prelude, source) {
        Ok(checked) => Ok(checked.typed.root_ty.to_string()),
        Err(mut errors) => Err(errors.remove(0)),
    }
}

fn warnings(prelude: &str, source: &str) -> Vec<GoatError> {
    check_with_prelude(prelude, source)
        .expect("checks")
        .typed
        .warnings
}

#[test]
fn the_embedded_prelude_checks_and_leaves_programs_alone() {
    let checked = check("").expect("empty program checks");
    assert!(checked.typed.warnings.is_empty());
    assert_eq!(check("1 + 2").unwrap().typed.root_ty.to_string(), "Number");
    assert!(
        check_with_prelude(PRELUDE, "x = 1 x").is_ok(),
        "the built-in prelude is a valid chain of definitions"
    );
}

#[test]
fn prelude_definitions_are_callable_from_user_code() {
    assert_eq!(type_of(PRELUDE_SRC, "double(21)").unwrap(), "Number");
    assert_eq!(type_of(PRELUDE_SRC, "count_down(3)").unwrap(), "Number");
}

#[test]
fn prelude_definitions_stay_polymorphic() {
    let src = "a = identity(1) b = identity(true) b";
    assert_eq!(type_of(PRELUDE_SRC, src).unwrap(), "Bool");
}

#[test]
fn prelude_names_are_unknown_without_the_prelude() {
    let err = type_of("", "double(21)").unwrap_err();
    assert!(err.message.contains("unknown name `double`"));
}

#[test]
fn an_empty_user_program_still_checks_under_a_prelude() {
    assert_eq!(type_of(PRELUDE_SRC, "").unwrap(), "Unit");
}

#[test]
fn user_spans_index_the_user_source_and_are_tagged_user() {
    let src = "x = 1\nidentity(true) + 1";
    let err = type_of(PRELUDE_SRC, src).unwrap_err();
    assert_eq!(err.span.file, FileId::User);
    assert_eq!(&src[err.span.start..err.span.end], "identity(true)");
}

#[test]
fn a_user_parse_error_is_not_blamed_on_the_prelude() {
    let err = type_of(PRELUDE_SRC, "1 +").unwrap_err();
    assert_eq!(err.span.file, FileId::User);
}

#[test]
fn a_prelude_parse_error_is_blamed_on_the_prelude() {
    let err = type_of("double = ", "1").unwrap_err();
    assert_eq!(err.span.file, FileId::Prelude);
}

#[test]
fn the_prelude_may_only_contain_definitions() {
    let err = type_of("1 + 2", "3").unwrap_err();
    assert_eq!(err.span.file, FileId::Prelude);
    assert!(err.message.contains("only contain definitions"));
}

#[test]
fn an_error_inside_the_prelude_is_marked_as_such_and_never_rendered_against_user_text() {
    let prelude = "bad = program(x) do x + true done\n";
    let user = "bad(1)";
    let err = type_of(prelude, user).unwrap_err();
    assert_eq!(err.span.file, FileId::Prelude);
    let rendered = err.render(user);
    assert!(rendered.starts_with("in the prelude, "), "{rendered}");
    assert!(!rendered.contains("bad(1)"), "{rendered}");
}

#[test]
fn a_prelude_error_is_presented_against_the_users_call_site() {
    let prelude = "bad = program(x) do x + true done\n";
    let user = "n = 5\nbad(n)";
    let err = type_of(prelude, user).unwrap_err();
    assert!(err.span.in_prelude());

    let call = Span::new(user.find("bad(n)").unwrap(), user.len());
    let shown = err.clone().at_call_site(call);
    assert_eq!(shown.span, call);
    assert_eq!(shown.message, err.message);
    let rendered = shown.render(user);
    assert!(rendered.starts_with("2:1: "), "{rendered}");
    assert!(rendered.contains("bad(n)"), "{rendered}");
}

#[test]
fn blaming_a_call_site_leaves_user_errors_where_they_are() {
    let user = "1 + true";
    let err = type_of(PRELUDE_SRC, user).unwrap_err();
    assert_eq!(err.span.file, FileId::User);
    let elsewhere = Span::new(0, 1);
    assert_eq!(err.clone().at_call_site(elsewhere), err);
}

#[test]
fn shadowing_a_prelude_name_warns_at_the_users_binding() {
    let user = "x = 1\ndouble = program(n) do n + n done\ndouble(x)";
    let warnings = warnings(PRELUDE_SRC, user);
    assert_eq!(warnings.len(), 1, "{warnings:?}");
    assert_eq!(warnings[0].span.file, FileId::User);
    assert_eq!(
        &user[warnings[0].span.start..warnings[0].span.end],
        "double"
    );
    assert_eq!(
        warnings[0].message,
        "`double` replaces the built-in `double`"
    );
}

#[test]
fn a_shadowing_value_binding_warns_and_the_user_binding_wins() {
    let user = "double = true double";
    assert_eq!(warnings(PRELUDE_SRC, user).len(), 1);
    assert_eq!(type_of(PRELUDE_SRC, user).unwrap(), "Bool");
}

#[test]
fn local_names_that_reuse_a_prelude_name_do_not_warn() {
    let user = "f = program(double) do double + 1 done f(1)";
    assert!(warnings(PRELUDE_SRC, user).is_empty());
    let user = "match Link(1, Empty) do Link(double, identity) then double Empty then 0 done";
    assert!(warnings(PRELUDE_SRC, user).is_empty());
}

#[test]
fn programs_that_avoid_prelude_names_do_not_warn() {
    assert!(warnings(PRELUDE_SRC, "twice = program(n) do n * 2 done twice(4)").is_empty());
}

#[test]
fn tags_the_prelude_constructs_are_not_reported_as_unmatched() {
    let prelude = "tag Oops make = program(n) do Oops(n) done\n";
    assert!(warnings(prelude, "tag Oops match make(1) do Oops(n) then n done").is_empty());
    assert!(warnings(prelude, "1").is_empty());
    let user = warnings(prelude, "tag Oops Oops(1)");
    assert_eq!(user.len(), 1);
    assert_eq!(user[0].span.file, FileId::User);
}

#[test]
fn prelude_definitions_cost_the_user_no_depth() {
    let prelude: String = (0..200).map(|i| format!("p{i} = {i}\n")).collect();
    let long: String = (0..300).map(|i| format!("q{i} = {i}\n")).collect();
    assert!(check_with_prelude(&prelude, &format!("{long} 1")).is_ok());
}
