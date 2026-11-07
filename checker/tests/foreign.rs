//! `foreign` declarations: a host function's type is written out, and only the
//! boundary types (Number, Bool, Unit, String) may appear in it.

use goat_checker::hir::{Boundary, ExprKind};
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

fn errors_of(source: &str) -> Vec<GoatError> {
    match check(source) {
        Ok(_) => panic!("should not check: {source}"),
        Err(errors) => errors,
    }
}

fn error_of(source: &str) -> String {
    type_of(source).expect_err("should not check")
}

#[test]
fn a_call_has_the_declared_result_type() {
    for (signature, call, ty) in [
        ("(Number) -> Unit", "f(1)", "Unit"),
        ("(Bool, String) -> Number", "f(true, \"s\")", "Number"),
        ("() -> Bool", "f()", "Bool"),
        ("(Unit) -> String", "f(f2())", "String"),
        ("(Number, Number,) -> Number", "f(1, 2)", "Number"),
    ] {
        let source = format!(
            "f2 = foreign \"m\" \"f2\" () -> Unit\nf = foreign \"m\" \"f\" {signature}\n{call}"
        );
        assert_eq!(type_of(&source).as_deref(), Ok(ty), "{source}");
    }
}

#[test]
fn the_scheme_is_fixed_and_not_generalized() {
    let checked = check("f = foreign \"turtle\" \"forward\" (Number) -> Unit f(1)").unwrap();
    let scheme = checked
        .typed
        .schemes
        .values()
        .next()
        .expect("f has a scheme");
    assert!(scheme.vars.is_empty());
    assert_eq!(scheme.ty.to_string(), "(Number) -> Unit");
}

#[test]
fn a_foreign_declaration_lowers_to_a_let_of_a_foreign_node() {
    let checked = check("f = foreign \"turtle\" \"forward\" (Number, Bool) -> String f").unwrap();
    let ExprKind::Let { value, .. } = &checked.root.kind else {
        panic!("a declaration is a let");
    };
    let ExprKind::Foreign {
        module,
        name,
        params,
        ret,
    } = &value.kind
    else {
        panic!("the value is a foreign node");
    };
    assert_eq!((module.as_str(), name.as_str()), ("turtle", "forward"));
    assert_eq!(params, &[Boundary::Number, Boundary::Bool]);
    assert_eq!(*ret, Boundary::Str);
}

#[test]
fn calls_are_checked_against_the_declared_types() {
    let decl = "forward = foreign \"turtle\" \"forward\" (Number) -> Unit\n";
    assert_eq!(type_of(&format!("{decl}forward(10)")).unwrap(), "Unit");
    assert!(error_of(&format!("{decl}forward(true)")).contains("Number"));
    assert!(error_of(&format!("{decl}forward(1, 2)")).contains("expects 1 argument"));
    assert!(error_of(&format!("{decl}forward(1) + 1")).contains("Unit"));
}

#[test]
fn a_foreign_function_is_not_generic() {
    let decl = "id = foreign \"m\" \"id\" (Number) -> Number\n";
    assert!(check(&format!("{decl}id(\"s\")")).is_err());
}

#[test]
fn a_foreign_function_can_be_called_from_a_function() {
    let source = "forward = foreign \"turtle\" \"forward\" (Number) -> Unit\n\
                  square = program(n) do forward(n); forward(n) done\n\
                  square(3)";
    assert_eq!(type_of(source).unwrap(), "Unit");
}

#[test]
fn a_user_may_shadow_a_foreign_name() {
    let source = "f = foreign \"m\" \"f\" (Number) -> Unit\nf = 1\nf + 1";
    assert_eq!(type_of(source).unwrap(), "Number");
}

#[test]
fn foreign_is_still_a_name() {
    assert_eq!(type_of("foreign = 1 foreign + 1").unwrap(), "Number");
}

#[test]
fn types_beyond_the_boundary_are_spanned_errors() {
    for (ty, shape) in [
        ("{x: Number}", "a record"),
        ("[Number]", "a list"),
        ("(Number) -> Number", "a function"),
    ] {
        let params = format!("f = foreign \"m\" \"f\" ({ty}) -> Unit");
        let errors = errors_of(&params);
        assert_eq!(
            errors[0].message,
            format!("foreign functions can't take {shape} yet")
        );
        let at = params.find(ty).unwrap();
        assert_eq!(
            (errors[0].span.start, errors[0].span.end),
            (at, at + ty.len())
        );

        let ret = format!("f = foreign \"m\" \"f\" (Number) -> {ty}");
        let errors = errors_of(&ret);
        assert_eq!(
            errors[0].message,
            format!("foreign functions can't return {shape} yet")
        );
    }
}

#[test]
fn an_unknown_type_name_is_a_spanned_error() {
    let source = "f = foreign \"m\" \"f\" (Point) -> Unit";
    let errors = errors_of(source);
    assert!(
        errors[0]
            .message
            .starts_with("foreign functions can't take `Point` yet")
    );
    assert_eq!(&source[errors[0].span.start..errors[0].span.end], "Point");
}

#[test]
fn the_module_and_name_must_be_strings() {
    for (source, what) in [
        ("f = foreign turtle \"f\" (Number) -> Unit", "module"),
        ("f = foreign \"m\" 3 (Number) -> Unit", "name"),
    ] {
        let errors = errors_of(source);
        assert_eq!(
            errors[0].message,
            format!("the {what} of a foreign function must be a string in quotes")
        );
    }
}

#[test]
fn a_signature_without_a_return_type_does_not_parse() {
    assert!(check("f = foreign \"m\" \"f\" (Number)").is_err());
    assert!(check("f = foreign \"m\" \"f\" Number -> Unit").is_err());
}
