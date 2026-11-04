//! The goat type checker: parse → lower (name resolution) → Hindley-Milner
//! inference. The entry point is [`check`].

pub mod captures;
pub mod error;
pub mod hir;
pub mod infer;
pub mod lower;
mod order;
pub mod ty;

pub use captures::Target;
pub use error::GoatError;
pub use hir::Expr;
pub use infer::Typed;
pub use ty::Ty;

use hir::Symbol;
use std::collections::HashMap;

/// A successfully checked program: its name-resolved tree and inferred types.
pub struct Checked {
    pub root: Expr,
    pub typed: Typed,
    /// What each function literal captures, in `Capture` index order.
    pub captures: HashMap<Target, Vec<Symbol>>,
}

/// The built-in definitions every program starts with.
pub const PRELUDE: &str = include_str!("../../prelude/prelude.goat");

/// Parse, name-resolve, and type-check `source` with the prelude in scope.
///
/// Returns every diagnostic found. Lowering (name resolution) and inference
/// errors are reported together; a parse error is returned on its own. The
/// binding-order check runs only on a program that type-checks.
pub fn check(source: &str) -> Result<Checked, Vec<GoatError>> {
    check_with_prelude(PRELUDE, source)
}

/// Like [`check`], with `prelude` standing in for the built-in one.
pub fn check_with_prelude(prelude: &str, source: &str) -> Result<Checked, Vec<GoatError>> {
    let lowered = lower::lower_with_prelude(prelude, source).map_err(|e| vec![e])?;
    if !lowered.errors.is_empty() {
        return Err(lowered.errors);
    }
    let mut typed = infer::infer(&lowered.root)?;
    typed.warnings.splice(0..0, lowered.warnings);
    let captures = captures::capture_sets(&lowered.root);
    let errors = order::check(&lowered.root, &captures);
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(Checked {
        root: lowered.root,
        typed,
        captures,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The inferred type of a program, as a string, or the first error message.
    fn type_of(source: &str) -> Result<String, String> {
        match check(source) {
            Ok(checked) => Ok(checked.typed.root_ty.to_string()),
            Err(errors) => Err(errors[0].message.clone()),
        }
    }

    fn warnings_of(source: &str) -> Vec<GoatError> {
        check(source).expect("checks").typed.warnings
    }

    #[test]
    fn match_binders_record_their_types() {
        let checked = check(
            "length = program(xs) do match xs do Empty then 0 \
             Link(first, rest) then 1 + length(rest) done done length(Link(1, Empty))",
        )
        .expect("checks");
        let mut types: Vec<String> = checked
            .typed
            .binder_types
            .values()
            .map(|t| t.to_string())
            .collect();
        types.sort();
        assert_eq!(types.len(), 2);
        assert!(types.iter().any(|t| t.starts_with("μt")), "{types:?}");
        assert!(types.iter().any(|t| !t.starts_with("μt")), "{types:?}");
    }

    #[test]
    fn constructing_a_tag_gives_an_open_row() {
        assert_eq!(type_of("Circle(5)").unwrap(), "[Circle: Number | t0]");
        assert_eq!(type_of("Empty").unwrap(), "[Empty | t0]");
        let link = type_of("Link(1, Empty)").unwrap();
        assert!(
            link.starts_with("[Link: {0: Number, 1: [Empty | t"),
            "{link}"
        );
    }

    #[test]
    fn branches_building_different_tags_merge_into_one_open_row() {
        let src = "if true then Circle(1) else Square(2) done";
        let ty = type_of(src).unwrap();
        assert!(ty.starts_with("[Circle: Number, Square: Number | "), "{ty}");
    }

    #[test]
    fn match_types_to_its_arm_bodies() {
        assert_eq!(
            type_of("match Circle(5) do Circle(r) then r else 0 done").unwrap(),
            "Number"
        );
        assert_eq!(
            type_of("match Empty do Empty then true Full then false done").unwrap(),
            "Bool"
        );
    }

    #[test]
    fn match_without_else_closes_the_row() {
        let src = "area = program(s) do match s do Circle(r) then r * 2 Square(w) then w * 2 done done area";
        assert_eq!(
            type_of(src).unwrap(),
            "([Circle: Number, Square: Number]) -> Number"
        );
    }

    #[test]
    fn match_with_else_keeps_the_row_open() {
        let src = "area = program(s) do match s do Circle(r) then r * 2 else 0 done done area";
        let ty = type_of(src).unwrap();
        assert!(ty.starts_with("([Circle: Number | t"), "{ty}");
    }

    #[test]
    fn open_tag_fits_a_closed_match_but_a_stranger_does_not() {
        let area = "area = program(s) do match s do Circle(r) then r Square(w) then w done done ";
        assert_eq!(
            type_of(&format!("{area} area(Circle(1))")).unwrap(),
            "Number"
        );
        assert_eq!(
            type_of(&format!("{area} area(Square(1))")).unwrap(),
            "Number"
        );
        let err = type_of(&format!("{area} area(Triangle(1))")).unwrap_err();
        assert!(err.contains("`Triangle`"), "{err}");
    }

    #[test]
    fn closed_row_flows_through_an_else_free_match() {
        let src = "pick = program(s) do match s do A then 1 B then 2 done done \
                   x = pick(A) y = pick(B) x + y";
        assert_eq!(type_of(src).unwrap(), "Number");
    }

    #[test]
    fn arm_bodies_must_agree() {
        let err = type_of("match Circle(5) do Circle(r) then r else true done").unwrap_err();
        assert!(err.contains("type mismatch"), "{err}");
        let err =
            type_of("match Circle(5) do Circle(r) then r Square(w) then true done").unwrap_err();
        assert!(err.contains("type mismatch"), "{err}");
    }

    #[test]
    fn match_missing_a_tag_is_an_error() {
        let err = type_of("match Circle(1) do Square(w) then w done").unwrap_err();
        assert!(err.contains("doesn't handle `Circle`"), "{err}");
        let src = "f = program(s) do \
                     first = match s do A then 1 B then 2 done \
                     match s do A then 1 done \
                   done";
        let err = type_of(src).unwrap_err();
        assert!(err.contains("doesn't handle `B`"), "{err}");
    }

    #[test]
    fn match_arm_for_an_impossible_tag_is_an_error() {
        let src = "f = program(s) do \
                     first = match s do A then 1 B then 2 done \
                     match s do C then 3 else 4 done \
                   done";
        let err = type_of(src).unwrap_err();
        assert!(err.contains("matches `C`"), "{err}");
        assert!(err.contains("`A` or `B`"), "{err}");
    }

    #[test]
    fn duplicate_arm_is_an_error() {
        let err = type_of("match A do A then 1 A then 2 else 3 done").unwrap_err();
        assert!(err.contains("repeats `A`"), "{err}");
    }

    #[test]
    fn match_on_a_non_variant_is_an_error() {
        let err = type_of("match 1 do A then 0 else 1 done").unwrap_err();
        assert!(err.contains("built from tags"), "{err}");
    }

    #[test]
    fn payload_mismatch_between_construction_and_pattern_is_an_error() {
        let err = type_of("match Circle(5) do Circle then 0 else 1 done").unwrap_err();
        assert!(err.contains("type mismatch"), "{err}");
        let err = type_of("match Circle(5) do Circle(a) then a + true else 1 done").unwrap_err();
        assert!(err.contains("type mismatch"), "{err}");
    }

    #[test]
    fn multi_argument_payload_binds_positional_fields() {
        let src = "match Pair(1, true) do Pair(a, b) then if b then a else 0 done done";
        assert_eq!(type_of(src).unwrap(), "Number");
    }

    #[test]
    fn variant_errors_are_spanned() {
        let src = "match Circle(1) do Square(w) then w done";
        let Err(errors) = check(src) else {
            panic!("expected an error");
        };
        assert_eq!(&src[errors[0].span.start..errors[0].span.end], "Circle(1)");
    }

    #[test]
    fn constructed_but_never_matched_tag_warns() {
        let src = "match Cirle(5) do Circle(r) then r else 0 done";
        let warnings = warnings_of(src);
        assert_eq!(warnings.len(), 1);
        assert_eq!(
            warnings[0].message,
            "tag `Cirle` is constructed but never matched anywhere"
        );
        assert_eq!(
            &src[warnings[0].span.start..warnings[0].span.end],
            "Cirle(5)"
        );
    }

    #[test]
    fn matched_tags_do_not_warn_and_each_tag_warns_once() {
        assert!(warnings_of("match Circle(5) do Circle(r) then r else 0 done").is_empty());
        assert!(warnings_of("1 + 2").is_empty());
        let warnings = warnings_of("x = Oops(1) y = Oops(2) 0");
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].span.start, 4);
    }

    const LENGTH: &str = "length = program(xs) do match xs do Empty then 0 \
         Link(first, rest) then 1 + length(rest) done done ";

    /// The name of the first `μ` binder in a printed type.
    fn binder(ty: &str) -> &str {
        let start = ty.find('μ').expect("a recursive type") + 'μ'.len_utf8();
        &ty[start..ty[start..].find('.').unwrap() + start]
    }

    #[test]
    fn a_list_length_function_infers_a_recursive_variant() {
        let ty = type_of(&format!("{LENGTH} length")).unwrap();
        let t = binder(&ty);
        assert!(
            ty.starts_with(&format!("(μ{t}. [Empty, Link: {{0: t")),
            "{ty}"
        );
        assert!(ty.ends_with(&format!(", 1: {t}}}]) -> Number")), "{ty}");
    }

    #[test]
    fn a_recursive_function_is_polymorphic_in_its_elements() {
        let src = format!(
            "{LENGTH} length(Link(1, Link(2, Empty))) + length(Link(true, Empty)) + length(Empty)"
        );
        assert_eq!(type_of(&src).unwrap(), "Number");
    }

    #[test]
    fn a_tree_recurses_through_both_children() {
        let src = "size = program(t) do match t do Leaf then 0 \
                   Node(l, r) then 1 + size(l) + size(r) done done size";
        let ty = type_of(src).unwrap();
        let t = binder(&ty);
        assert_eq!(
            ty,
            format!("(μ{t}. [Leaf, Node: {{0: {t}, 1: {t}}}]) -> Number")
        );
    }

    #[test]
    fn building_a_recursive_value_types_as_an_open_recursive_variant() {
        let src =
            "build = program(n) do if n < 1 then Empty else Link(n, build(n - 1)) done done build";
        let ty = type_of(src).unwrap();
        let t = binder(&ty);
        assert!(
            ty.starts_with(&format!(
                "(Number) -> μ{t}. [Empty, Link: {{0: Number, 1: {t}}} | t"
            )),
            "{ty}"
        );
    }

    #[test]
    fn a_recursive_value_matches_through_nested_unfoldings() {
        let src = format!(
            "{LENGTH} second = program(xs) do match xs do Empty then 0 \
             Link(a, r) then match r do Empty then 0 Link(b, s) then length(s) done done done \
             second(Link(1, Link(2, Link(3, Empty))))"
        );
        assert_eq!(type_of(&src).unwrap(), "Number");
    }

    #[test]
    fn a_recursion_with_no_base_case_still_has_a_type() {
        let src = "f = program(xs) do match xs do Next(n) then f(n) done done f";
        let ty = type_of(src).unwrap();
        let t = binder(&ty);
        assert!(ty.starts_with(&format!("(μ{t}. [Next: {t}]) -> t")), "{ty}");
        let two = "f = program(xs) do match xs do Next(n) then match n do Next(m) then f(m) done done done f";
        assert!(type_of(two).is_ok());
    }

    #[test]
    fn a_function_returning_its_own_wrapped_result_is_recursive() {
        let ty = type_of("f = program(x) do Wrap(f(x)) done f").unwrap();
        let t = binder(&ty);
        assert!(ty.contains(&format!("μ{t}. [Wrap: {t} | t")), "{ty}");
    }

    #[test]
    fn two_recursive_types_unify() {
        let src = format!(
            "{LENGTH} both = program(xs, ys) do a = length(xs) b = length(ys) \
             if true then xs else ys done done both"
        );
        assert!(type_of(&src).is_ok());
    }

    #[test]
    fn rebuilding_a_scrutinee_ties_the_row_itself() {
        let src = "f = program(xs) do \
                     z = match xs do Empty then 0 else 1 done \
                     match xs do Empty then Link(1, xs) else xs done \
                   done f";
        let ty = type_of(src).unwrap();
        let t = binder(&ty);
        assert!(
            ty.starts_with(&format!("(μ{t}. [Empty, Link: {{0: Number, 1: {t}}} | t")),
            "{ty}"
        );
        let after_empty = "f = program(xs) do \
                     z = match xs do Empty then 0 else 1 done \
                     if true then xs else Link(1, xs) done \
                   done f";
        assert!(type_of(after_empty).is_ok());
    }

    #[test]
    fn a_cycle_outside_a_variant_tag_is_still_infinite() {
        for src in [
            "f = program(x) do x(x) done f",
            "f = program(x) do Wrap(x(x)) done f",
            "f = program(x) do {a: x(x)} done f",
            "f = program(r) do if true then r else {a: r} done done f",
        ] {
            let err = type_of(src).unwrap_err();
            assert!(err.contains("infinite type"), "{src}: {err}");
        }
    }

    #[test]
    fn a_recursive_variant_still_rejects_the_wrong_shape() {
        for tail in ["3", "Wrong", "Link(1, 2)", "Link(true, Empty) + 1"] {
            let src = format!("{LENGTH} length(Link(1, {tail}))");
            assert!(type_of(&src).is_err(), "{src}");
        }
        let err = type_of(&format!("{LENGTH} length(Link(1, Wrong))")).unwrap_err();
        assert!(err.contains("`Wrong`"), "{err}");
    }

    #[test]
    fn a_recursive_program_type_checks_with_no_unused_tag_warning() {
        let src = format!("{LENGTH} length(Link(1, Empty))");
        assert!(warnings_of(&src).is_empty());
    }

    #[test]
    fn recursive_types_survive_in_schemes_and_node_types() {
        let checked = check(&format!("{LENGTH} length")).unwrap();
        let scheme = checked.typed.schemes.values().next().unwrap();
        let printed = scheme.ty.to_string();
        assert!(printed.contains('μ'), "{printed}");
        assert!(
            checked
                .typed
                .node_types
                .values()
                .any(|t| t.to_string().contains('μ')),
            "no node carries the recursive type"
        );
    }

    #[test]
    fn calling_a_non_function_is_a_clear_error() {
        assert!(type_of("1(2)").unwrap_err().contains("is not a function"));
        // the sequencing-mistake shape: `(…)` right after an expression
        assert!(
            type_of("x = 1 (2)")
                .unwrap_err()
                .contains("is not a function")
        );
        // a real call still works
        assert_eq!(type_of("f = program(x) do x done f(1)").unwrap(), "Number");
    }

    #[test]
    fn capturing_closures_type_check() {
        let curried = "add = program(a) do program(b) do a + b done done add(1)(2)";
        assert_eq!(type_of(curried).unwrap(), "Number");

        let recursive = "outer = program(n) do \
                           go = program(k) do if k < 1 then 0 else n + go(k - 1) done done \
                           go(3) \
                         done \
                         outer(10)";
        assert_eq!(type_of(recursive).unwrap(), "Number");

        let polymorphic_apply = "apply = program(f, x) do f(x) done \
                                 n = 10 \
                                 t = true \
                                 addn = program(x) do x + n done \
                                 pick = program(b) do if t then b else false done done \
                                 if apply(pick, true) then apply(addn, 1) else 0 done";
        assert_eq!(type_of(polymorphic_apply).unwrap(), "Number");

        let record_of_functions = "k = 10 \
                                   r = {f: program(x) do x + k done, g: program(x) do x * k done} \
                                   r.f(3) + r.g(2)";
        assert_eq!(type_of(record_of_functions).unwrap(), "Number");
    }

    #[test]
    fn capturing_closures_reject_ill_typed_calls() {
        assert!(type_of("add = program(a) do program(b) do a + b done done add(1)(true)").is_err());
        assert!(type_of("k = 10 f = program(x) do x + k done f(true)").is_err());
    }

    #[test]
    fn literals() {
        assert_eq!(type_of("1").unwrap(), "Number");
        assert_eq!(type_of("1.5").unwrap(), "Number");
        assert_eq!(type_of("\"hi\"").unwrap(), "String");
        assert_eq!(type_of("true").unwrap(), "Bool");
        assert_eq!(type_of("").unwrap(), "Unit");
    }

    #[test]
    fn arithmetic_and_comparison() {
        assert_eq!(type_of("1 + 2 * 3").unwrap(), "Number");
        assert_eq!(type_of("1 < 2").unwrap(), "Bool");
        assert_eq!(type_of("(1 + 2) < 3").unwrap(), "Bool");
    }

    #[test]
    fn arithmetic_rejects_non_numbers() {
        assert!(type_of("1 + true").is_err());
        assert!(type_of("\"a\" * 2").is_err());
    }

    #[test]
    fn declaration_binds_and_sequences() {
        assert_eq!(type_of("x = 1 x + 2").unwrap(), "Number");
        assert_eq!(type_of("x = 1").unwrap(), "Number");
    }

    #[test]
    fn unknown_name_is_an_error() {
        assert_eq!(type_of("x + 1").unwrap_err(), "unknown name `x`");
    }

    #[test]
    fn identity_function_is_polymorphic() {
        // `program(x) do x done` : (t) -> t
        let ty = type_of("program(x) do x done").unwrap();
        assert!(ty.contains("->"), "expected a function type, got {ty}");
        // applied to a number, yields a number
        assert_eq!(
            type_of("id = program(x) do x done id(1)").unwrap(),
            "Number"
        );
    }

    #[test]
    fn let_polymorphism() {
        // The same identity binding is used at two different types.
        let src = "id = program(x) do x done a = id(1) b = id(true) b";
        assert_eq!(type_of(src).unwrap(), "Bool");
    }

    #[test]
    fn function_application_checks_arguments() {
        assert_eq!(
            type_of("add = program(a, b) do a + b done add(1, 2)").unwrap(),
            "Number"
        );
        // wrong argument type
        assert!(type_of("add = program(a, b) do a + b done add(1, true)").is_err());
        // wrong arity
        assert!(type_of("add = program(a, b) do a + b done add(1)").is_err());
    }

    #[test]
    fn recursion_checks() {
        // A recursive countdown: program(n) do if n < 1 then 0 else count(n - 1) done done
        let src = "count = program(n) do if n < 1 then 0 else count(n - 1) done done count(5)";
        assert_eq!(type_of(src).unwrap(), "Number");
    }

    #[test]
    fn records_infer_and_access() {
        assert_eq!(type_of("{x: 1, y: 2}").unwrap(), "{x: Number, y: Number}");
        assert_eq!(type_of("p = {x: 1, y: true} p.x").unwrap(), "Number");
        assert_eq!(type_of("p = {x: 1, y: true} p.y").unwrap(), "Bool");
        // nested records
        assert_eq!(
            type_of("line = {from: {x: 0}, to: {x: 10}} line.to.x").unwrap(),
            "Number"
        );
    }

    #[test]
    fn record_field_errors() {
        // accessing a field the record does not have
        assert!(type_of("p = {x: 1} p.z").is_err());
        // a field used as the wrong type
        assert!(type_of("p = {x: 1} p.x + true").is_err());
    }

    #[test]
    fn record_field_access_is_row_polymorphic() {
        // `program(p) do p.x done` accepts any record with an `x` field, so it
        // applies to records of different shapes.
        let src = "getx = program(p) do p.x done \
                   a = getx({x: 1, y: 2}) \
                   b = getx({x: 9, z: true}) \
                   a + b";
        assert_eq!(type_of(src).unwrap(), "Number");
    }

    #[test]
    fn conditional_branches_must_agree() {
        assert_eq!(type_of("if true then 1 else 2 done").unwrap(), "Number");
        assert!(type_of("if true then 1 else false done").is_err());
        assert!(type_of("if 1 then 2 else 3 done").is_err());
    }

    /// The contract mono relies on: a let-bound symbol's scheme, `Var`
    /// use sites typed at their instantiation, and the generalized body still
    /// mentioning the scheme's quantified variable.
    #[test]
    fn schemes_and_instantiated_node_types() {
        use crate::hir::ExprKind;
        use crate::ty::Ty;

        let checked = check("id = program(x) do x done\na = id(1)\nb = id(true)\nb").unwrap();
        let typed = &checked.typed;

        let ExprKind::Let {
            symbol: id_sym,
            value: id_value,
            rest: Some(rest_a),
            ..
        } = &checked.root.kind
        else {
            panic!("expected `id` let");
        };
        let ExprKind::Let {
            value: a_value,
            rest: Some(rest_b),
            ..
        } = &rest_a.kind
        else {
            panic!("expected `a` let");
        };
        let ExprKind::Let { value: b_value, .. } = &rest_b.kind else {
            panic!("expected `b` let");
        };

        let scheme = &typed.schemes[id_sym];
        assert_eq!(scheme.vars.len(), 1);
        let quantified = scheme.vars[0];
        assert_eq!(
            scheme.ty,
            Ty::Func(vec![Ty::Var(quantified)], Box::new(Ty::Var(quantified)))
        );

        let callee_ty = |call: &crate::hir::Expr| {
            let ExprKind::App { callee, .. } = &call.kind else {
                panic!("expected a call");
            };
            assert!(matches!(&callee.kind, ExprKind::Var { symbol, .. } if symbol == id_sym));
            typed.node_types[&callee.id].to_string()
        };
        assert_eq!(callee_ty(a_value), "(Number) -> Number");
        assert_eq!(callee_ty(b_value), "(Bool) -> Bool");

        let ExprKind::Func { body, .. } = &id_value.kind else {
            panic!("expected a function");
        };
        assert_eq!(typed.node_types[&body.id], Ty::Var(quantified));
    }

    #[test]
    fn calls_on_any_callee() {
        let src = "vec = {add: program(p, q) do p.x + q.x done} vec.add({x: 1}, {x: 2})";
        assert_eq!(type_of(src).unwrap(), "Number");
        // chained calls and accesses nest left to right
        assert_eq!(
            type_of("f = program(x) do program(y) do x + y done done f(1)(2)").unwrap(),
            "Number"
        );
        assert_eq!(
            type_of("a = {b: {c: program(x) do x done}} a.b.c(1)").unwrap(),
            "Number"
        );
        // a call result can be accessed
        assert_eq!(
            type_of("f = program() do {x: true} done f().x").unwrap(),
            "Bool"
        );
        // a grouped expression is not a call
        assert_eq!(type_of("(1 + 2) < 3").unwrap(), "Bool");
        // calling a non-function is a checker error, not a panic
        assert!(type_of("1(2)").is_err());
    }

    #[test]
    fn negation_and_subtraction() {
        assert_eq!(type_of("-3").unwrap(), "Number");
        assert_eq!(type_of("--3").unwrap(), "Number");
        assert_eq!(type_of("a = 1 1 - a").unwrap(), "Number");
        // `5 -1` is the subtraction `5 - 1`, never `5` followed by `-1`
        assert_eq!(type_of("5 -1").unwrap(), "Number");
        assert_eq!(type_of("5 - -1").unwrap(), "Number");
        // negation binds tighter than `*` and applies to a whole postfix chain
        assert_eq!(type_of("p = {x: 2} 3 * -p.x").unwrap(), "Number");
        assert!(type_of("-true").is_err());
    }

    #[test]
    fn duplicate_record_labels_are_rejected() {
        let err = type_of("{x: 1, x: 2}").unwrap_err();
        assert!(err.contains("duplicate") && err.contains("`x`"), "{err}");
        assert!(type_of("{x: 1, y: 2}").is_ok());
    }

    #[test]
    fn empty_string_and_lenient_literals() {
        assert_eq!(type_of("\"\"").unwrap(), "String");
        assert_eq!(type_of(".5").unwrap(), "Number");
        assert_eq!(type_of("007").unwrap(), "Number");
        assert_eq!(type_of("{x: 1,}").unwrap(), "{x: Number}");
        assert_eq!(type_of("f = program(a) do a done f(1,)").unwrap(), "Number");
    }

    #[test]
    fn mismatch_reads_expected_then_found_on_the_offending_span() {
        let errors = check("1 + true").err().expect("type error");
        assert_eq!(
            errors[0].message,
            "type mismatch: expected `Number`, found `Bool`"
        );
        assert_eq!((errors[0].span.start, errors[0].span.end), (4, 8));
        assert_eq!(
            type_of("add = program(a, b) do a + b done add(1, true)").unwrap_err(),
            "type mismatch: expected `Number`, found `Bool`"
        );
    }

    #[test]
    fn reusing_a_parameter_at_two_types_names_the_parameter() {
        assert_eq!(
            type_of("use = program(m) do a = m.id + 1\n if m.id then 1 else 2 done done use(1)")
                .unwrap_err(),
            "`m` is a parameter, so m.id can only be used at one type here; bind it with `=` instead"
        );
        assert_eq!(
            type_of("both = program(f) do a = f(1)\n b = f(true)\n b done").unwrap_err(),
            "`f` is a parameter, so it can only be used at one type here; bind it with `=` instead"
        );
        assert_eq!(
            type_of("use2 = program(g) do a = g({x: 1})\n b = g({x: 2, y: 3})\n b done use2(1)")
                .unwrap_err(),
            "`g` is a parameter, so it can only be used at one type here; bind it with `=` instead"
        );
    }

    #[test]
    fn ordinary_mismatches_and_bound_functions_keep_their_messages() {
        assert_eq!(
            type_of("1 + true").unwrap_err(),
            "type mismatch: expected `Number`, found `Bool`"
        );
        assert_eq!(
            type_of("f = program(x) do x done\n a = f(1)\n b = f(true)\n b").unwrap(),
            "Bool"
        );
        assert_eq!(
            type_of("f = program(n) do n + 1 done\n g = program(h) do h(true) done\n g(f)")
                .unwrap_err(),
            "type mismatch: expected `Number`, found `Bool`"
        );
    }

    #[test]
    fn missing_field_is_reported_as_missing() {
        assert_eq!(
            type_of("{x: 1}.y").unwrap_err(),
            "record is missing field `y`"
        );
    }

    #[test]
    fn conditional_without_else_must_be_unit() {
        assert_eq!(
            type_of("if true then 1 done").unwrap_err(),
            "type mismatch: expected `Unit`, found `Number`"
        );
        assert_eq!(
            type_of("nop = program() do done if true then nop() done").unwrap(),
            "Unit"
        );
    }

    #[test]
    fn mutual_recursion_works_in_either_order() {
        let even_first = "is_even = program(n) do if n < 1 then true else is_odd(n - 1) done done \
                          is_odd = program(n) do if n < 1 then false else is_even(n - 1) done done \
                          is_even(4)";
        let odd_first = "is_odd = program(n) do if n < 1 then false else is_even(n - 1) done done \
                         is_even = program(n) do if n < 1 then true else is_odd(n - 1) done done \
                         is_even(4)";
        assert_eq!(type_of(even_first).unwrap(), "Bool");
        assert_eq!(type_of(odd_first).unwrap(), "Bool");
    }

    #[test]
    fn mutual_recursion_rejects_ill_typed_calls() {
        let src = "f = program(n) do g(true) done g = program(n) do n + 1 done f(1)";
        assert!(type_of(src).is_err());
    }

    #[test]
    fn value_bindings_shadow() {
        assert_eq!(
            type_of("score = 1 score = score + 1 score").unwrap(),
            "Number"
        );
        assert_eq!(
            type_of("score = score + 1").unwrap_err(),
            "unknown name `score`"
        );
        assert_eq!(
            type_of("ones = Link(1, ones)").unwrap_err(),
            "unknown name `ones`"
        );
        assert_eq!(
            type_of("ones = {a: ones}").unwrap_err(),
            "unknown name `ones`"
        );
    }

    #[test]
    fn duplicate_parameter_is_an_error() {
        assert_eq!(
            type_of("program(a, a) do a done").unwrap_err(),
            "duplicate parameter `a`"
        );
    }

    /// The single error of a program rejected for use before definition: its
    /// message and the source text its span covers.
    fn order_error(source: &str) -> (String, &str) {
        let errors = check(source).err().expect("rejected");
        assert_eq!(errors.len(), 1, "{errors:?}");
        let span = errors[0].span;
        (errors[0].message.clone(), &source[span.start..span.end])
    }

    #[test]
    fn function_run_before_a_value_it_reads_is_rejected() {
        let src = "f = program() do g() done  x = f()  m = 5  g = program() do m done  x";
        let errors = check(src).err().expect("rejected");
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].message, "`f` uses `m` before it is defined");
        assert_eq!(errors[0].span.start, src.find("f()  m").unwrap());
        assert_eq!(errors[0].span.end, errors[0].span.start + 1);
    }

    #[test]
    fn function_value_taken_before_a_value_it_reads_is_rejected() {
        let src = "f = program() do g() done  h = f  m = 5  g = program() do m done  h()";
        assert_eq!(
            order_error(src),
            ("`f` uses `m` before it is defined".to_string(), "f")
        );
    }

    #[test]
    fn program_literal_built_before_a_value_it_reads_is_rejected() {
        let src = "apply = program(h) do h() done \
                   z = apply(program() do g() done) \
                   m = 5 \
                   g = program() do m done \
                   z";
        assert_eq!(
            order_error(src),
            (
                "this program uses `m` before it is defined".to_string(),
                "program() do g() done"
            )
        );
    }

    #[test]
    fn order_is_checked_in_every_scope() {
        let src = "outer = program() do \
                     f = program() do g() done \
                     x = f() \
                     m = 5 \
                     g = program() do m done \
                     x \
                   done \
                   outer()";
        assert_eq!(
            order_error(src),
            ("`f` uses `m` before it is defined".to_string(), "f")
        );
    }

    #[test]
    fn functions_may_run_once_their_values_are_defined() {
        for src in [
            "f = program() do g() done  m = 5  g = program() do m done  f()",
            "m = 5  f = program() do g() done  g = program() do m done  f()",
            "m = 5  g = program() do m done  f = program() do g() done  f()",
            "f = program() do g() done  m = 5  g = program() do m done  x = f()  x",
            "g = program() do 0 done  m = 5  x = f()  f = program() do m done  x",
            "f = program() do g() done  g = program() do 1 done  f()",
            "m = 5  f = program() do g() done  h = f  g = program() do m done  h()",
            "outer = program() do \
               f = program() do g() done \
               m = 5 \
               g = program() do m done \
               f() \
             done \
             outer()",
        ] {
            assert_eq!(type_of(src).unwrap(), "Number", "{src}");
        }
    }

    #[test]
    fn mutual_recursion_with_earlier_values_still_checks() {
        let src = "limit = 4 \
                   is_even = program(n) do if n < 1 then true else is_odd(n - 1) done done \
                   is_odd = program(n) do if n < 1 then false else is_even(n - 1) done done \
                   is_even(limit)";
        assert_eq!(type_of(src).unwrap(), "Bool");
    }

    fn chain(n: usize) -> String {
        vec!["1"; n].join(" + ")
    }

    #[test]
    fn deeply_nested_expression_is_a_clean_error() {
        let Err(errors) = check(&chain(100_000)) else {
            panic!("expected an error");
        };
        assert_eq!(errors[0].message, "expression nested too deeply");
        assert_eq!(errors[0].span.start, 0);
    }

    #[test]
    fn moderately_nested_expression_still_checks() {
        assert_eq!(type_of(&chain(200)).unwrap(), "Number");
    }

    fn first_error(source: &str) -> GoatError {
        check(source).err().expect("an error").remove(0)
    }

    #[test]
    fn spread_adds_a_field() {
        let src = "p = {x: 1} {...p, y: true}";
        assert_eq!(type_of(src).unwrap(), "{y: Bool, x: Number}");
        assert_eq!(type_of("p = {x: 1} {...p}").unwrap(), "{x: Number}");
    }

    #[test]
    fn spread_override_replaces_the_field_even_at_a_new_type() {
        let same = "p = {x: 1, y: 2} {...p, x: 5}";
        assert_eq!(type_of(same).unwrap(), "{x: Number, y: Number}");
        let changed = "p = {x: 1, y: 2} {...p, x: \"one\"}";
        assert_eq!(type_of(changed).unwrap(), "{x: String, y: Number}");
        assert_eq!(
            type_of("p = {x: 1} q = {...p, x: true} q.x").unwrap(),
            "Bool"
        );
    }

    #[test]
    fn spread_of_an_unknown_record_stays_polymorphic_in_the_rest() {
        let src = "bump = program(m) do {...m, x: 1} done \
                   a = bump({y: true}) \
                   b = bump({x: \"s\", z: 2}) \
                   if a.y then b.x + a.x else 0 done";
        assert_eq!(type_of(src).unwrap(), "Number");
    }

    #[test]
    fn spread_update_of_a_field_it_reads_can_recurse() {
        let src = "countdown = program(s) do \
                     if s.n < 1 then s else countdown({...s, n: s.n - 1}) done done \
                   countdown({n: 3, label: true}).label";
        assert_eq!(type_of(src).unwrap(), "Bool");
    }

    #[test]
    fn spread_needs_a_record_and_mentions_what_it_got() {
        let err = first_error("{...3, x: 1}");
        assert!(err.message.contains("copies a record"), "{}", err.message);
        assert!(err.message.contains("Number"), "{}", err.message);
        assert_eq!((err.span.start, err.span.end), (4, 5));
    }

    #[test]
    fn two_spreads_cannot_merge() {
        let src = "a = {x: 1} b = {y: 2} {...a, ...b}";
        let err = first_error(src);
        assert!(
            err.message
                .contains("can't merge two records of unknown shape here"),
            "{}",
            err.message
        );
        assert_eq!(&src[err.span.start..err.span.end], "...b");
        assert!(check("a = {x: 1} {...a, x: 2, ...a}").is_err());
    }

    #[test]
    fn a_spread_must_come_first() {
        let src = "a = {x: 1} {y: 2, ...a}";
        let err = first_error(src);
        assert!(err.message.contains("must come first"), "{}", err.message);
        assert_eq!(&src[err.span.start..err.span.end], "...a");
    }

    #[test]
    fn spread_keeps_duplicate_field_detection() {
        let err = first_error("a = {x: 1} {...a, y: 1, y: 2}");
        assert!(
            err.message.contains("duplicate field `y`"),
            "{}",
            err.message
        );
    }

    #[test]
    fn destructuring_binds_each_field() {
        let src = "point = {x: 1, y: true} {x, y} = point if y then x else 0 done";
        assert_eq!(type_of(src).unwrap(), "Number");
        assert_eq!(type_of("{x} = {x: 1, y: true}  x").unwrap(), "Number");
        assert_eq!(type_of("{x, y} = {x: 1, y: true}").unwrap(), "Bool");
    }

    #[test]
    fn destructuring_accepts_any_record_with_at_least_those_fields() {
        let src = "norm = program(p) do {x, y} = p x + y done \
                   norm({x: 1, y: 2}) + norm({a: 0, x: 3, y: 4, z: true})";
        assert_eq!(type_of(src).unwrap(), "Number");
    }

    #[test]
    fn destructuring_a_missing_field_points_at_the_name() {
        let src = "p = {x: 1} {x, z} = p x";
        let err = first_error(src);
        assert!(err.message.contains("missing field `z`"), "{}", err.message);
        assert_eq!(&src[err.span.start..err.span.end], "z");
    }

    #[test]
    fn destructured_names_scope_over_the_rest_and_shadow() {
        assert_eq!(type_of("{x} = {x: 1} {x} = {x: true} x").unwrap(), "Bool");
        assert!(type_of("f = program(p) do {x} = p x done x").is_err());
        let err = first_error("p = {x: 1} {x, x} = p x");
        assert!(
            err.message.contains("duplicate name `x`"),
            "{}",
            err.message
        );
    }

    #[test]
    fn parameter_destructuring() {
        let src = "norm = program({x, y}) do x * x + y * y done \
                   norm({x: 3, y: 4})";
        assert_eq!(type_of(src).unwrap(), "Number");
        let mixed = "f = program(a, {x}, b) do a + x + b done f(1, {x: 2, q: true}, 3)";
        assert_eq!(type_of(mixed).unwrap(), "Number");
        let err = first_error("f = program({x}) do x done f({y: 1})");
        assert!(err.message.contains("`x`"), "{}", err.message);
        let dup = first_error("f = program(x, {x}) do x done");
        assert!(
            dup.message.contains("duplicate parameter `x`"),
            "{}",
            dup.message
        );
    }

    #[test]
    fn rest_binds_the_record_without_the_named_fields() {
        let src = "{x, ...rest} = {x: 1, y: true, z: 2} rest";
        assert_eq!(type_of(src).unwrap(), "{y: Bool, z: Number}");
        let all = "{x, y, ...rest} = {x: 1, y: true} rest";
        assert_eq!(type_of(all).unwrap(), "{}");
        assert_eq!(type_of("{...rest} = {x: 1} rest").unwrap(), "{x: Number}");
        let param = "drop = program({x, ...r}) do r done drop({x: 1, y: true})";
        assert_eq!(type_of(param).unwrap(), "{y: Bool}");
    }

    #[test]
    fn rest_needs_the_removed_fields() {
        let err = first_error("{x, y, ...rest} = {x: 1} rest");
        assert!(err.message.contains("`y`"), "{}", err.message);
    }

    #[test]
    fn rest_refuses_a_label_a_spread_override_hid() {
        let bump = "bump = program(m) do {...m, x: 1} done \
                    drop = program({x, ...r}) do r done ";
        assert_eq!(
            type_of(&format!("{bump} drop(bump({{y: 2}}))")).unwrap(),
            "{y: Number}"
        );
        let err = first_error(&format!("{bump} drop(bump({{x: \"s\", y: 2}}))"));
        let twice = "`x` is in this record twice";
        assert!(err.message.contains(twice), "{}", err.message);
        let direct =
            first_error("bump = program(m) do {...m, x: 1} done {x, ...r} = bump({x: true}) r");
        assert!(direct.message.contains(twice), "{}", direct.message);
    }
}
