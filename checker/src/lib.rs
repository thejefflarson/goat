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

/// Parse, name-resolve, and type-check `source`.
///
/// Returns every diagnostic found. Lowering (name resolution) and inference
/// errors are reported together; a parse error is returned on its own. The
/// binding-order check runs only on a program that type-checks.
pub fn check(source: &str) -> Result<Checked, Vec<GoatError>> {
    let lowered = lower::lower(source).map_err(|e| vec![e])?;
    if !lowered.errors.is_empty() {
        return Err(lowered.errors);
    }
    let typed = infer::infer(&lowered.root)?;
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
            "unknown name `Link`"
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
}
