//! The goat type checker: parse → lower (name resolution) → Hindley-Milner
//! inference. The entry point is [`check`].

pub mod error;
pub mod hir;
pub mod infer;
pub mod lower;
pub mod ty;

pub use error::GoatError;
pub use hir::Expr;
pub use infer::Typed;
pub use ty::Ty;

/// A successfully checked program: its name-resolved tree and inferred types.
pub struct Checked {
    pub root: Expr,
    pub typed: Typed,
}

/// Parse, name-resolve, and type-check `source`.
///
/// Returns every diagnostic found. Lowering (name resolution) and inference
/// errors are reported together; a parse error is returned on its own.
pub fn check(source: &str) -> Result<Checked, Vec<GoatError>> {
    let lowered = lower::lower(source).map_err(|e| vec![e])?;
    if !lowered.errors.is_empty() {
        return Err(lowered.errors);
    }
    match infer::infer(&lowered.root) {
        Ok(typed) => Ok(Checked {
            root: lowered.root,
            typed,
        }),
        Err(errors) => Err(errors),
    }
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
}
