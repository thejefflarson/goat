//! The shape lowering gives a block, which `Den_blk` in `proofs/GoatDen.v` reads
//! (ADR 0003, ADR 0030): a `;` statement is a binding of a name nothing uses, a
//! block that ends in a binding has no body, an empty program or function body is
//! the unit value, and `program()` and `f()` keep their empty parameter and
//! argument lists. Lowering keeps source order; where a function binding sits is
//! the checker's decision, which the proof reads from what the function uses.

use goat_checker::hir::{BinOp, Expr, ExprKind};
use goat_checker::lower::lower;

fn lowered_root(source: &str) -> Expr {
    let lowered = lower(source).unwrap_or_else(|e| panic!("{source:?} does not parse: {e:?}"));
    assert!(
        lowered.errors.is_empty(),
        "{source:?} lowers with errors: {:?}",
        lowered.errors
    );
    lowered.root
}

fn sexp(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Unit => "()".into(),
        ExprKind::Int(n) => n.to_string(),
        ExprKind::Var { name, .. } => name.clone(),
        ExprKind::Bin { op, lhs, rhs } => {
            let op = match op {
                BinOp::Add => "+",
                BinOp::Lt => "<",
                other => panic!("a block test uses no {other:?}"),
            };
            format!("({op} {} {})", sexp(lhs), sexp(rhs))
        }
        ExprKind::Let {
            name, value, rest, ..
        } => match rest {
            Some(rest) => format!("(let {name} {} {})", sexp(value), sexp(rest)),
            None => format!("(let {name} {})", sexp(value)),
        },
        ExprKind::Func { params, body } => {
            let names: Vec<_> = params.iter().map(|p| p.name.as_str()).collect();
            format!("(fn ({}) {})", names.join(" "), sexp(body))
        }
        ExprKind::App { callee, args } => {
            let mut parts = vec![sexp(callee)];
            parts.extend(args.iter().map(sexp));
            format!("({})", parts.join(" "))
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => match else_branch {
            Some(other) => format!("(if {} {} {})", sexp(cond), sexp(then_branch), sexp(other)),
            None => format!("(if {} {})", sexp(cond), sexp(then_branch)),
        },
        other => panic!("a block lowers to no {other:?}"),
    }
}

fn lowered(source: &str) -> String {
    sexp(&lowered_root(source))
}

#[test]
fn an_empty_program_is_unit() {
    assert_eq!(lowered(""), "()");
}

#[test]
fn a_statement_binds_a_name_nothing_uses() {
    assert_eq!(lowered("1; 2"), "(let _ 1 2)");
}

#[test]
fn a_trailing_semicolon_leaves_unit() {
    assert_eq!(lowered("1;"), "(let _ 1 ())");
}

#[test]
fn a_block_ending_in_a_binding_has_no_body() {
    assert_eq!(lowered("x = 1"), "(let x 1)");
    assert_eq!(lowered("x = 1\ny = 2"), "(let x 1 (let y 2))");
}

#[test]
fn a_stray_semicolon_after_a_binding_is_skipped() {
    assert_eq!(lowered("x = 1;; x"), "(let x 1 x)");
}

#[test]
fn a_function_with_no_parameters_keeps_the_empty_list() {
    assert_eq!(lowered("program() do done"), "(fn () ())");
    assert_eq!(lowered("program() do 1 done"), "(fn () 1)");
}

#[test]
fn a_call_with_no_arguments_keeps_the_empty_list() {
    assert_eq!(
        lowered("f = program() do 1 done\nf()"),
        "(let f (fn () 1) (f))"
    );
}

#[test]
fn an_if_without_an_else_has_no_else_branch() {
    assert_eq!(
        lowered("x = 1\nif x < 2 then 1 done"),
        "(let x 1 (if (< x 2) 1))"
    );
}

#[test]
fn a_function_after_a_value_stays_where_it_is_written() {
    assert_eq!(
        lowered("x = 1\ng = program() do x done\ng()"),
        "(let x 1 (let g (fn () x) (g)))"
    );
}

#[test]
fn a_function_sees_the_functions_written_after_a_value() {
    let source = "f = program() do g() done\nx = 1\ng = program() do 1 done\nf()";
    assert_eq!(
        lowered(source),
        "(let f (fn () (g)) (let x 1 (let g (fn () 1) (f))))"
    );
}

#[test]
fn a_function_binding_as_an_operand_is_a_binding() {
    assert_eq!(
        lowered("1 + f = program(x) do x done f(2)"),
        "(+ 1 (let f (fn (x) x) (f 2)))"
    );
}

/// The block with each name followed by the number of the binding it is, in the
/// order bindings first appear, so two bindings of one name differ.
fn resolved(e: &Expr, numbers: &mut Vec<u32>) -> String {
    fn number(numbers: &mut Vec<u32>, symbol: u32) -> usize {
        match numbers.iter().position(|s| *s == symbol) {
            Some(at) => at,
            None => {
                numbers.push(symbol);
                numbers.len() - 1
            }
        }
    }
    match &e.kind {
        ExprKind::Int(n) => n.to_string(),
        ExprKind::Var { symbol, name } => format!("{name}#{}", number(numbers, *symbol)),
        ExprKind::Bin { lhs, rhs, .. } => {
            format!("(+ {} {})", resolved(lhs, numbers), resolved(rhs, numbers))
        }
        ExprKind::Let {
            symbol,
            name,
            value,
            rest,
        } => {
            let value = resolved(value, numbers);
            let bound = format!("{name}#{}", number(numbers, *symbol));
            let rest = rest
                .as_ref()
                .map_or(String::new(), |r| format!(" {}", resolved(r, numbers)));
            format!("(let {bound} {value}{rest})")
        }
        ExprKind::Func { params, body } => {
            let names: Vec<_> = params
                .iter()
                .map(|p| format!("{}#{}", p.name, number(numbers, p.symbol)))
                .collect();
            format!("(fn ({}) {})", names.join(" "), resolved(body, numbers))
        }
        ExprKind::App { callee, args } => {
            let mut parts = vec![resolved(callee, numbers)];
            parts.extend(args.iter().map(|a| resolved(a, numbers)));
            format!("({})", parts.join(" "))
        }
        other => panic!("a shadowing test lowers to no {other:?}"),
    }
}

/// `ctx` in `proofs/GoatDen.v` resolves a name by its text, so a name bound
/// twice in one run is read as the nearest earlier binding; lowering agrees by
/// giving each binding its own symbol.
#[test]
fn a_name_bound_twice_in_one_run_is_two_bindings_and_a_use_is_the_nearest() {
    let root = lowered_root("x = 1\nx = x + 1\nx");
    assert_eq!(
        resolved(&root, &mut Vec::new()),
        "(let x#0 1 (let x#1 (+ x#0 1) x#1))"
    );
}

#[test]
fn a_function_keeps_the_binding_it_was_written_after() {
    let root = lowered_root("x = 1\nf = program(y) do x done\nx = 2\nf(0) + x");
    assert_eq!(
        resolved(&root, &mut Vec::new()),
        "(let x#0 1 (let f#2 (fn (y#1) x#0) (let x#3 2 (+ (f#2 0) x#3))))"
    );
}

#[test]
fn a_rebinding_may_change_the_type() {
    let source = "x = 1\nx = \"one\"\nx";
    assert!(goat_checker::check_with_prelude("", source).is_ok());
}
