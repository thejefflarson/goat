//! The shape lowering gives a loop, which `Den` in `proofs/GoatDen.v` reads
//! (`counted`, `each_term`, ADR 0013, ADR 0030): a loop is a local function that
//! tests, runs the body and calls itself, entered at the start, so it needs no
//! loop node. Each case lowers a loop and compares the HIR, written as an
//! s-expression over the names lowering gives its generated bindings, with the
//! shape the Coq term has.

use goat_checker::hir::{BinOp, Expr, ExprKind, PatternPayload};
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

fn op_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Lt => "<",
        BinOp::Lte => "<=",
        other => panic!("a loop uses no {other:?}"),
    }
}

fn sexp(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Unit => "()".into(),
        ExprKind::Int(n) => n.to_string(),
        ExprKind::Var { name, .. } => name.clone(),
        ExprKind::Bin { op, lhs, rhs } => {
            format!("({} {} {})", op_name(*op), sexp(lhs), sexp(rhs))
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch: Some(else_branch),
        } => format!(
            "(if {} {} {})",
            sexp(cond),
            sexp(then_branch),
            sexp(else_branch)
        ),
        ExprKind::Let {
            name,
            value,
            rest: Some(rest),
            ..
        } => format!("(let {name} {} {})", sexp(value), sexp(rest)),
        ExprKind::Func { params, body } => {
            let names: Vec<_> = params.iter().map(|p| p.name.as_str()).collect();
            format!("(fn ({}) {})", names.join(" "), sexp(body))
        }
        ExprKind::App { callee, args } => {
            let args: Vec<_> = args.iter().map(sexp).collect();
            format!("({} {})", sexp(callee), args.join(" "))
        }
        ExprKind::Tag {
            name,
            payload: None,
            ..
        } => name.clone(),
        ExprKind::Tag {
            name,
            payload: Some(payload),
            ..
        } => format!("({name} {})", sexp(payload)),
        ExprKind::Record { fields } => {
            let fields: Vec<_> = fields
                .iter()
                .map(|(label, e)| format!("{label}={}", sexp(e)))
                .collect();
            format!("{{{}}}", fields.join(" "))
        }
        ExprKind::Match {
            scrutinee,
            arms,
            else_branch: None,
        } => {
            let arms: Vec<_> = arms
                .iter()
                .map(|arm| {
                    let slots = match &arm.pattern.payload {
                        PatternPayload::None => String::new(),
                        PatternPayload::Fields(fields) => fields
                            .iter()
                            .map(|(label, p)| format!(" {label}={}", p.name))
                            .collect(),
                        other => panic!("a loop's arm binds {other:?}"),
                    };
                    format!("({}{slots} {})", arm.pattern.tag, sexp(&arm.body))
                })
                .collect();
            format!("(match {} {})", sexp(scrutinee), arms.join(" "))
        }
        other => panic!("a loop lowers to no {other:?}"),
    }
}

/// A program that declares the list tags the prelude would.
fn with_lists(source: &str) -> String {
    format!("tag List = Empty | Link(_, List)\n{source}")
}

fn lowered_loop(source: &str) -> String {
    sexp(&lowered_root(source))
}

/// The shape of a counted loop with the body `body` and the comparison `cmp`
/// of the counter `i`: `counted` in `GoatDen.v`.
fn counted(start: &str, stop: &str, cmp: &str, i: &str, body: &str) -> String {
    format!(
        "(let start {start} (let stop {stop} (let loop (fn ({i}) \
         (if ({cmp} {i} stop) (let _ {body} (loop (+ {i} 1))) ())) (loop start))))"
    )
}

#[test]
fn repeat_counts_from_zero_below_the_count() {
    assert_eq!(
        lowered_loop("repeat 2 times do done"),
        counted("0", "2", "<", "count", "()")
    );
}

#[test]
fn for_counts_from_the_start_to_the_stop_inclusive() {
    assert_eq!(
        lowered_loop("for i from 1 to 3 do i done"),
        counted("1", "3", "<=", "i", "i")
    );
}

#[test]
fn a_loop_body_is_run_before_the_next_step() {
    assert_eq!(
        lowered_loop("n = 4\nrepeat n times do n done"),
        format!("(let n 4 {})", counted("0", "n", "<", "count", "n"))
    );
}

#[test]
fn for_in_walks_the_list_on_empty_and_link() {
    assert_eq!(
        lowered_loop(&with_lists("for x in [1, 2] do x done")),
        "(let loop (fn (list) (match list (Empty ()) (Link 0=x 1=list (let _ x (loop list))))) \
         (loop (Link {0=1 1=(Link {0=2 1=Empty})})))"
    );
}

#[test]
fn an_absent_body_is_unit() {
    assert_eq!(
        lowered_loop(&with_lists("for x in [] do done")),
        "(let loop (fn (list) (match list (Empty ()) (Link 0=x 1=list (let _ () (loop list))))) \
         (loop Empty))"
    );
}
