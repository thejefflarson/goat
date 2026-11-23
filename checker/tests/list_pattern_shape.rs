//! The decision tree lowering builds for a list pattern, which `ltree`, `lmatch`,
//! `lit_bind` and `lps_wrap` in `proofs/GoatDen.v` denote (ADR 0030): the arms
//! of a `match` on `Empty` and `Link`, one nested match for each item the
//! pattern takes, a `let` for each name read off the list node the tree took
//! apart, and the trap (which the proof writes as a term that never returns)
//! where a destructuring can miss. A variable prints as its distance to its
//! binder, so a test pins what each name is bound to and not the names.

use goat_checker::hir::{Expr, ExprKind, Symbol};
use goat_checker::lower::lower_with_prelude;

const LISTS: &str = "tag List = Empty | Link(_, List)\n";

fn lowered_root(source: &str) -> Expr {
    let lowered = lower_with_prelude(LISTS, source)
        .unwrap_or_else(|e| panic!("{source:?} does not parse: {e:?}"));
    assert!(
        lowered.errors.is_empty(),
        "{source:?} lowers with errors: {:?}",
        lowered.errors
    );
    lowered.root
}

fn sexp(e: &Expr, scope: &mut Vec<Symbol>) -> String {
    match &e.kind {
        ExprKind::Unit => "()".into(),
        ExprKind::Int(n) => n.to_string(),
        ExprKind::Trap(_) => "trap".into(),
        ExprKind::Var { symbol, name } => {
            let depth = scope
                .iter()
                .rev()
                .position(|s| s == symbol)
                .unwrap_or_else(|| panic!("{name} is unbound"));
            format!("#{depth}")
        }
        ExprKind::Tag { name, payload, .. } => match payload.as_deref() {
            None => name.clone(),
            Some(Expr {
                kind: ExprKind::Record { fields },
                ..
            }) => {
                let items: Vec<_> = fields.iter().map(|(_, v)| sexp(v, scope)).collect();
                format!("({name} {})", items.join(" "))
            }
            Some(other) => format!("({name} {})", sexp(other, scope)),
        },
        ExprKind::Let {
            symbol,
            value,
            rest,
            ..
        } => {
            let value = sexp(value, scope);
            scope.push(*symbol);
            let rest = rest.as_ref().map_or("()".to_string(), |r| sexp(r, scope));
            scope.pop();
            format!("(let {value} {rest})")
        }
        ExprKind::Func { params, body } => {
            scope.extend(params.iter().map(|p| p.symbol));
            let body = sexp(body, scope);
            scope.truncate(scope.len() - params.len());
            format!("(fn {} {body})", params.len())
        }
        ExprKind::Match {
            scrutinee,
            arms,
            else_branch,
        } => {
            let mut out = format!("(match {}", sexp(scrutinee, scope));
            for arm in arms {
                let binders: Vec<_> = arm.pattern.payload.binders().collect();
                scope.extend(binders.iter().map(|p| p.symbol));
                let body = sexp(&arm.body, scope);
                scope.truncate(scope.len() - binders.len());
                out.push_str(&format!(" ({} {} {body})", arm.pattern.tag, binders.len()));
            }
            if let Some(other) = else_branch {
                out.push_str(&format!(" else {}", sexp(other, scope)));
            }
            out.push(')');
            out
        }
        other => panic!("a list pattern lowers to no {other:?}"),
    }
}

fn lowered(source: &str) -> String {
    sexp(&lowered_root(source), &mut Vec::new())
}

#[test]
fn two_arms_are_one_match_whose_link_arm_names_the_item_and_the_rest() {
    assert_eq!(
        lowered("f = program(xs) do match xs do [] then 0 [a, ...r] then a done done"),
        "(let (fn 1 (match #0 (Empty 0 0) (Link 2 (let #1 (let #1 #1))))) ())"
    );
}

#[test]
fn arms_that_share_a_prefix_share_the_matches_that_read_it() {
    assert_eq!(
        lowered(
            "f = program(xs) do match xs do [a, b] then a [a, ...r] then a [] then 0 done done"
        ),
        "(let (fn 1 (match #0 (Empty 0 0) (Link 2 (match #0 (Empty 0 (let #1 (let #1 #1))) \
         (Link 2 (match #0 (Empty 0 (let #3 (let #2 #1))) (Link 2 (let #5 (let #5 #1))))))))) ())"
    );
}

#[test]
fn an_else_stands_in_for_each_missing_arm_of_a_one_arm_match() {
    assert_eq!(
        lowered("f = program(xs) do match xs do [a] then a else 0 done done"),
        "(let (fn 1 (match #0 (Link 2 (match #0 (Empty 0 (let #1 #0)) else 0)) else 0)) ())"
    );
}

#[test]
fn a_destructuring_nests_a_match_for_each_item_and_traps_where_it_can_miss() {
    assert_eq!(
        lowered("f = program(xs) do [a, b] = xs a done"),
        "(let (fn 1 (let #0 (match #0 (Link 2 (match #0 (Link 2 (match #0 \
         (Empty 0 (let #3 (let #2 #1))) else trap)) else trap)) else trap))) ())"
    );
}

#[test]
fn a_literal_that_fits_binds_each_name_to_its_item_and_the_rest_to_what_is_left() {
    assert_eq!(
        lowered("[a, ...r] = [1, 2] a"),
        "(let 1 (let 2 (let #1 (let (Link #1 Empty) #1))))"
    );
}

#[test]
fn a_list_parameter_is_unpacked_from_a_variable_of_its_own() {
    assert_eq!(
        lowered("f = program([a, ...r], n) do a done"),
        "(let (fn 2 (match #1 (Link 2 (let #1 (let #1 #1))) else trap)) ())"
    );
}

#[test]
fn a_rest_name_alone_binds_a_scrutinee_that_is_not_a_variable() {
    assert_eq!(
        lowered("match [1] do [...r] then 0 done"),
        "(let (Link 1 Empty) (let #0 0))"
    );
}
