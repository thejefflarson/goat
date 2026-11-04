//! Which enclosing variables each function literal holds, shared by the order
//! check here and by monomorphization so the two cannot disagree.

use crate::hir::{Expr, ExprId, ExprKind, Param, Symbol};
use std::collections::{HashMap, HashSet};

/// A function literal's identity: a `name = program(...)` binding, or an
/// anonymous literal keyed by its expression.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Target {
    Named(Symbol),
    Anon(ExprId),
}

/// Each literal's captures, in `Capture` index order: its free variables, where
/// a referenced function binding contributes that function's captures instead
/// of itself.
pub fn capture_sets(root: &Expr) -> HashMap<Target, Vec<Symbol>> {
    let mut free = Vec::new();
    collect(root, &mut free);
    resolve(&free)
}

fn collect(e: &Expr, free: &mut Vec<(Target, Vec<Symbol>)>) {
    match &e.kind {
        ExprKind::Let {
            symbol,
            value,
            rest,
            ..
        } => {
            match &value.kind {
                ExprKind::Func { params, body } => {
                    let mut symbols = free_symbols(params, body);
                    symbols.retain(|s| s != symbol);
                    free.push((Target::Named(*symbol), symbols));
                    collect(body, free);
                }
                _ => collect(value, free),
            }
            if let Some(rest) = rest {
                collect(rest, free);
            }
        }
        ExprKind::Func { params, body } => {
            free.push((Target::Anon(e.id), free_symbols(params, body)));
            collect(body, free);
        }
        _ => for_each_child(e, &mut |c| collect(c, free)),
    }
}

/// Lists only grow and keep their order, so mutually recursive functions
/// settle on a common set.
fn resolve(free: &[(Target, Vec<Symbol>)]) -> HashMap<Target, Vec<Symbol>> {
    let mut sets: HashMap<Target, Vec<Symbol>> =
        free.iter().map(|(t, _)| (*t, Vec::new())).collect();
    let mut changed = true;
    while changed {
        changed = false;
        for (target, symbols) in free {
            let mut captures = sets[target].clone();
            let before = captures.len();
            for s in symbols {
                let wanted = match sets.get(&Target::Named(*s)) {
                    Some(function) => function.clone(),
                    None => vec![*s],
                };
                for c in wanted {
                    if !captures.contains(&c) {
                        captures.push(c);
                    }
                }
            }
            changed |= captures.len() != before;
            sets.insert(*target, captures);
        }
    }
    sets
}

/// The symbols `body` uses that neither it nor `params` bind, in order of
/// first use.
fn free_symbols(params: &[Param], body: &Expr) -> Vec<Symbol> {
    fn scan(e: &Expr, used: &mut Vec<Symbol>, bound: &mut HashSet<Symbol>) {
        match &e.kind {
            ExprKind::Var { symbol, .. } if !used.contains(symbol) => used.push(*symbol),
            ExprKind::Let { symbol, .. } => {
                bound.insert(*symbol);
            }
            ExprKind::Func { params, .. } => bound.extend(params.iter().map(|p| p.symbol)),
            ExprKind::Match { arms, .. } => {
                for arm in arms {
                    bound.extend(arm.pattern.payload.binders().map(|p| p.symbol));
                }
            }
            _ => {}
        }
        for_each_child(e, &mut |c| scan(c, used, bound));
    }
    let mut used = Vec::new();
    let mut bound: HashSet<_> = params.iter().map(|p| p.symbol).collect();
    scan(body, &mut used, &mut bound);
    used.retain(|s| !bound.contains(s));
    used
}

pub fn for_each_child<'a>(e: &'a Expr, f: &mut impl FnMut(&'a Expr)) {
    match &e.kind {
        ExprKind::Let { value, rest, .. } => {
            f(value);
            rest.iter().for_each(|r| f(r));
        }
        ExprKind::Func { body, .. } => f(body),
        ExprKind::App { callee, args } => {
            f(callee);
            args.iter().for_each(f);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            f(cond);
            f(then_branch);
            else_branch.iter().for_each(|e| f(e));
        }
        ExprKind::Bin { lhs, rhs, .. } => {
            f(lhs);
            f(rhs);
        }
        ExprKind::Record { fields } => fields.iter().for_each(|(_, v)| f(v)),
        ExprKind::Spread { base, fields } => {
            f(base);
            fields.iter().for_each(|(_, v)| f(v));
        }
        ExprKind::Restrict { record, .. } | ExprKind::Field { record, .. } => f(record),
        ExprKind::Tag { payload, .. } => payload.iter().for_each(|p| f(p)),
        ExprKind::Match {
            scrutinee,
            arms,
            else_branch,
        } => {
            f(scrutinee);
            arms.iter().for_each(|a| f(&a.body));
            else_branch.iter().for_each(|e| f(e));
        }
        ExprKind::Unit
        | ExprKind::Number(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Builtin(_)
        | ExprKind::Var { .. } => {}
    }
}
