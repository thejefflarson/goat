//! Hindley-Milner type inference over the [`hir`].
//!
//! The inferer walks the tree, generating and immediately solving equality
//! constraints through [`Inferer::unify`] (which maintains a substitution from
//! type variables to types). Declarations are generalized so let-bound names
//! are polymorphic; function parameters stay monomorphic within the body.

use crate::error::GoatError;
use crate::hir::{Expr, ExprId, ExprKind, Span, Symbol};
use crate::ty::{Scheme, Ty, TypeVar};
use std::collections::{BTreeSet, HashMap};

/// The result of checking a program: the program's own type, plus the resolved
/// type of every node (keyed by [`ExprId`]) for later phases.
pub struct Typed {
    pub root_ty: Ty,
    pub node_types: HashMap<ExprId, Ty>,
}

pub fn infer(root: &Expr) -> Result<Typed, Vec<GoatError>> {
    let mut inf = Inferer::default();
    let ty = inf.infer(root);
    if inf.errors.is_empty() {
        let root_ty = inf.resolve(&ty);
        let node_types = inf
            .node_types
            .iter()
            .map(|(id, t)| (*id, inf.resolve(t)))
            .collect();
        Ok(Typed {
            root_ty,
            node_types,
        })
    } else {
        Err(inf.errors)
    }
}

#[derive(Default)]
struct Inferer {
    next: TypeVar,
    subst: HashMap<TypeVar, Ty>,
    env: HashMap<Symbol, Scheme>,
    node_types: HashMap<ExprId, Ty>,
    errors: Vec<GoatError>,
}

impl Inferer {
    fn fresh(&mut self) -> Ty {
        let v = self.next;
        self.next += 1;
        Ty::Var(v)
    }

    /// Follow the substitution to the type's current best-known form.
    fn resolve(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::Var(v) => match self.subst.get(v) {
                Some(t) => self.resolve(t),
                None => Ty::Var(*v),
            },
            Ty::Func(args, ret) => Ty::Func(
                args.iter().map(|a| self.resolve(a)).collect(),
                Box::new(self.resolve(ret)),
            ),
            other => other.clone(),
        }
    }

    fn unify(&mut self, a: &Ty, b: &Ty, span: Span) {
        let a = self.resolve(a);
        let b = self.resolve(b);
        match (&a, &b) {
            (Ty::Var(x), Ty::Var(y)) if x == y => {}
            (Ty::Var(x), t) | (t, Ty::Var(x)) => {
                if occurs(*x, t) {
                    self.errors.push(GoatError::new(
                        span,
                        format!("cannot construct the infinite type `{a}` = `{b}`"),
                    ));
                } else {
                    self.subst.insert(*x, t.clone());
                }
            }
            (Ty::Number, Ty::Number)
            | (Ty::Str, Ty::Str)
            | (Ty::Bool, Ty::Bool)
            | (Ty::Unit, Ty::Unit) => {}
            (Ty::Func(a_args, a_ret), Ty::Func(b_args, b_ret)) => {
                if a_args.len() != b_args.len() {
                    self.errors.push(GoatError::new(
                        span,
                        format!(
                            "function expects {} argument(s) but got {}",
                            a_args.len(),
                            b_args.len()
                        ),
                    ));
                    return;
                }
                for (x, y) in a_args.iter().zip(b_args) {
                    self.unify(x, y, span);
                }
                self.unify(a_ret, b_ret, span);
            }
            _ => {
                self.errors.push(GoatError::new(
                    span,
                    format!("type mismatch: expected `{a}`, found `{b}`"),
                ));
            }
        }
    }

    fn instantiate(&mut self, scheme: &Scheme) -> Ty {
        let mapping: HashMap<TypeVar, Ty> =
            scheme.vars.iter().map(|v| (*v, self.fresh())).collect();
        subst_vars(&scheme.ty, &mapping)
    }

    fn generalize(&self, ty: &Ty) -> Scheme {
        let resolved = self.resolve(ty);
        let mut in_ty = BTreeSet::new();
        resolved.free_vars(&mut in_ty);
        let in_env = self.env_free_vars();
        let vars = in_ty.difference(&in_env).copied().collect();
        Scheme { vars, ty: resolved }
    }

    fn env_free_vars(&self) -> BTreeSet<TypeVar> {
        let mut out = BTreeSet::new();
        for scheme in self.env.values() {
            let mut free = BTreeSet::new();
            self.resolve(&scheme.ty).free_vars(&mut free);
            for bound in &scheme.vars {
                free.remove(bound);
            }
            out.extend(free);
        }
        out
    }

    fn infer(&mut self, expr: &Expr) -> Ty {
        let ty = self.infer_kind(expr);
        self.node_types.insert(expr.id, ty.clone());
        ty
    }

    fn infer_kind(&mut self, expr: &Expr) -> Ty {
        match &expr.kind {
            ExprKind::Unit => Ty::Unit,
            ExprKind::Number(_) => Ty::Number,
            ExprKind::Str(_) => Ty::Str,
            ExprKind::Bool(_) => Ty::Bool,
            ExprKind::Var { symbol, .. } => match self.env.get(symbol).cloned() {
                Some(scheme) => self.instantiate(&scheme),
                None => self.fresh(),
            },
            ExprKind::Func { params, body } => {
                let arg_tys: Vec<Ty> = params.iter().map(|_| self.fresh()).collect();
                for (param, ty) in params.iter().zip(&arg_tys) {
                    self.env.insert(param.symbol, Scheme::mono(ty.clone()));
                }
                let ret = self.infer(body);
                for param in params {
                    self.env.remove(&param.symbol);
                }
                Ty::func(arg_tys, ret)
            }
            ExprKind::App { callee, args } => {
                let callee_ty = self.infer(callee);
                let arg_tys: Vec<Ty> = args.iter().map(|a| self.infer(a)).collect();
                let ret = self.fresh();
                let expected = Ty::func(arg_tys, ret.clone());
                self.unify(&callee_ty, &expected, expr.span);
                ret
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_ty = self.infer(cond);
                self.unify(&cond_ty, &Ty::Bool, cond.span);
                let then_ty = self.infer(then_branch);
                match else_branch {
                    Some(else_expr) => {
                        let else_ty = self.infer(else_expr);
                        self.unify(&then_ty, &else_ty, expr.span);
                        then_ty
                    }
                    // Without an else branch the conditional is a statement: its
                    // value is Unit and the then-branch's value is discarded.
                    None => Ty::Unit,
                }
            }
            ExprKind::Let {
                symbol,
                value,
                rest,
                ..
            } => {
                // Bind a fresh monomorphic type before checking the value so the
                // value may refer to itself (recursion).
                let rec = self.fresh();
                self.env.insert(*symbol, Scheme::mono(rec.clone()));
                let value_ty = self.infer(value);
                self.unify(&rec, &value_ty, value.span);
                self.env.remove(symbol);

                let scheme = self.generalize(&rec);
                self.env.insert(*symbol, scheme.clone());
                let result = match rest {
                    Some(rest) => self.infer(rest),
                    None => self.instantiate(&scheme),
                };
                self.env.remove(symbol);
                result
            }
            ExprKind::Bin { op, lhs, rhs } => {
                let lhs_ty = self.infer(lhs);
                let rhs_ty = self.infer(rhs);
                self.unify(&lhs_ty, &Ty::Number, lhs.span);
                self.unify(&rhs_ty, &Ty::Number, rhs.span);
                if op.is_comparison() {
                    Ty::Bool
                } else {
                    Ty::Number
                }
            }
        }
    }
}

fn occurs(var: TypeVar, ty: &Ty) -> bool {
    match ty {
        Ty::Var(v) => *v == var,
        Ty::Func(args, ret) => args.iter().any(|a| occurs(var, a)) || occurs(var, ret),
        _ => false,
    }
}

fn subst_vars(ty: &Ty, mapping: &HashMap<TypeVar, Ty>) -> Ty {
    match ty {
        Ty::Var(v) => mapping.get(v).cloned().unwrap_or(Ty::Var(*v)),
        Ty::Func(args, ret) => Ty::Func(
            args.iter().map(|a| subst_vars(a, mapping)).collect(),
            Box::new(subst_vars(ret, mapping)),
        ),
        other => other.clone(),
    }
}
