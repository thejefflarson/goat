//! Hindley-Milner type inference over the [`hir`].
//!
//! The inferer walks the tree, generating and immediately solving equality
//! constraints through [`Inferer::unify`] (which maintains a substitution from
//! type and row variables to types and rows). Declarations are generalized so
//! let-bound names are polymorphic; function parameters stay monomorphic within
//! the body.
//!
//! Records use row types with scoped-label unification (Leijen): to unify a
//! record carrying field `l` against another record, [`Inferer::rewrite_row`]
//! surfaces `l` in the other row — extending an open row (one ending in a row
//! variable) with `l` when needed — then the field types and the remaining rows
//! unify. Field access unifies the record against an open row `{l: t | rest}`,
//! so it accepts any record that has at least field `l`.

use crate::error::GoatError;
use crate::hir::{Expr, ExprId, ExprKind, Span, Symbol};
use crate::ty::{Row, Scheme, Ty, TypeVar};
use std::collections::{BTreeSet, HashMap};

/// The result of checking a program: the program's own type, plus the resolved
/// type of every node (keyed by [`ExprId`]) for later phases.
pub struct Typed {
    pub root_ty: Ty,
    pub node_types: HashMap<ExprId, Ty>,
    /// The generalized scheme of every `let`-bound symbol. A `Var` use site's
    /// node type is the scheme instantiated at that use; nodes inside the
    /// binding's value still mention the scheme's quantified variables.
    /// `Symbol`s are unique per binding site, so they key this map alone.
    pub schemes: HashMap<Symbol, Scheme>,
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
        let schemes = inf
            .schemes
            .iter()
            .map(|(symbol, s)| {
                let scheme = Scheme {
                    vars: s.vars.clone(),
                    ty: inf.resolve(&s.ty),
                };
                (*symbol, scheme)
            })
            .collect();
        Ok(Typed {
            root_ty,
            node_types,
            schemes,
        })
    } else {
        Err(inf.errors)
    }
}

#[derive(Default)]
struct Inferer {
    next: TypeVar,
    subst: HashMap<TypeVar, Ty>,
    row_subst: HashMap<TypeVar, Row>,
    env: HashMap<Symbol, Scheme>,
    params: HashMap<Symbol, String>,
    node_types: HashMap<ExprId, Ty>,
    schemes: HashMap<Symbol, Scheme>,
    errors: Vec<GoatError>,
}

impl Inferer {
    fn fresh_id(&mut self) -> TypeVar {
        let v = self.next;
        self.next += 1;
        v
    }

    fn fresh(&mut self) -> Ty {
        Ty::Var(self.fresh_id())
    }

    fn fresh_row(&mut self) -> Row {
        Row::Var(self.fresh_id())
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
            Ty::Record(row) => Ty::Record(self.resolve_row(row)),
            other => other.clone(),
        }
    }

    fn resolve_row(&self, row: &Row) -> Row {
        match row {
            Row::Var(v) => match self.row_subst.get(v) {
                Some(r) => self.resolve_row(r),
                None => Row::Var(*v),
            },
            Row::Extend { label, field, rest } => Row::Extend {
                label: label.clone(),
                field: Box::new(self.resolve(field)),
                rest: Box::new(self.resolve_row(rest)),
            },
            Row::Empty => Row::Empty,
        }
    }

    /// For a parameter or a field chain off one, the parameter's name and the
    /// written path (`m`, `m.id`).
    fn param_path(&self, expr: &Expr) -> Option<(String, String)> {
        match &expr.kind {
            ExprKind::Var { symbol, name } => self
                .params
                .contains_key(symbol)
                .then(|| (name.clone(), name.clone())),
            ExprKind::Field { record, label } => {
                let (root, path) = self.param_path(record)?;
                Some((root, format!("{path}.{label}")))
            }
            _ => None,
        }
    }

    /// Unify the type of `used`, which the surrounding expression needs to be
    /// `expected`. When `used` is a parameter (or a field of one) that an
    /// earlier use already fixed, a failure is the monomorphic-parameter
    /// limitation, so say that instead of a bare mismatch.
    fn unify_use(&mut self, used: &Expr, actual: &Ty, expected: &Ty, span: Span) {
        let reused = !matches!(self.resolve(actual), Ty::Var(_));
        let before = self.errors.len();
        self.unify(actual, expected, span);
        if reused
            && self.errors.len() > before
            && let Some((root, path)) = self.param_path(used)
        {
            self.errors.truncate(before);
            let what = if path == root { "it" } else { path.as_str() };
            self.errors.push(GoatError::new(
                span,
                format!(
                    "`{root}` is a parameter, so {what} can only be used at one type here; bind it with `=` instead"
                ),
            ));
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
                    self.unify(y, x, span);
                }
                self.unify(a_ret, b_ret, span);
            }
            (Ty::Record(a_row), Ty::Record(b_row)) => {
                self.unify_row(a_row, b_row, span);
            }
            _ => {
                self.errors.push(GoatError::new(
                    span,
                    format!("type mismatch: expected `{b}`, found `{a}`"),
                ));
            }
        }
    }

    fn unify_row(&mut self, a: &Row, b: &Row, span: Span) {
        let a = self.resolve_row(a);
        let b = self.resolve_row(b);
        match (&a, &b) {
            (Row::Empty, Row::Empty) => {}
            (Row::Var(x), Row::Var(y)) if x == y => {}
            (Row::Var(x), other) | (other, Row::Var(x)) => {
                if occurs_row(*x, other) {
                    self.errors.push(GoatError::new(
                        span,
                        "cannot construct an infinite record type".to_string(),
                    ));
                } else {
                    self.row_subst.insert(*x, other.clone());
                }
            }
            (Row::Extend { label, field, rest }, _) => match self.rewrite_row(label, &b) {
                Some((b_field, b_rest)) => {
                    self.unify(field, &b_field, span);
                    self.unify_row(rest, &b_rest, span);
                }
                None => {
                    self.errors.push(GoatError::new(
                        span,
                        format!("record has an unexpected field `{label}`"),
                    ));
                }
            },
            (Row::Empty, Row::Extend { label, .. }) => {
                self.errors.push(GoatError::new(
                    span,
                    format!("record is missing field `{label}`"),
                ));
            }
        }
    }

    /// Surface `label` in `row`, returning its field type and the row without
    /// it. An open row (ending in a row variable) is grown with a fresh field;
    /// a closed row missing the label yields `None`. Differing labels ahead of
    /// `label` keep their position, which is what makes labels scoped.
    fn rewrite_row(&mut self, label: &str, row: &Row) -> Option<(Ty, Row)> {
        match self.resolve_row(row) {
            Row::Empty => None,
            Row::Extend {
                label: l2,
                field,
                rest,
            } => {
                if l2 == label {
                    Some((*field, *rest))
                } else {
                    let (f, r) = self.rewrite_row(label, &rest)?;
                    Some((
                        f,
                        Row::Extend {
                            label: l2,
                            field,
                            rest: Box::new(r),
                        },
                    ))
                }
            }
            Row::Var(v) => {
                let field = self.fresh();
                let rest = self.fresh_row();
                let grown = Row::Extend {
                    label: label.to_string(),
                    field: Box::new(field.clone()),
                    rest: Box::new(rest.clone()),
                };
                self.row_subst.insert(v, grown);
                Some((field, rest))
            }
        }
    }

    fn instantiate(&mut self, scheme: &Scheme) -> Ty {
        let mapping: HashMap<TypeVar, TypeVar> =
            scheme.vars.iter().map(|v| (*v, self.fresh_id())).collect();
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

    /// Give each function binding in the `Let` chain from `expr` a monomorphic
    /// type up front, so bodies can use bindings not yet inferred (self and
    /// mutual recursion). Each is generalized when its own `Let` is reached.
    fn seed_function_group(&mut self, expr: &Expr) {
        let mut cursor = Some(expr);
        while let Some(Expr {
            kind:
                ExprKind::Let {
                    symbol,
                    value,
                    rest,
                    ..
                },
            ..
        }) = cursor
        {
            if matches!(value.kind, ExprKind::Func { .. }) && !self.env.contains_key(symbol) {
                let ty = self.fresh();
                self.env.insert(*symbol, Scheme::mono(ty));
            }
            cursor = rest.as_deref();
        }
    }

    fn infer(&mut self, expr: &Expr) -> Ty {
        let ty = self.infer_kind(expr);
        self.node_types.insert(expr.id, ty.clone());
        ty
    }

    #[cold]
    fn report_not_callable(&mut self, span: Span, ty: &Ty) {
        self.errors.push(GoatError::new(
            span,
            format!(
                "`{ty}` is not a function and can't be called; a `(…)` right after an expression is read as a call"
            ),
        ));
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
                    self.params.insert(param.symbol, param.name.clone());
                }
                let ret = self.infer(body);
                for param in params {
                    self.env.remove(&param.symbol);
                    self.params.remove(&param.symbol);
                }
                Ty::func(arg_tys, ret)
            }
            ExprKind::App { callee, args } => {
                let callee_ty = self.infer(callee);
                let arg_tys: Vec<Ty> = args.iter().map(|a| self.infer(a)).collect();
                let ret = self.fresh();
                match self.resolve(&callee_ty) {
                    Ty::Func(..) | Ty::Var(_) => {
                        let expected = Ty::func(arg_tys, ret.clone());
                        self.unify_use(callee, &callee_ty, &expected, expr.span);
                    }
                    // A `(…)` immediately after an expression is read as a
                    // call, so calling a non-function is often a sequencing
                    // mistake. Reporting lives in a cold helper to keep this
                    // deeply-recursed match's stack frame small.
                    other => self.report_not_callable(callee.span, &other),
                }
                ret
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_ty = self.infer(cond);
                self.unify_use(cond, &cond_ty, &Ty::Bool, cond.span);
                let then_ty = self.infer(then_branch);
                match else_branch {
                    Some(else_expr) => {
                        let else_ty = self.infer(else_expr);
                        self.unify(&else_ty, &then_ty, else_expr.span);
                        then_ty
                    }
                    None => {
                        self.unify(&then_ty, &Ty::Unit, then_branch.span);
                        Ty::Unit
                    }
                }
            }
            ExprKind::Let {
                symbol,
                value,
                rest,
                ..
            } => {
                if matches!(value.kind, ExprKind::Func { .. }) {
                    self.seed_function_group(expr);
                }
                let value_ty = self.infer(value);
                let rec = match self.env.remove(symbol) {
                    Some(seed) => {
                        self.unify(&value_ty, &seed.ty, value.span);
                        seed.ty
                    }
                    None => value_ty,
                };

                let scheme = self.generalize(&rec);
                self.env.insert(*symbol, scheme.clone());
                self.schemes.insert(*symbol, scheme.clone());
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
                self.unify_use(lhs, &lhs_ty, &Ty::Number, lhs.span);
                self.unify_use(rhs, &rhs_ty, &Ty::Number, rhs.span);
                if op.is_comparison() {
                    Ty::Bool
                } else {
                    Ty::Number
                }
            }
            ExprKind::Record { fields } => {
                let field_tys: Vec<(String, Ty)> = fields
                    .iter()
                    .map(|(label, value)| (label.clone(), self.infer(value)))
                    .collect();
                // Build the closed row back-to-front so field order is kept.
                let mut row = Row::Empty;
                for (label, ty) in field_tys.into_iter().rev() {
                    row = Row::Extend {
                        label,
                        field: Box::new(ty),
                        rest: Box::new(row),
                    };
                }
                Ty::Record(row)
            }
            ExprKind::Field { record, label } => {
                let record_ty = self.infer(record);
                let field_ty = self.fresh();
                let rest = self.fresh_row();
                let expected = Ty::Record(Row::Extend {
                    label: label.clone(),
                    field: Box::new(field_ty.clone()),
                    rest: Box::new(rest),
                });
                self.unify(&record_ty, &expected, expr.span);
                field_ty
            }
        }
    }
}

fn occurs(var: TypeVar, ty: &Ty) -> bool {
    match ty {
        Ty::Var(v) => *v == var,
        Ty::Func(args, ret) => args.iter().any(|a| occurs(var, a)) || occurs(var, ret),
        Ty::Record(row) => occurs_row(var, row),
        _ => false,
    }
}

fn occurs_row(var: TypeVar, row: &Row) -> bool {
    match row {
        Row::Empty => false,
        Row::Var(v) => *v == var,
        Row::Extend { field, rest, .. } => occurs(var, field) || occurs_row(var, rest),
    }
}

fn subst_vars(ty: &Ty, mapping: &HashMap<TypeVar, TypeVar>) -> Ty {
    match ty {
        Ty::Var(v) => Ty::Var(mapping.get(v).copied().unwrap_or(*v)),
        Ty::Func(args, ret) => Ty::Func(
            args.iter().map(|a| subst_vars(a, mapping)).collect(),
            Box::new(subst_vars(ret, mapping)),
        ),
        Ty::Record(row) => Ty::Record(subst_row(row, mapping)),
        other => other.clone(),
    }
}

fn subst_row(row: &Row, mapping: &HashMap<TypeVar, TypeVar>) -> Row {
    match row {
        Row::Empty => Row::Empty,
        Row::Var(v) => Row::Var(mapping.get(v).copied().unwrap_or(*v)),
        Row::Extend { label, field, rest } => Row::Extend {
            label: label.clone(),
            field: Box::new(subst_vars(field, mapping)),
            rest: Box::new(subst_row(rest, mapping)),
        },
    }
}
