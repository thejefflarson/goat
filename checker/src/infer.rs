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
//!
//! Variants are the dual, on the same rows: a label is a tag and its field type
//! is the payload. Constructing a tag yields an open row `[Circle: Number | ρ]`;
//! each `match` arm extends the scrutinee's row with its tag, and a `match`
//! without `else` then closes it.
//!
//! A cycle in a type is allowed only when it passes through a variant payload
//! (`Link(1, rest)` where `rest` is the same list type). Binding a variable to
//! a type that mentions it then records a [`Ty::Rec`] instead of failing the
//! occurs check; any other cycle (`f(f)`) stays an error. The substitution
//! itself stays acyclic, so [`Inferer::resolve`] terminates structurally;
//! unification of two recursive types terminates through the assumed-equal set
//! on [`Inferer::unify_ty`].

use crate::error::GoatError;
use crate::hir::{BinOp, Builtin, Expr, ExprId, ExprKind, MatchArm, PatternPayload, Span, Symbol};
use crate::kinds::{Kind, Kinds, Offender, Violation, is_list_tag};
use crate::ty::{Row, Scheme, Ty, TypeVar};
use std::collections::{BTreeSet, HashMap, HashSet};

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
    /// The type of every `match` pattern binder, in terms of the type variables
    /// of the function it sits in (like a parameter's type).
    pub binder_types: HashMap<Symbol, Ty>,
    /// Diagnostics that do not stop compilation.
    pub warnings: Vec<GoatError>,
}

pub fn infer(root: &Expr) -> Result<Typed, Vec<GoatError>> {
    let mut inf = Inferer::default();
    let ty = inf.infer(root);
    if inf.errors.is_empty() {
        let warnings = inf.unused_tag_warnings();
        let root_ty = inf.finish(&ty);
        let node_types = inf
            .node_types
            .iter()
            .map(|(id, t)| (*id, inf.finish(t)))
            .collect();
        let schemes = inf
            .schemes
            .iter()
            .map(|(symbol, s)| {
                let scheme = Scheme {
                    vars: s.vars.clone(),
                    ty: inf.finish(&s.ty),
                };
                (*symbol, scheme)
            })
            .collect();
        let binder_types = inf
            .binders
            .iter()
            .map(|(symbol, t)| (*symbol, inf.finish(t)))
            .collect();
        Ok(Typed {
            root_ty,
            node_types,
            schemes,
            binder_types,
            warnings,
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
    binders: HashMap<Symbol, Ty>,
    constructed: Vec<(String, Span)>,
    matched: HashSet<String>,
    /// Pairs of types [`Inferer::unify_ty`] is already unifying or has unified,
    /// within one top-level [`Inferer::unify`].
    assumed: HashSet<(Ty, Ty)>,
    /// Row variables that must never gain these labels: `{x, ...rest} = m`
    /// takes only the front `x` out of `m`, so a second `x` behind it (left by a
    /// `...` override) would resurface in `rest`, while the runtime layout
    /// keeps one `x` per record.
    lacks: HashMap<TypeVar, BTreeSet<String>>,
    /// The constraints each unbound type variable must satisfy once it is
    /// bound. Binding a variable checks them against its type and hands them
    /// on to the variables inside it.
    kinds: HashMap<TypeVar, Kinds>,
    /// The same for row variables: every field a row gains must satisfy them.
    row_kinds: HashMap<TypeVar, Kinds>,
    errors: Vec<GoatError>,
}

/// Which table of constraints a variable's lives in.
#[derive(Clone, Copy)]
enum KindMap {
    Ty,
    Row,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RowKind {
    Record,
    Variant,
}

/// What a cycle-closing substitution replaces: a type variable, or every
/// record or variant type whose row is exactly this one (a row variable,
/// possibly behind a prefix of labels).
#[derive(Clone, PartialEq, Eq)]
enum Hole {
    Ty(TypeVar),
    Mention(RowKind, Row),
}

impl RowKind {
    fn noun(self) -> &'static str {
        match self {
            RowKind::Record => "record",
            RowKind::Variant => "variant",
        }
    }

    fn wrap(self, row: Row) -> Ty {
        match self {
            RowKind::Record => Ty::Record(row),
            RowKind::Variant => Ty::Variant(row),
        }
    }
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
            Ty::Variant(row) => Ty::Variant(self.resolve_row(row)),
            Ty::Rec(binder, body) => Ty::Rec(*binder, Box::new(self.resolve(body))),
            other => other.clone(),
        }
    }

    /// [`Self::resolve`] with a recursive type unfolded until its head is a
    /// constructor, for code that inspects the head (`match`, calls).
    fn resolve_head(&self, ty: &Ty) -> Ty {
        self.resolve(ty).unfold_head()
    }

    /// The resolved type in its final shape: every variable substituted, and
    /// recursive types folded back to their `μ` form.
    fn finish(&self, ty: &Ty) -> Ty {
        self.resolve(ty).fold_rec()
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
        self.unify_ty(a, b, span);
        self.assumed.clear();
    }

    fn unify_ty(&mut self, a: &Ty, b: &Ty, span: Span) {
        let a = self.resolve(a);
        let b = self.resolve(b);
        match (&a, &b) {
            (Ty::Var(x), Ty::Var(y)) if x == y => {}
            (Ty::Var(x), t) | (t, Ty::Var(x)) => {
                let bound = if !occurs(*x, t) {
                    t.clone()
                } else if let Some(rec) = self.tie_ty_knot(*x, t) {
                    rec
                } else {
                    self.errors.push(GoatError::new(
                        span,
                        format!("cannot construct the infinite type `{a}` = `{b}`"),
                    ));
                    return;
                };
                self.subst.insert(*x, bound.clone());
                if let Some(kinds) = self.kinds.remove(x)
                    && let Err(violation) = self.constrain(&bound, kinds)
                {
                    self.report_violation(span, &violation, &bound, None);
                }
            }
            (Ty::Rec(..), _) | (_, Ty::Rec(..)) => {
                // Termination: unfolding a `Rec` re-exposes the same `Rec` at
                // every back-edge, so unifying two recursive types would
                // otherwise recurse forever. A pair already in `assumed` is
                // being unified further up (or already was), so it is taken as
                // equal and returns at once. The set only grows within one
                // top-level `unify`, and its pairs are drawn from the finitely
                // many distinct sub-terms of the two types and their
                // unfoldings (a regular tree has finitely many), so the
                // recursion depth is bounded.
                if self.assumed.insert((a.clone(), b.clone())) {
                    self.unify_ty(&a.unfold_head(), &b.unfold_head(), span);
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
                    self.unify_ty(y, x, span);
                }
                self.unify_ty(a_ret, b_ret, span);
            }
            (Ty::Record(a_row), Ty::Record(b_row)) => {
                self.unify_row(a_row, b_row, span, RowKind::Record);
            }
            (Ty::Variant(a_row), Ty::Variant(b_row)) => {
                self.unify_row(a_row, b_row, span, RowKind::Variant);
            }
            _ => {
                self.errors.push(GoatError::new(
                    span,
                    format!("type mismatch: expected `{b}`, found `{a}`"),
                ));
            }
        }
    }

    fn unify_row(&mut self, a: &Row, b: &Row, span: Span, kind: RowKind) {
        let a = self.resolve_row(a);
        let b = self.resolve_row(b);
        match (&a, &b) {
            (Row::Empty, Row::Empty) => {}
            (Row::Var(x), Row::Var(y)) if x == y => {}
            (Row::Var(x), other) | (other, Row::Var(x)) => {
                if let Some(banned) = self.lacks.get(x).cloned()
                    && let Some(label) = self.lack(other, &banned)
                {
                    self.report_hidden_label(span, &label);
                }
                let bound = if !occurs_row(*x, other) {
                    other.clone()
                } else if let Some(rec) = self.tie_row_knot(*x, kind, other) {
                    rec
                } else {
                    self.errors.push(GoatError::new(
                        span,
                        format!("cannot construct an infinite {} type", kind.noun()),
                    ));
                    return;
                };
                self.row_subst.insert(*x, bound.clone());
                if let Some(kinds) = self.row_kinds.remove(x) {
                    for kind_to_check in kinds.iter() {
                        let mut seen = Vec::new();
                        if let Err(violation) = self.constrain_row(&bound, kind_to_check, &mut seen)
                        {
                            self.report_violation(
                                span,
                                &violation,
                                &kind.wrap(bound.clone()),
                                None,
                            );
                            break;
                        }
                    }
                }
            }
            (Row::Extend { label, field, rest }, _) => match self.rewrite_row(label, &b) {
                Some((b_field, b_rest)) => {
                    self.unify_ty(field, &b_field, span);
                    self.unify_row(rest, &b_rest, span, kind);
                }
                None => {
                    let message = match kind {
                        RowKind::Record => format!("record has an unexpected field `{label}`"),
                        RowKind::Variant => format!(
                            "the tag `{label}` is not allowed here; the other side never has it"
                        ),
                    };
                    self.errors.push(GoatError::new(span, message));
                }
            },
            (Row::Empty, Row::Extend { label, .. }) => {
                let message = match kind {
                    RowKind::Record => format!("record is missing field `{label}`"),
                    RowKind::Variant => format!(
                        "the tag `{label}` is expected here, but this value is never `{label}`"
                    ),
                };
                self.errors.push(GoatError::new(span, message));
            }
        }
    }

    /// `x = t` where `t` mentions `x`: the recursive type `μv. t[x := v]`, if
    /// every mention sits under a variant payload.
    fn tie_ty_knot(&mut self, x: TypeVar, t: &Ty) -> Option<Ty> {
        let binder = self.fresh_id();
        let body = plug(t, &Hole::Ty(x), &Ty::Var(binder), false);
        (!occurs(x, &body)).then(|| Ty::Rec(binder, Box::new(body)))
    }

    /// `x = row` where `row` mentions `x`. Allowed only when every mention is
    /// the same `kind` type, `[x]` or `[l: t | x]` (and likewise for records),
    /// under a variant payload: that type is then `row` behind the prefix, so
    /// it is the recursive type `μv. [prefix | row[mention := v]]`. `x` becomes
    /// `row` with that type in place of the mentions.
    fn tie_row_knot(&mut self, x: TypeVar, kind: RowKind, row: &Row) -> Option<Row> {
        let under_tag = kind == RowKind::Variant;
        let mention = find_mention(row, x, kind, under_tag)?;
        let hole = Hole::Mention(kind, mention.clone());
        let binder = self.fresh_id();
        let inner = plug_row(row, &hole, &Ty::Var(binder), under_tag);
        if occurs_row(x, &inner) {
            return None;
        }
        let rec = Ty::Rec(binder, Box::new(kind.wrap(replace_tail(&mention, inner))));
        if occurs(x, &rec) {
            return None;
        }
        Some(plug_row(row, &hole, &rec, under_tag))
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
                let banned = self.lacks.get(&v).cloned().unwrap_or_default();
                if banned.contains(label) {
                    return None;
                }
                let kinds = self.row_kinds.get(&v).copied().unwrap_or_default();
                if kinds.appendable() && !is_list_tag(label) {
                    return None;
                }
                let field = self.fresh();
                let rest = self.fresh_row();
                self.lack(&rest, &banned);
                if let (Ty::Var(f), Row::Var(r)) = (&field, &rest) {
                    self.kinds.insert(*f, kinds.for_fields());
                    self.row_kinds.insert(*r, kinds);
                }
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

    /// Record that `row` may never gain `labels`: pin them on its tail
    /// variable. A label `row` already has makes this impossible, and is
    /// returned.
    fn lack(&mut self, row: &Row, labels: &BTreeSet<String>) -> Option<String> {
        match self.resolve_row(row) {
            Row::Empty => None,
            Row::Var(v) => {
                if !labels.is_empty() {
                    self.lacks
                        .entry(v)
                        .or_default()
                        .extend(labels.iter().cloned());
                }
                None
            }
            Row::Extend { label, rest, .. } => {
                if labels.contains(&label) {
                    Some(label)
                } else {
                    self.lack(&rest, labels)
                }
            }
        }
    }

    #[cold]
    fn report_hidden_label(&mut self, span: Span, label: &str) {
        self.errors.push(GoatError::new(
            span,
            format!(
                "`{label}` is in this record twice (a `...` override hid the first), so it can't be taken out with `...`"
            ),
        ));
    }

    /// Require `ty` to satisfy every constraint in `kinds`. A variable inside
    /// `ty` takes on the constraint, to be checked when it is bound; a type that
    /// can never satisfy it is a [`Violation`].
    fn constrain(&mut self, ty: &Ty, kinds: Kinds) -> Result<(), Violation> {
        kinds
            .iter()
            .try_for_each(|kind| self.constrain_kind(ty, kind, &mut Vec::new()))
    }

    /// `bound` holds the `μ` binders around `ty`: they stand for the type being
    /// walked, which is already being checked.
    fn constrain_kind(
        &mut self,
        ty: &Ty,
        kind: Kind,
        bound: &mut Vec<TypeVar>,
    ) -> Result<(), Violation> {
        let ty = self.resolve(ty);
        let fail = |ty: &Ty| {
            Err(Violation {
                kind,
                offender: Offender::Type(ty.clone()),
            })
        };
        match (&ty, kind) {
            (Ty::Var(v), _) if bound.contains(v) => Ok(()),
            (Ty::Var(v), _) => self.add_kind(KindMap::Ty, *v, kind),
            (Ty::Number, Kind::Eq | Kind::Numeric) => Ok(()),
            (Ty::Str, Kind::Eq | Kind::Appendable) => Ok(()),
            (Ty::Bool | Ty::Unit, Kind::Eq) => Ok(()),
            (Ty::Record(row), Kind::Eq | Kind::Numeric) => self.constrain_row(row, kind, bound),
            (Ty::Variant(row), Kind::Eq) => self.constrain_row(row, kind, bound),
            (Ty::Variant(row), Kind::Appendable) => self.constrain_list(row),
            (Ty::Rec(binder, body), Kind::Eq) => {
                bound.push(*binder);
                let result = self.constrain_kind(body, kind, bound);
                bound.pop();
                result
            }
            (Ty::Rec(..), Kind::Appendable) => match ty.unfold_head() {
                Ty::Variant(row) => self.constrain_list(&row),
                _ => fail(&ty),
            },
            _ => fail(&ty),
        }
    }

    fn constrain_row(
        &mut self,
        row: &Row,
        kind: Kind,
        bound: &mut Vec<TypeVar>,
    ) -> Result<(), Violation> {
        match self.resolve_row(row) {
            Row::Empty => Ok(()),
            Row::Var(v) => self.add_kind(KindMap::Row, v, kind),
            Row::Extend { field, rest, .. } => {
                self.constrain_kind(&field, kind, bound)?;
                self.constrain_row(&rest, kind, bound)
            }
        }
    }

    /// A variant is a list when its tags are only `Empty` and `Link`. An open
    /// row may still grow, so its tail is held to the same tags.
    fn constrain_list(&mut self, row: &Row) -> Result<(), Violation> {
        let mut cursor = self.resolve_row(row);
        loop {
            match cursor {
                Row::Empty => return Ok(()),
                Row::Var(v) => return self.add_kind(KindMap::Row, v, Kind::Appendable),
                Row::Extend { label, rest, .. } => {
                    if !is_list_tag(&label) {
                        return Err(Violation {
                            kind: Kind::Appendable,
                            offender: Offender::Type(Ty::Variant(row.clone())),
                        });
                    }
                    cursor = self.resolve_row(&rest);
                }
            }
        }
    }

    fn add_kind(&mut self, map: KindMap, var: TypeVar, kind: Kind) -> Result<(), Violation> {
        let table = match map {
            KindMap::Ty => &mut self.kinds,
            KindMap::Row => &mut self.row_kinds,
        };
        let kinds = table.entry(var).or_default().with(kind);
        if kinds.conflicts() {
            return Err(Violation {
                kind,
                offender: Offender::Both,
            });
        }
        table.insert(var, kinds);
        Ok(())
    }

    #[cold]
    fn report_violation(
        &mut self,
        span: Span,
        violation: &Violation,
        whole: &Ty,
        op: Option<&str>,
    ) {
        let whole = self.finish(whole);
        self.errors
            .push(GoatError::new(span, violation.message(&whole, op)));
    }

    /// Require `ty` to satisfy `kind` for the operator `op` at `span`. Returns
    /// whether it does.
    fn require(&mut self, ty: &Ty, kind: Kind, op: BinOp, span: Span) -> bool {
        match self.constrain(ty, Kinds::of(kind)) {
            Ok(()) => true,
            Err(violation) => {
                self.report_violation(span, &violation, ty, Some(op.symbol()));
                false
            }
        }
    }

    fn instantiate(&mut self, scheme: &Scheme) -> Ty {
        let mut binders = Vec::new();
        scheme.ty.rec_binders(&mut binders);
        let mapping: HashMap<TypeVar, TypeVar> = scheme
            .vars
            .iter()
            .chain(&binders)
            .map(|v| (*v, self.fresh_id()))
            .collect();
        for (old, new) in &mapping {
            if let Some(banned) = self.lacks.get(old).cloned() {
                self.lacks.insert(*new, banned);
            }
            if let Some(kinds) = self.kinds.get(old).copied() {
                self.kinds.insert(*new, kinds);
            }
            if let Some(kinds) = self.row_kinds.get(old).copied() {
                self.row_kinds.insert(*new, kinds);
            }
        }
        subst_vars(&scheme.ty, &mapping)
    }

    fn generalize(&self, ty: &Ty) -> Scheme {
        let resolved = self.finish(ty);
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
                match self.resolve_head(&callee_ty) {
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
                self.type_bin(expr, *op, (lhs, lhs_ty), (rhs, rhs_ty))
            }
            ExprKind::Builtin(Builtin::Print) => self.print_ty(),
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
            ExprKind::Spread { base, fields } => self.infer_spread(base, fields),
            ExprKind::Restrict { record, labels } => self.infer_restrict(expr.span, record, labels),
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
            ExprKind::Tag { name, payload } => {
                let payload_ty = match payload {
                    Some(p) => self.infer(p),
                    None => Ty::Unit,
                };
                self.constructed.push((name.clone(), expr.span));
                Ty::Variant(Row::Extend {
                    label: name.clone(),
                    field: Box::new(payload_ty),
                    rest: Box::new(self.fresh_row()),
                })
            }
            ExprKind::Match {
                scrutinee,
                arms,
                else_branch,
            } => self.infer_match(scrutinee, arms, else_branch.as_deref()),
        }
    }

    /// The type of `lhs op rhs` given its operands' types. Called after the
    /// operands are inferred, not around them, so it adds nothing to the stack
    /// depth of a long chain of operators.
    #[inline(never)]
    fn type_bin(
        &mut self,
        expr: &Expr,
        op: BinOp,
        (lhs, lhs_ty): (&Expr, Ty),
        (rhs, rhs_ty): (&Expr, Ty),
    ) -> Ty {
        if op.is_arithmetic() {
            if self.require(&lhs_ty, Kind::Numeric, op, lhs.span) {
                self.unify_use(rhs, &rhs_ty, &lhs_ty, rhs.span);
            }
            lhs_ty
        } else if op.is_equality() {
            self.unify_use(rhs, &rhs_ty, &lhs_ty, rhs.span);
            self.require(&lhs_ty, Kind::Eq, op, expr.span);
            Ty::Bool
        } else {
            self.unify_use(lhs, &lhs_ty, &Ty::Number, lhs.span);
            self.unify_use(rhs, &rhs_ty, &Ty::Number, rhs.span);
            Ty::Bool
        }
    }

    fn print_ty(&mut self) -> Ty {
        Ty::func(vec![self.fresh()], Ty::Unit)
    }

    /// `{...base, l: e}`: Leijen's extension of `base`'s row. A label `base`
    /// is already known to have is replaced; one hidden behind its row variable
    /// is shadowed, and the layout keeps only the new field.
    fn infer_spread(&mut self, base: &Expr, fields: &[(String, Expr)]) -> Ty {
        let base_ty = self.infer(base);
        let tail = self.fresh_row();
        match self.resolve_head(&base_ty) {
            Ty::Record(_) | Ty::Var(_) => {
                self.unify(&base_ty, &Ty::Record(tail.clone()), base.span)
            }
            other => self.errors.push(GoatError::new(
                base.span,
                format!("`...` copies a record, but this is `{other}`"),
            )),
        }
        let field_tys: Vec<(String, Ty)> = fields
            .iter()
            .map(|(label, value)| (label.clone(), self.infer(value)))
            .collect();
        // Resolved after the fields are inferred: reading `base.l` in a field
        // grows `base`'s row with `l`, which the override then replaces.
        let mut row = self.resolve_row(&tail);
        for (label, ty) in field_tys.into_iter().rev() {
            row = without_front(row, &label);
            row = Row::Extend {
                label,
                field: Box::new(ty),
                rest: Box::new(row),
            };
        }
        Ty::Record(row)
    }

    /// `record` minus `labels`: the record must have each, and the result is
    /// the rest of its row.
    fn infer_restrict(&mut self, span: Span, record: &Expr, labels: &[String]) -> Ty {
        let record_ty = self.infer(record);
        let tail = self.fresh_row();
        let mut expected = tail.clone();
        for label in labels.iter().rev() {
            expected = Row::Extend {
                label: label.clone(),
                field: Box::new(self.fresh()),
                rest: Box::new(expected),
            };
        }
        self.unify(&record_ty, &Ty::Record(expected), span);
        let banned = labels.iter().cloned().collect();
        if let Some(label) = self.lack(&tail, &banned) {
            self.report_hidden_label(span, &label);
        }
        Ty::Record(tail)
    }

    fn infer_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        else_branch: Option<&Expr>,
    ) -> Ty {
        let scrut_ty = self.infer(scrutinee);
        let is_variant = match self.resolve_head(&scrut_ty) {
            Ty::Variant(_) => true,
            Ty::Var(_) => {
                let open = Ty::Variant(self.fresh_row());
                self.unify(&scrut_ty, &open, scrutinee.span);
                true
            }
            other => {
                self.errors.push(GoatError::new(
                    scrutinee.span,
                    format!(
                        "`match` needs a value built from tags (like `Circle(5)`), but this is `{other}`"
                    ),
                ));
                false
            }
        };

        let mut result: Option<Ty> = None;
        let mut handled: Vec<&str> = Vec::new();
        for arm in arms {
            let pattern = &arm.pattern;
            self.matched.insert(pattern.tag.clone());
            let payload_ty = self.bind_payload(&pattern.payload);
            if is_variant {
                self.constrain_arm(
                    &scrut_ty,
                    pattern.span,
                    &pattern.tag,
                    payload_ty,
                    &mut handled,
                );
            }
            let body_ty = self.infer(&arm.body);
            for binder in pattern.payload.binders() {
                self.env.remove(&binder.symbol);
            }
            self.join_branch(&mut result, body_ty, arm.body.span);
        }
        match else_branch {
            Some(else_expr) => {
                let else_ty = self.infer(else_expr);
                self.join_branch(&mut result, else_ty, else_expr.span);
            }
            None if is_variant => self.close_match(&scrut_ty, &handled, scrutinee.span),
            None => {}
        }
        result.unwrap_or_else(|| self.fresh())
    }

    fn bind_binder(&mut self, symbol: Symbol, ty: &Ty) {
        self.env.insert(symbol, Scheme::mono(ty.clone()));
        self.binders.insert(symbol, ty.clone());
    }

    /// Type the binders of an arm's pattern, returning the payload type the
    /// arm expects.
    fn bind_payload(&mut self, payload: &PatternPayload) -> Ty {
        match payload {
            PatternPayload::None => Ty::Unit,
            PatternPayload::Whole(binder) => {
                let ty = self.fresh();
                self.bind_binder(binder.symbol, &ty);
                ty
            }
            PatternPayload::Fields(fields) => {
                let mut row = Row::Empty;
                for (label, binder) in fields.iter().rev() {
                    let ty = self.fresh();
                    self.bind_binder(binder.symbol, &ty);
                    row = Row::Extend {
                        label: label.clone(),
                        field: Box::new(ty),
                        rest: Box::new(row),
                    };
                }
                Ty::Record(row)
            }
        }
    }

    /// Require the scrutinee to be able to carry `tag` with `payload_ty`.
    fn constrain_arm<'a>(
        &mut self,
        scrut_ty: &Ty,
        span: Span,
        tag: &'a str,
        payload_ty: Ty,
        handled: &mut Vec<&'a str>,
    ) {
        if handled.contains(&tag) {
            self.errors.push(GoatError::new(
                span,
                format!("this arm repeats `{tag}`; an earlier arm already handles it"),
            ));
            return;
        }
        handled.push(tag);
        let Ty::Variant(row) = self.resolve_head(scrut_ty) else {
            return;
        };
        let (tags, tail) = row_shape(&row);
        if tail.is_none() && !tags.iter().any(|t| t == tag) {
            self.errors.push(GoatError::new(
                span,
                format!(
                    "this arm matches `{tag}`, but the value is only ever {}",
                    tag_list(&tags, "or")
                ),
            ));
            return;
        }
        let expected = Ty::Variant(Row::Extend {
            label: tag.to_string(),
            field: Box::new(payload_ty),
            rest: Box::new(self.fresh_row()),
        });
        self.unify(scrut_ty, &expected, span);
    }

    /// A `match` with no `else` must cover every tag the scrutinee can be, and
    /// then the scrutinee can be no other.
    fn close_match(&mut self, scrut_ty: &Ty, handled: &[&str], span: Span) {
        let Ty::Variant(row) = self.resolve_head(scrut_ty) else {
            return;
        };
        let (tags, tail) = row_shape(&row);
        let missing: Vec<String> = tags
            .into_iter()
            .filter(|t| !handled.contains(&t.as_str()))
            .collect();
        if !missing.is_empty() {
            self.errors.push(GoatError::new(
                span,
                format!(
                    "`match` doesn't handle {}; add an arm for it or an `else`",
                    tag_list(&missing, "and")
                ),
            ));
        } else if let Some(var) = tail {
            self.row_subst.insert(var, Row::Empty);
        }
    }

    /// Unify a branch's type with the type of the branches before it.
    fn join_branch(&mut self, result: &mut Option<Ty>, ty: Ty, span: Span) {
        match result {
            Some(first) => self.unify(&ty, first, span),
            None => *result = Some(ty),
        }
    }

    /// One warning per tag that is constructed but never named in a `match`
    /// arm: the usual sign of a misspelled tag.
    fn unused_tag_warnings(&self) -> Vec<GoatError> {
        let mut seen = HashSet::new();
        self.constructed
            .iter()
            .filter(|(name, span)| {
                !span.in_prelude() && !self.matched.contains(name) && seen.insert(name)
            })
            .map(|(name, span)| {
                GoatError::new(
                    *span,
                    format!("tag `{name}` is constructed but never matched anywhere"),
                )
            })
            .collect()
    }
}

/// `row` without the first field labelled `label`, looking only at the fields
/// written out ahead of any row variable.
fn without_front(row: Row, label: &str) -> Row {
    match row {
        Row::Extend {
            label: l,
            field,
            rest,
        } => {
            if l == label {
                *rest
            } else {
                Row::Extend {
                    label: l,
                    field,
                    rest: Box::new(without_front(*rest, label)),
                }
            }
        }
        other => other,
    }
}

fn occurs(var: TypeVar, ty: &Ty) -> bool {
    match ty {
        Ty::Var(v) => *v == var,
        Ty::Func(args, ret) => args.iter().any(|a| occurs(var, a)) || occurs(var, ret),
        Ty::Record(row) | Ty::Variant(row) => occurs_row(var, row),
        Ty::Rec(_, body) => occurs(var, body),
        _ => false,
    }
}

/// Replace the mentions of `hole` in `ty` with `with`, but only those under a
/// variant payload: `under_tag` says whether `ty` already sits in one. A
/// mention left behind is a cycle that does not pass through a tag.
fn plug(ty: &Ty, hole: &Hole, with: &Ty, under_tag: bool) -> Ty {
    match ty {
        Ty::Var(v) if under_tag && *hole == Hole::Ty(*v) => with.clone(),
        Ty::Record(row)
            if under_tag && matches!(hole, Hole::Mention(RowKind::Record, m) if m == row) =>
        {
            with.clone()
        }
        Ty::Variant(row)
            if under_tag && matches!(hole, Hole::Mention(RowKind::Variant, m) if m == row) =>
        {
            with.clone()
        }
        Ty::Func(args, ret) => Ty::Func(
            args.iter()
                .map(|a| plug(a, hole, with, under_tag))
                .collect(),
            Box::new(plug(ret, hole, with, under_tag)),
        ),
        Ty::Record(row) => Ty::Record(plug_row(row, hole, with, under_tag)),
        Ty::Variant(row) => Ty::Variant(plug_row(row, hole, with, true)),
        Ty::Rec(binder, body) => Ty::Rec(*binder, Box::new(plug(body, hole, with, under_tag))),
        other => other.clone(),
    }
}

/// [`plug`] over the fields of a row; `under_tag` is whether those fields are
/// variant payloads.
fn plug_row(row: &Row, hole: &Hole, with: &Ty, under_tag: bool) -> Row {
    match row {
        Row::Extend { label, field, rest } => Row::Extend {
            label: label.clone(),
            field: Box::new(plug(field, hole, with, under_tag)),
            rest: Box::new(plug_row(rest, hole, with, under_tag)),
        },
        other => other.clone(),
    }
}

/// The row of the first `kind` type under a variant payload whose row ends in
/// the row variable `x`.
fn find_mention(row: &Row, x: TypeVar, kind: RowKind, under_tag: bool) -> Option<Row> {
    let Row::Extend { field, rest, .. } = row else {
        return None;
    };
    find_mention_in(field, x, kind, under_tag).or_else(|| find_mention(rest, x, kind, under_tag))
}

fn find_mention_in(ty: &Ty, x: TypeVar, kind: RowKind, under_tag: bool) -> Option<Row> {
    match ty {
        Ty::Func(args, ret) => args
            .iter()
            .chain([&**ret])
            .find_map(|t| find_mention_in(t, x, kind, under_tag)),
        Ty::Record(row) | Ty::Variant(row) => {
            let is_variant = matches!(ty, Ty::Variant(_));
            if under_tag && is_variant == (kind == RowKind::Variant) && row_shape(row).1 == Some(x)
            {
                return Some(row.clone());
            }
            find_mention(row, x, kind, under_tag || is_variant)
        }
        Ty::Rec(_, body) => find_mention_in(body, x, kind, under_tag),
        _ => None,
    }
}

/// `row` with its tail replaced by `tail`.
fn replace_tail(row: &Row, tail: Row) -> Row {
    match row {
        Row::Extend { label, field, rest } => Row::Extend {
            label: label.clone(),
            field: field.clone(),
            rest: Box::new(replace_tail(rest, tail)),
        },
        _ => tail,
    }
}

/// The labels of a resolved row, and its tail variable if the row is open.
fn row_shape(row: &Row) -> (Vec<String>, Option<TypeVar>) {
    let mut labels = Vec::new();
    let mut cursor = row;
    loop {
        match cursor {
            Row::Extend { label, rest, .. } => {
                labels.push(label.clone());
                cursor = rest;
            }
            Row::Var(v) => return (labels, Some(*v)),
            Row::Empty => return (labels, None),
        }
    }
}

fn tag_list(tags: &[String], conjunction: &str) -> String {
    let quoted: Vec<String> = tags.iter().map(|t| format!("`{t}`")).collect();
    match quoted.as_slice() {
        [] => "nothing".to_string(),
        [only] => only.clone(),
        [init @ .., last] => format!("{} {conjunction} {last}", init.join(", ")),
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
        Ty::Variant(row) => Ty::Variant(subst_row(row, mapping)),
        Ty::Rec(binder, body) => Ty::Rec(
            mapping.get(binder).copied().unwrap_or(*binder),
            Box::new(subst_vars(body, mapping)),
        ),
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

#[cfg(test)]
mod tests {
    use super::*;

    const SPAN: Span = Span::new(0, 0);

    fn extend(label: &str, field: Ty, rest: Row) -> Row {
        Row::Extend {
            label: label.to_string(),
            field: Box::new(field),
            rest: Box::new(rest),
        }
    }

    /// `μbinder. [label: binder | tail]`
    fn chain(binder: TypeVar, label: &str, tail: Row) -> Ty {
        Ty::Rec(
            binder,
            Box::new(Ty::Variant(extend(label, Ty::Var(binder), tail))),
        )
    }

    fn inferer() -> Inferer {
        Inferer {
            next: 1000,
            ..Inferer::default()
        }
    }

    fn unify_ok(a: &Ty, b: &Ty) -> Inferer {
        let mut inf = inferer();
        inf.unify(a, b, SPAN);
        assert!(inf.errors.is_empty(), "{:?}", inf.errors);
        inf
    }

    #[test]
    fn recursive_types_that_unfold_to_each_other_unify() {
        let one = chain(100, "A", Row::Empty);
        let two = Ty::Rec(
            101,
            Box::new(Ty::Variant(extend(
                "A",
                Ty::Variant(extend("A", Ty::Var(101), Row::Empty)),
                Row::Empty,
            ))),
        );
        unify_ok(&one, &two);
        unify_ok(&two, &one);
    }

    #[test]
    fn mutually_recursive_open_shapes_unify_and_share_their_tails() {
        let one = chain(100, "A", Row::Var(1));
        let two = Ty::Rec(
            101,
            Box::new(Ty::Variant(extend(
                "A",
                Ty::Variant(extend("A", Ty::Var(101), Row::Var(2))),
                Row::Var(2),
            ))),
        );
        let inf = unify_ok(&one, &two);
        assert_eq!(inf.resolve_row(&Row::Var(1)), inf.resolve_row(&Row::Var(2)));
        assert!(inf.assumed.is_empty());
    }

    #[test]
    fn recursive_types_that_differ_are_an_error_not_a_loop() {
        let mut inf = inferer();
        inf.unify(
            &chain(100, "A", Row::Empty),
            &chain(101, "B", Row::Empty),
            SPAN,
        );
        assert!(!inf.errors.is_empty());

        let mut inf = inferer();
        let finite = Ty::Variant(extend(
            "A",
            Ty::Variant(extend("A", Ty::Number, Row::Empty)),
            Row::Empty,
        ));
        inf.unify(&chain(100, "A", Row::Empty), &finite, SPAN);
        assert!(!inf.errors.is_empty());
    }

    #[test]
    fn a_variable_bound_to_a_type_containing_it_under_a_tag_becomes_recursive() {
        let mut inf = inferer();
        let under_tag = Ty::Variant(extend("A", Ty::Var(1), Row::Empty));
        inf.unify(&Ty::Var(1), &under_tag, SPAN);
        assert!(inf.errors.is_empty());
        let resolved = inf.finish(&Ty::Var(1));
        let Ty::Rec(binder, body) = &resolved else {
            panic!("{resolved}");
        };
        assert_eq!(
            **body,
            Ty::Variant(extend("A", Ty::Var(*binder), Row::Empty))
        );
    }

    #[test]
    fn a_variable_bound_to_a_type_containing_it_outside_a_tag_is_an_error() {
        for ty in [
            Ty::func(vec![Ty::Var(1)], Ty::Number),
            Ty::Record(extend("a", Ty::Var(1), Row::Empty)),
            // one mention under a tag does not excuse another outside it
            Ty::Record(extend(
                "a",
                Ty::Var(1),
                extend(
                    "b",
                    Ty::Variant(extend("A", Ty::Var(1), Row::Empty)),
                    Row::Empty,
                ),
            )),
        ] {
            let mut inf = inferer();
            inf.unify(&Ty::Var(1), &ty, SPAN);
            assert_eq!(inf.errors.len(), 1, "{ty}");
            assert!(inf.errors[0].message.contains("infinite"), "{ty}");
            assert!(!inf.subst.contains_key(&1));
        }
    }

    #[test]
    fn a_row_variable_mentioned_only_in_its_own_payload_becomes_recursive() {
        let mut inf = inferer();
        let row = extend("Link", Ty::Variant(Row::Var(1)), Row::Var(2));
        inf.unify_row(&Row::Var(1), &row, SPAN, RowKind::Variant);
        assert!(inf.errors.is_empty());
        let resolved = inf.finish(&Ty::Variant(Row::Var(1)));
        assert!(matches!(resolved, Ty::Rec(..)), "{resolved}");
    }

    #[test]
    fn a_row_variable_that_is_its_own_tail_or_record_field_is_an_error() {
        for (kind, row) in [
            (RowKind::Variant, extend("A", Ty::Unit, Row::Var(1))),
            (
                RowKind::Record,
                extend("a", Ty::Record(Row::Var(1)), Row::Empty),
            ),
        ] {
            let mut inf = inferer();
            inf.unify_row(&Row::Var(1), &row, SPAN, kind);
            assert_eq!(inf.errors.len(), 1);
            assert!(inf.errors[0].message.contains("infinite"));
        }
    }

    #[test]
    fn instantiating_a_recursive_scheme_renames_its_binder() {
        let mut inf = inferer();
        let scheme = Scheme {
            vars: vec![7],
            ty: Ty::func(vec![chain(5, "A", Row::Var(7))], Ty::Var(7)),
        };
        let first = inf.instantiate(&scheme);
        let second = inf.instantiate(&scheme);
        let binder = |t: &Ty| match t {
            Ty::Func(args, _) => match &args[0] {
                Ty::Rec(b, body) => {
                    assert!(
                        matches!(&**body, Ty::Variant(Row::Extend { field, .. }) if **field == Ty::Var(*b))
                    );
                    *b
                }
                other => panic!("{other}"),
            },
            other => panic!("{other}"),
        };
        let (a, b) = (binder(&first), binder(&second));
        assert!(a != 5 && b != 5 && a != b);
    }

    #[test]
    fn resolving_substitutes_inside_a_recursive_body_only_for_free_variables() {
        let mut inf = inferer();
        inf.subst.insert(1, Ty::Number);
        let rec = Ty::Rec(
            5,
            Box::new(Ty::Variant(extend(
                "A",
                Ty::Record(extend("0", Ty::Var(1), extend("1", Ty::Var(5), Row::Empty))),
                Row::Empty,
            ))),
        );
        let Ty::Rec(_, body) = inf.resolve(&rec) else {
            panic!("lost the binder");
        };
        assert_eq!(body.to_string(), "[A: {0: Number, 1: t5}]",);
    }

    /// `μbinder. [Empty, Link: {0: Number, 1: binder}]`
    fn list(binder: TypeVar) -> Ty {
        let link = Ty::Record(extend(
            "0",
            Ty::Number,
            extend("1", Ty::Var(binder), Row::Empty),
        ));
        Ty::Rec(
            binder,
            Box::new(Ty::Variant(extend(
                "Empty",
                Ty::Unit,
                extend("Link", link, Row::Empty),
            ))),
        )
    }

    fn appendable(inf: &mut Inferer, ty: &Ty) -> Result<(), String> {
        inf.constrain(ty, Kinds::of(Kind::Appendable))
            .map_err(|v| v.message(ty, None))
    }

    #[test]
    fn strings_and_lists_are_appendable() {
        let mut inf = inferer();
        assert_eq!(appendable(&mut inf, &Ty::Str), Ok(()));
        assert_eq!(appendable(&mut inf, &list(100)), Ok(()));
        let open = Ty::Variant(extend("Empty", Ty::Unit, Row::Var(1)));
        assert_eq!(appendable(&mut inf, &open), Ok(()));
    }

    #[test]
    fn nothing_else_is_appendable_and_the_message_says_so() {
        let mut inf = inferer();
        assert_eq!(
            appendable(&mut inf, &Ty::Number),
            Err("`join` needs strings or lists, but this is `Number`".into())
        );
        assert_eq!(
            appendable(&mut inf, &Ty::Bool),
            Err("`join` needs strings or lists, but this is `Bool`".into())
        );
        assert_eq!(
            appendable(&mut inf, &Ty::Record(extend("x", Ty::Number, Row::Empty))),
            Err("`join` needs strings or lists, but this is `{x: Number}`".into())
        );
        let shape = Ty::Variant(extend("Circle", Ty::Number, Row::Empty));
        assert_eq!(
            appendable(&mut inf, &shape),
            Err("`join` needs strings or lists, but this is `[Circle: Number]`".into())
        );
        let func = Ty::func(vec![Ty::Number], Ty::Number);
        assert!(appendable(&mut inf, &func).is_err());
    }

    #[test]
    fn a_variable_is_checked_when_it_is_bound() {
        let mut inf = inferer();
        let v = inf.fresh();
        assert_eq!(appendable(&mut inf, &v), Ok(()));
        inf.unify(&v, &Ty::Str, SPAN);
        assert!(inf.errors.is_empty(), "{:?}", inf.errors);

        let w = inf.fresh();
        appendable(&mut inf, &w).unwrap();
        inf.unify(&w, &Ty::Number, SPAN);
        assert_eq!(
            inf.errors[0].message,
            "`join` needs strings or lists, but this is `Number`"
        );
    }

    #[test]
    fn two_constrained_variables_intersect_their_constraints() {
        let mut inf = inferer();
        let (a, b) = (inf.fresh(), inf.fresh());
        appendable(&mut inf, &a).unwrap();
        inf.constrain(&b, Kinds::of(Kind::Numeric)).unwrap();
        inf.unify(&a, &b, SPAN);
        assert_eq!(
            inf.errors[0].message,
            "this would have to be both a number and a string or list"
        );

        let mut inf = inferer();
        let (a, b) = (inf.fresh(), inf.fresh());
        inf.constrain(&a, Kinds::of(Kind::Eq)).unwrap();
        inf.constrain(&b, Kinds::of(Kind::Numeric)).unwrap();
        inf.unify(&a, &b, SPAN);
        inf.unify(&b, &Ty::Number, SPAN);
        assert!(inf.errors.is_empty(), "{:?}", inf.errors);
        let func = Ty::func(vec![Ty::Number], Ty::Number);
        let c = inf.fresh();
        inf.constrain(&c, Kinds::of(Kind::Eq)).unwrap();
        inf.unify(&c, &func, SPAN);
        assert_eq!(inf.errors[0].message, "can't compare functions with `==`");
    }

    #[test]
    fn an_open_list_row_refuses_a_tag_that_is_not_part_of_a_list() {
        let list_row = || Ty::Variant(extend("Empty", Ty::Unit, Row::Var(7)));
        let circle = Ty::Variant(extend("Circle", Ty::Number, Row::Var(8)));

        let mut inf = inferer();
        appendable(&mut inf, &list_row()).unwrap();
        inf.unify(&circle, &list_row(), SPAN);
        assert_eq!(
            inf.errors[0].message,
            "the tag `Circle` is not allowed here; the other side never has it"
        );

        let mut inf = inferer();
        appendable(&mut inf, &list_row()).unwrap();
        inf.unify(&list_row(), &circle, SPAN);
        assert_eq!(
            inf.errors[0].message,
            "`join` needs strings or lists, but this is `[Circle: Number | t1001]`"
        );
    }

    #[test]
    fn a_row_variable_hands_its_constraint_to_the_fields_it_gains() {
        let mut inf = inferer();
        let record = Ty::Record(extend("x", Ty::Number, Row::Var(7)));
        inf.constrain(&record, Kinds::of(Kind::Numeric)).unwrap();
        let grown = Ty::Record(extend("y", Ty::Bool, Row::Var(8)));
        inf.unify(&record, &grown, SPAN);
        assert_eq!(
            inf.errors[0].message,
            "arithmetic needs numbers or records of numbers, but this is `{y: Bool | t1001}`"
        );
    }
}
