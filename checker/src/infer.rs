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
use crate::hir::{
    BinOp, Builtin, ContractBinding, Expr, ExprId, ExprKind, Interactive, MatchArm, PatternPayload,
    Span, Symbol,
};
use crate::kinds::{Kind, Kinds, Offender, Violation, is_list_tag};
use crate::ty::{Group, Row, Scheme, Ty, TypeVar};
use crate::vocab::{Vocab, list};
use std::collections::{BTreeSet, HashMap, HashSet};

/// Most type terms (constructors, fields, variables) one expression's type may
/// hold. Composing generic functions with themselves doubles a type at every
/// level, and inference over a type that large is slower than quadratic, so a
/// crafted program would hang the checker; no hand-written type comes close.
const MAX_TYPE_TERMS: usize = 1024;

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
    /// The type variables, left free in a generalized function, that can only
    /// be `Int` or `Float`. Where nothing instantiates one, it reads as `Int`.
    pub number_vars: HashSet<TypeVar>,
    /// Diagnostics that do not stop compilation.
    pub warnings: Vec<GoatError>,
}

pub fn infer(root: &Expr) -> Result<Typed, Vec<GoatError>> {
    infer_program(root, None, &Vocab::empty())
}

/// Like [`infer`], for a program that may be interactive: its three contract
/// bindings are then unified into the shape ADR 0015 gives them, over the
/// events and shapes of `vocab`.
pub fn infer_program(
    root: &Expr,
    interactive: Option<&Interactive>,
    vocab: &Vocab,
) -> Result<Typed, Vec<GoatError>> {
    match infer_partial(root, interactive, vocab) {
        (typed, errors) if errors.is_empty() => Ok(typed),
        (_, errors) => Err(errors),
    }
}

/// [`infer_program`] for editor tooling: the types of whatever the checker
/// could settle, beside the errors it found. A program with errors has types
/// for the parts that are fine, and none of its warnings.
pub fn infer_partial(
    root: &Expr,
    interactive: Option<&Interactive>,
    vocab: &Vocab,
) -> (Typed, Vec<GoatError>) {
    let mut inf = Inferer::default();
    let ty = inf.infer(root);
    if let (true, Some(contract)) = (inf.errors.is_empty(), interactive) {
        inf.check_contract(contract, vocab);
    }
    inf.report_spent_ids(root.span);
    inf.default_numbers();
    let warnings = if inf.errors.is_empty() {
        inf.unused_tag_warnings()
    } else {
        Vec::new()
    };
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
    let number_vars = inf
        .kinds
        .iter()
        .filter(|(_, kinds)| kinds.is_scalar())
        .map(|(var, _)| *var)
        .collect();
    let typed = Typed {
        root_ty,
        node_types,
        schemes,
        binder_types,
        number_vars,
        warnings,
    };
    (typed, inf.errors)
}

#[derive(Default)]
struct Inferer {
    next: TypeVar,
    ids_spent: bool,
    subst: HashMap<TypeVar, Ty>,
    row_subst: HashMap<TypeVar, Row>,
    env: HashMap<Symbol, Scheme>,
    /// The `env` symbols whose types may still mention a variable that is
    /// neither quantified nor bound, other than those in `lone_vars`.
    /// [`Inferer::env_free_vars`] drops a symbol once its type is closed,
    /// which it stays.
    open_env: HashSet<Symbol>,
    /// The `env` symbols whose type is exactly one unbound variable, by that
    /// variable. Such a symbol adds only its variable to the environment's, so
    /// generalizing looks the variable up instead of scanning the symbol.
    lone_vars: HashMap<TypeVar, HashSet<Symbol>>,
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
    /// Ids stop at `TypeVar::MAX`, where `ids_spent` is raised once and every
    /// later variable aliases it; the caller reports that before codegen could
    /// see an unsound type.
    fn fresh_id(&mut self) -> TypeVar {
        let v = self.next;
        if v == TypeVar::MAX - 1 {
            self.ids_spent = true;
        }
        self.next = v.saturating_add(1);
        v
    }

    fn report_spent_ids(&mut self, span: Span) {
        if std::mem::take(&mut self.ids_spent) {
            self.errors.push(GoatError::new(
                span,
                "program too complex: it needs more type variables than the checker can number",
            ));
        }
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
        self.undecided_as_int(self.resolve(ty).unfold_head())
    }

    /// A literal whose type is still open reads as `Int` to code that only
    /// inspects what kind of type it has.
    fn undecided_as_int(&self, ty: Ty) -> Ty {
        match ty {
            Ty::Var(v) if self.is_literal(v) => Ty::Int,
            ty => ty,
        }
    }

    fn is_literal(&self, var: TypeVar) -> bool {
        self.kinds.get(&var).is_some_and(|kinds| kinds.is_literal())
    }

    fn is_scalar(&self, var: TypeVar) -> bool {
        self.kinds.get(&var).is_some_and(|kinds| kinds.is_scalar())
    }

    /// The resolved type in its final shape: every variable substituted, and
    /// recursive types folded back to their `μ` form.
    fn finish(&self, ty: &Ty) -> Ty {
        self.resolve(ty).fold_rec()
    }

    /// [`Self::finish`] for a message: a literal whose type is still open
    /// reads as `Number`, not as a bare variable.
    fn shown(&self, ty: &Ty) -> Ty {
        let resolved = self.finish(ty);
        let mut vars = BTreeSet::new();
        resolved.free_vars(&mut vars);
        vars.into_iter()
            .filter(|var| self.is_literal(*var))
            .fold(resolved, |ty, var| ty.substitute(var, &Ty::Int))
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
        let reused = match self.resolve(actual) {
            Ty::Var(v) => self.is_scalar(v),
            _ => true,
        };
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
        let (mut a, mut b) = (self.resolve(a), self.resolve(b));
        // Between two variables the newer is bound to the older, so a variable
        // unified once per statement stays one link from its root.
        if matches!((&a, &b), (Ty::Var(x), Ty::Var(y)) if x < y) {
            std::mem::swap(&mut a, &mut b);
        }
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
                self.bind_var(*x, bound.clone());
                if let Some(kinds) = self.kinds.remove(x)
                    && let Err(violation) = self.constrain(&bound, kinds)
                {
                    if kinds.is_scalar() && violation.offender != Offender::Both {
                        // The number stays a number, so one mismatch is not
                        // followed by others about the type it would have taken.
                        self.subst.remove(x);
                        self.kinds.insert(*x, kinds);
                        let shown = self.shown(&bound).to_string();
                        let (found, expected) = match &a {
                            Ty::Var(v) if v == x => ("Number".to_string(), shown),
                            _ => (shown, "Number".to_string()),
                        };
                        self.errors.push(GoatError::new(
                            span,
                            format!("type mismatch: expected `{expected}`, found `{found}`"),
                        ));
                    } else {
                        self.report_violation(span, &violation, &bound, None);
                    }
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
            (Ty::Int, Ty::Int)
            | (Ty::Float, Ty::Float)
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
                // Both numeric types read `Number`, so a clash between `Int`
                // and `Float` has to name them.
                let (a, b) = (self.shown(&a), self.shown(&b));
                let (found, expected) = match (a.to_string(), b.to_string()) {
                    (found, expected) if found == expected => {
                        (a.exact().to_string(), b.exact().to_string())
                    }
                    shown => shown,
                };
                self.errors.push(GoatError::new(
                    span,
                    format!("type mismatch: expected `{expected}`, found `{found}`"),
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
                    let message = match pure_extension(*x, other) {
                        Some(labels) if kind == RowKind::Record => spread_regress_message(&labels),
                        _ => format!("cannot construct an infinite {} type", kind.noun()),
                    };
                    self.errors.push(GoatError::new(span, message));
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
    /// `label` keep their position, which is what makes labels scoped. The
    /// recursion is as deep as the row is long, which [`MAX_TYPE_TERMS`] caps:
    /// every row grows by one inferred expression at a time and each is checked.
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
            (Ty::Int | Ty::Float, Kind::Eq | Kind::Numeric | Kind::Ordered | Kind::Literal) => {
                Ok(())
            }
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
        let whole = self.shown(whole);
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

    /// A value that is not a function keeps its literals' types shared (still
    /// open to `Float`) rather than generalized: `n = 3` is one number, not a
    /// fresh one at every use.
    fn generalize(&mut self, ty: &Ty, function: bool) -> Scheme {
        let resolved = self.finish(ty);
        let mut in_ty = BTreeSet::new();
        resolved.free_vars(&mut in_ty);
        in_ty.retain(|v| function || !self.is_literal(*v));
        if !in_ty.is_empty() {
            let in_env = self.env_free_vars();
            in_ty.retain(|v| !in_env.contains(v) && !self.lone_vars.contains_key(v));
        }
        Scheme {
            vars: in_ty.into_iter().collect(),
            ty: resolved,
        }
    }

    fn bind_env(&mut self, symbol: Symbol, scheme: Scheme) {
        self.unbind_env(&symbol);
        match &scheme.ty {
            Ty::Var(v) if scheme.vars.is_empty() && !self.subst.contains_key(v) => {
                self.lone_vars.entry(*v).or_default().insert(symbol);
            }
            _ => {
                self.open_env.insert(symbol);
            }
        }
        self.env.insert(symbol, scheme);
    }

    fn unbind_env(&mut self, symbol: &Symbol) -> Option<Scheme> {
        let scheme = self.env.remove(symbol)?;
        self.open_env.remove(symbol);
        if let Ty::Var(v) = &scheme.ty
            && let Some(symbols) = self.lone_vars.get_mut(v)
        {
            symbols.remove(symbol);
            if symbols.is_empty() {
                self.lone_vars.remove(v);
            }
        }
        Some(scheme)
    }

    /// Bind `var`, which moves any symbol of exactly that type out of
    /// `lone_vars`: its type is no longer just the variable.
    fn bind_var(&mut self, var: TypeVar, ty: Ty) {
        self.subst.insert(var, ty);
        if let Some(symbols) = self.lone_vars.remove(&var) {
            self.open_env.extend(symbols);
        }
    }

    fn env_free_vars(&mut self) -> BTreeSet<TypeVar> {
        let mut out = BTreeSet::new();
        let mut open = std::mem::take(&mut self.open_env);
        open.retain(|symbol| {
            let Some(scheme) = self.env.get(symbol) else {
                return false;
            };
            let mut free = BTreeSet::new();
            self.resolve(&scheme.ty).free_vars(&mut free);
            for bound in &scheme.vars {
                free.remove(bound);
            }
            let still_open = !free.is_empty();
            out.extend(free);
            still_open
        });
        self.open_env = open;
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
                self.bind_env(*symbol, Scheme::mono(ty));
            }
            cursor = rest.as_deref();
        }
    }

    /// `init : M`, `update : (M, E) -> M`, `draw : (M) -> List(S)`, with `M` a
    /// record and `E` and `S` variants. The three types are the uses the
    /// root's tail makes, so unifying them here fixes what mono specializes.
    fn check_contract(&mut self, contract: &Interactive, vocab: &Vocab) {
        for decoder in &contract.decoders {
            if let Some(expected) = vocab.decoder_ty(&decoder.function) {
                let actual = self.contract_ty(&decoder.binding);
                let what = format!(
                    "the host's `{}` decodes its events, so it must have the type",
                    decoder.function
                );
                self.unify_vocab(&decoder.binding, &actual, &expected, &what);
            }
        }
        let model = self.contract_ty(&contract.init);
        if !matches!(self.resolve_head(&model), Ty::Record(_)) {
            self.contract_error(
                &contract.init,
                format!(
                    "init must be a record, like {{x: 0, y: 0}}, not `{}`",
                    self.shown(&model)
                ),
            );
            return;
        }

        let update = self.contract_ty(&contract.update);
        match self.resolve_head(&update) {
            Ty::Func(args, ret) if args.len() == 2 => {
                self.unify_contract(&contract.update, &args[0], &model, "update's model");
                self.unify_contract(&contract.update, &ret, &model, "update's result");
                self.check_events(&contract.update, &args[1], vocab);
            }
            other => self.contract_error(
                &contract.update,
                format!(
                    "update must be a function of a model and an event, like program(model, event); this is `{}`",
                    self.shown(&other)
                ),
            ),
        }

        let draw = self.contract_ty(&contract.draw);
        match self.resolve_head(&draw) {
            Ty::Func(args, ret) if args.len() == 1 => {
                self.unify_contract(&contract.draw, &args[0], &model, "draw's model");
                if self.is_list_of_variants(&ret) {
                    self.check_shapes(&contract.draw, &ret, vocab);
                } else {
                    self.contract_error(
                        &contract.draw,
                        format!(
                            "draw must return a list of shapes, like [Line({{x1: 0, y1: 0, x2: 5, y2: 5, color: \"black\"}})], not `{}`",
                            self.shown(&ret)
                        ),
                    );
                }
            }
            other => self.contract_error(
                &contract.draw,
                format!(
                    "draw must be a function of the model, like program(model); this is `{}`",
                    self.shown(&other)
                ),
            ),
        }

        if let Some(function) = self.finish(&model).find_func() {
            let function = self.shown(function);
            self.contract_error(
                &contract.init,
                format!(
                    "the model can't hold a function, but this one holds `{function}`; \
                     a reload keeps the model, and a function can't outlive its code, so keep functions at the top level"
                ),
            );
        }
    }

    /// The event type is exactly the tags `update` handles, each carrying what
    /// the host sends. Closing the row is what lets the backend build one
    /// constructor per handled tag (ADR 0015).
    fn check_events(&mut self, binding: &ContractBinding, event: &Ty, vocab: &Vocab) {
        let Ty::Variant(row) = self.resolve_head(event) else {
            self.contract_error(
                binding,
                format!(
                    "update's second argument must be an event, a tag like Tick(dt) or KeyDown(key), not `{}`",
                    self.shown(event)
                ),
            );
            return;
        };
        let (tags, tail) = row_shape(&row);
        let known: Vec<&str> = vocab.events.iter().map(|e| e.name.as_str()).collect();
        if self.reject_unknown(binding, &tags, &known, "the host doesn't send", "event") {
            return;
        }
        for tag in &tags {
            if let (Some(payload), Some(event)) = (field_of(&row, tag), vocab.event(tag)) {
                let what = format!("the host's `{tag}` event carries");
                self.unify_vocab(binding, payload, &event.payload, &what);
            }
        }
        if let Some(var) = tail {
            self.row_subst.insert(var, Row::Empty);
        }
    }

    /// `draw`'s shapes come from the host's vocabulary, each with the payload
    /// the host reads.
    fn check_shapes(&mut self, binding: &ContractBinding, shapes: &Ty, vocab: &Vocab) {
        // A list literal types each element on its own; unifying with one list
        // type makes every element the same `Shape`.
        let (item, binder) = (self.fresh(), self.fresh_id());
        self.unify(shapes, &list(binder, item.clone()), binding.span);
        let Ty::Variant(row) = self.resolve_head(&item) else {
            return;
        };
        let (tags, tail) = row_shape(&row);
        let known: Vec<&str> = vocab.shapes.iter().map(|s| s.name.as_str()).collect();
        if self.reject_unknown(binding, &tags, &known, "the host can't draw", "shape") {
            return;
        }
        for tag in &tags {
            let binder = self.fresh_id();
            if let (Some(payload), Some(expected)) =
                (field_of(&row, tag), vocab.shape_payload(tag, binder))
            {
                let what = format!("the host's `{tag}` shape needs");
                self.unify_vocab(binding, payload, &expected, &what);
            }
        }
        if let Some(var) = tail {
            self.row_subst.insert(var, Row::Empty);
        }
    }

    /// Report the tags outside `known`; true if there were any.
    fn reject_unknown(
        &mut self,
        binding: &ContractBinding,
        tags: &[String],
        known: &[&str],
        verb: &str,
        noun: &str,
    ) -> bool {
        let unknown: Vec<String> = tags
            .iter()
            .filter(|t| !known.contains(&t.as_str()))
            .cloned()
            .collect();
        if unknown.is_empty() {
            return false;
        }
        let known: Vec<String> = known.iter().map(|t| t.to_string()).collect();
        let named = match unknown.as_slice() {
            [only] => format!("a `{only}` {noun}"),
            _ => format!("{} {noun}s", tag_list(&unknown, "or")),
        };
        self.contract_error(
            binding,
            format!("{verb} {named}; the host knows {}", tag_list(&known, "and")),
        );
        true
    }

    fn unify_vocab(&mut self, binding: &ContractBinding, actual: &Ty, expected: &Ty, what: &str) {
        let before = self.errors.len();
        self.unify(actual, expected, binding.span);
        let expected = self.shown(expected);
        for error in &mut self.errors[before..] {
            error.message = format!("{what} `{expected}`: {}", error.message);
        }
    }

    fn contract_ty(&self, binding: &ContractBinding) -> Ty {
        self.node_types[&binding.use_id].clone()
    }

    fn contract_error(&mut self, binding: &ContractBinding, message: String) {
        self.errors.push(GoatError::new(binding.span, message));
    }

    fn unify_contract(&mut self, binding: &ContractBinding, actual: &Ty, model: &Ty, what: &str) {
        let before = self.errors.len();
        self.unify(actual, model, binding.span);
        for error in &mut self.errors[before..] {
            error.message = format!(
                "{what} must have the type of init's value: {}",
                error.message
            );
        }
    }

    /// Whether `ty` is `[]` or a `Link` list whose items are variants.
    fn is_list_of_variants(&self, ty: &Ty) -> bool {
        let Ty::Variant(row) = self.resolve_head(ty) else {
            return false;
        };
        let (labels, _) = row_shape(&row);
        if !labels.iter().all(|l| is_list_tag(l)) {
            return false;
        }
        let Some(link) = field_of(&row, "Link") else {
            return true;
        };
        let Ty::Record(link) = self.resolve_head(link) else {
            return false;
        };
        field_of(&link, "0").is_some_and(|item| matches!(self.resolve_head(item), Ty::Variant(_)))
    }

    fn infer(&mut self, expr: &Expr) -> Ty {
        let mut ty = self.infer_kind(expr);
        self.report_spent_ids(expr.span);
        if !self.within_term_budget(&ty) {
            self.errors.push(GoatError::new(
                expr.span,
                format!(
                    "program too complex: the type of this expression has more than {MAX_TYPE_TERMS} parts"
                ),
            ));
            ty = self.fresh();
        }
        self.node_types.insert(expr.id, ty.clone());
        ty
    }

    /// Whether `ty`, followed through the substitution, has at most
    /// [`MAX_TYPE_TERMS`] terms. Counting stops once the budget is spent, so
    /// the cost is bounded however large the type is.
    fn within_term_budget(&self, ty: &Ty) -> bool {
        let mut budget = MAX_TYPE_TERMS;
        self.spend_on_ty(ty, &mut budget).is_some()
    }

    fn spend_on_ty(&self, ty: &Ty, budget: &mut usize) -> Option<()> {
        *budget = budget.checked_sub(1)?;
        match ty {
            Ty::Var(v) => match self.subst.get(v) {
                Some(bound) => self.spend_on_ty(bound, budget),
                None => Some(()),
            },
            Ty::Func(args, ret) => {
                for arg in args {
                    self.spend_on_ty(arg, budget)?;
                }
                self.spend_on_ty(ret, budget)
            }
            Ty::Record(row) | Ty::Variant(row) => self.spend_on_row(row, budget),
            Ty::Rec(_, body) => self.spend_on_ty(body, budget),
            Ty::Int | Ty::Float | Ty::Str | Ty::Bool | Ty::Unit => Some(()),
        }
    }

    fn spend_on_row(&self, row: &Row, budget: &mut usize) -> Option<()> {
        *budget = budget.checked_sub(1)?;
        match row {
            Row::Var(v) => match self.row_subst.get(v) {
                Some(bound) => self.spend_on_row(bound, budget),
                None => Some(()),
            },
            Row::Extend { field, rest, .. } => {
                self.spend_on_ty(field, budget)?;
                self.spend_on_row(rest, budget)
            }
            Row::Empty => Some(()),
        }
    }

    /// The chain of `Let`s from `first`, walked in a loop so a long block costs
    /// no stack. Every `Let` in it has the type of the chain's last expression.
    fn infer_spine(&mut self, first: &Expr) -> Ty {
        let mut spine = Vec::new();
        let mut seeded = false;
        let mut cursor = first;
        let ty = loop {
            let ExprKind::Let {
                symbol,
                value,
                rest,
                ..
            } = &cursor.kind
            else {
                break self.infer(cursor);
            };
            if !seeded && matches!(value.kind, ExprKind::Func { .. }) {
                self.seed_function_group(cursor);
                seeded = true;
            }
            let value_ty = self.infer(value);
            let rec = match self.unbind_env(symbol) {
                Some(seed) => {
                    self.unify(&value_ty, &seed.ty, value.span);
                    seed.ty
                }
                None => value_ty,
            };

            let scheme = self.generalize(&rec, matches!(value.kind, ExprKind::Func { .. }));
            self.bind_env(*symbol, scheme.clone());
            self.schemes.insert(*symbol, scheme.clone());
            spine.push((cursor.id, symbol));
            match rest {
                Some(rest) => cursor = rest,
                None => break self.instantiate(&scheme),
            }
        };
        for (id, symbol) in spine.into_iter().rev() {
            self.unbind_env(symbol);
            self.node_types.insert(id, ty.clone());
        }
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

    /// `and`, `or` and `not` need Bool operands; a wrong one is blamed on the
    /// operand itself, naming the operator.
    fn infer_logic(&mut self, op: &str, first: &Expr, second: Option<&Expr>) -> Ty {
        let operands = std::iter::once((first, "left")).chain(second.map(|e| (e, "right")));
        for (operand, side) in operands {
            let ty = self.infer(operand);
            let before = self.errors.len();
            let found = self.undecided_as_int(self.resolve(&ty));
            self.unify_use(operand, &ty, &Ty::Bool, operand.span);
            if let Some(err) = self.errors[before..].first_mut()
                && err.message.starts_with("type mismatch")
            {
                let which = if second.is_some() {
                    format!("the {side} side of `{op}`")
                } else {
                    format!("the operand of `{op}`")
                };
                err.message = format!("{which} must be a Bool, found `{found}`");
            }
        }
        Ty::Bool
    }

    fn infer_kind(&mut self, expr: &Expr) -> Ty {
        match &expr.kind {
            ExprKind::Unit => Ty::Unit,
            ExprKind::Int(_) => self.literal(),
            ExprKind::Float(_) => Ty::Float,
            ExprKind::Str(_) => Ty::Str,
            ExprKind::Bool(_) => Ty::Bool,
            ExprKind::Var { symbol, .. } => match self.env.get(symbol).cloned() {
                Some(scheme) => self.instantiate(&scheme),
                None => self.fresh(),
            },
            ExprKind::Foreign { params, ret, .. } => Ty::func(
                params.iter().copied().map(Ty::from).collect(),
                Ty::from(*ret),
            ),
            ExprKind::Func { params, body } => {
                let arg_tys: Vec<Ty> = params.iter().map(|_| self.fresh()).collect();
                for (param, ty) in params.iter().zip(&arg_tys) {
                    self.bind_env(param.symbol, Scheme::mono(ty.clone()));
                    self.params.insert(param.symbol, param.name.clone());
                }
                let ret = self.infer(body);
                for param in params {
                    self.unbind_env(&param.symbol);
                    self.params.remove(&param.symbol);
                }
                Ty::func(arg_tys, ret)
            }
            ExprKind::App { callee, args } => self.infer_app(expr.span, callee, args),
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
            ExprKind::And { lhs, rhs } => self.infer_logic("and", lhs, Some(rhs)),
            ExprKind::Or { lhs, rhs } => self.infer_logic("or", lhs, Some(rhs)),
            ExprKind::Not(operand) => self.infer_logic("not", operand, None),
            ExprKind::Let { .. } => self.infer_spine(expr),
            ExprKind::Bin { op, lhs, rhs } => {
                let lhs_ty = self.infer(lhs);
                let rhs_ty = self.infer(rhs);
                self.type_bin(expr, *op, (lhs, lhs_ty), (rhs, rhs_ty))
            }
            ExprKind::Builtin(Builtin::Print) => self.print_ty(),
            ExprKind::Builtin(Builtin::Trap) => {
                self.errors.push(GoatError::new(
                    expr.span,
                    "`trap` stops the program, so call it with a message: `trap(\"...\")`",
                ));
                self.fresh()
            }
            ExprKind::Trap(_) => self.fresh(),
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
            ExprKind::Tag {
                name,
                payload,
                group,
            } => {
                let payload_ty = match payload {
                    Some(p) => self.infer(p),
                    None => Ty::Unit,
                };
                self.constructed.push((name.clone(), expr.span));
                if let Some(group) = group {
                    return self.construct_grouped(group, name, &payload_ty, expr.span);
                }
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

    /// A tag of a declared group builds the group's whole closed type, so a
    /// `match` over it needs every tag and no annotation.
    fn construct_grouped(&mut self, group: &Group, tag: &str, payload: &Ty, span: Span) -> Ty {
        let binder = self.fresh_id();
        let whole = group.instantiate(binder);
        if let Ty::Variant(row) = whole.unfold_head()
            && let Some(expected) = field_of(&row, tag)
        {
            self.unify(payload, expected, span);
        }
        whole
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
        let operands = ((lhs, lhs_ty), (rhs, rhs_ty));
        if matches!(op, BinOp::FloorDiv | BinOp::Mod) {
            self.type_whole_division(op, operands)
        } else if op == BinOp::Div {
            self.type_division(op, operands)
        } else if op.is_arithmetic() {
            let (lhs, lhs_ty) = &operands.0;
            if self.require(lhs_ty, Kind::Numeric, op, lhs.span) {
                return self.join_operands(operands);
            }
            lhs_ty.clone()
        } else if op.is_equality() {
            let ty = self.join_operands(operands);
            self.require(&ty, Kind::Eq, op, expr.span);
            Ty::Bool
        } else {
            let (lhs, lhs_ty) = &operands.0;
            if self.require(lhs_ty, Kind::Ordered, op, lhs.span) {
                self.join_operands(operands);
            }
            Ty::Bool
        }
    }

    /// The type both operands share. An `Int` meeting a `Float` widens to
    /// `Float` (mono converts the `Int` side); anything else must be one type.
    fn join_operands(&mut self, ((_, lhs_ty), (rhs, rhs_ty)): ((&Expr, Ty), (&Expr, Ty))) -> Ty {
        match (self.resolve(&lhs_ty), self.resolve(&rhs_ty)) {
            (Ty::Int, Ty::Float) | (Ty::Float, Ty::Int) => Ty::Float,
            _ => {
                self.unify_use(rhs, &rhs_ty, &lhs_ty, rhs.span);
                lhs_ty
            }
        }
    }

    /// `/` always yields a `Float`, whatever its operands are. A record of
    /// numbers divides field by field, so each field has to be a `Float`.
    fn type_division(
        &mut self,
        op: BinOp,
        ((lhs, lhs_ty), (rhs, rhs_ty)): ((&Expr, Ty), (&Expr, Ty)),
    ) -> Ty {
        let is_record = |ty: &Ty| matches!(self.resolve_head(ty), Ty::Record(_));
        if is_record(&lhs_ty) || is_record(&rhs_ty) {
            if self.require(&lhs_ty, Kind::Numeric, op, lhs.span) {
                self.unify_use(rhs, &rhs_ty, &lhs_ty, rhs.span);
                self.require_float_fields(&lhs_ty, lhs.span);
            }
            lhs_ty
        } else {
            self.require(&lhs_ty, Kind::Ordered, op, lhs.span);
            self.require(&rhs_ty, Kind::Ordered, op, rhs.span);
            Ty::Float
        }
    }

    /// Kept out of line so its locals stay out of the deeply recursed
    /// [`Inferer::infer_kind`] frame.
    #[inline(never)]
    fn infer_app(&mut self, span: Span, callee: &Expr, args: &[Expr]) -> Ty {
        let callee_ty = self.infer(callee);
        let mut arg_tys: Vec<Ty> = args.iter().map(|a| self.infer(a)).collect();
        let ret = self.fresh();
        let head = self.resolve_head(&callee_ty);
        if let Ty::Func(params, _) = &head {
            self.widen_arguments(params, &mut arg_tys);
        }
        match head {
            Ty::Func(..) | Ty::Var(_) => {
                let expected = Ty::func(arg_tys, ret.clone());
                self.unify_use(callee, &callee_ty, &expected, span);
            }
            // A `(…)` immediately after an expression is read as a call, so
            // calling a non-function is often a sequencing mistake. Reporting
            // lives in a cold helper to keep this frame small.
            other => self.report_not_callable(callee.span, &other),
        }
        ret
    }

    /// A concrete `Int` argument to a `Float` parameter is taken as the
    /// `Float` it widens to; mono converts it at the call.
    fn widen_arguments(&self, params: &[Ty], args: &mut [Ty]) {
        for (param, arg) in params.iter().zip(args) {
            if self.resolve(param) == Ty::Float && self.resolve(arg) == Ty::Int {
                *arg = Ty::Float;
            }
        }
    }

    /// `//` and `%` take and give whole numbers. A `Float` operand is named
    /// rather than reported as a bare mismatch, because both read `Number`.
    fn type_whole_division(&mut self, op: BinOp, operands: ((&Expr, Ty), (&Expr, Ty))) -> Ty {
        for (operand, ty) in [operands.0, operands.1] {
            if self.resolve(&ty) == Ty::Float {
                self.errors.push(GoatError::new(
                    operand.span,
                    format!(
                        "`{}` needs whole numbers, but this is a `Float`; use `round`, `floor` or `truncate` first",
                        op.symbol()
                    ),
                ));
            } else {
                self.unify_use(operand, &ty, &Ty::Int, operand.span);
            }
        }
        Ty::Int
    }

    fn require_float_fields(&mut self, ty: &Ty, span: Span) {
        match self.resolve_head(ty) {
            Ty::Record(row) => {
                let mut cursor = row;
                while let Row::Extend { field, rest, .. } = cursor {
                    self.require_float_fields(&field, span);
                    cursor = *rest;
                }
            }
            _ => self.unify(ty, &Ty::Float, span),
        }
    }

    /// The type of a whole-number literal: an unknown `Int` or `Float`. If
    /// nothing decides, [`Inferer::default_numbers`] makes it `Int`.
    fn literal(&mut self) -> Ty {
        let var = self.fresh_id();
        self.kinds.insert(var, Kinds::of(Kind::Literal));
        Ty::Var(var)
    }

    /// Settle every number whose type nothing decided as `Int`, except one in
    /// a function's type, which stays free for each call to decide.
    fn default_numbers(&mut self) {
        let generalized: HashSet<TypeVar> = self
            .schemes
            .values()
            .flat_map(|scheme| scheme.vars.iter().copied())
            .collect();
        let undecided: Vec<TypeVar> = self
            .kinds
            .iter()
            .filter(|(var, kinds)| kinds.is_scalar() && !generalized.contains(var))
            .map(|(var, _)| *var)
            .collect();
        for var in undecided {
            self.bind_var(var, Ty::Int);
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
                self.unbind_env(&binder.symbol);
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
        self.bind_env(symbol, Scheme::mono(ty.clone()));
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

fn field_of<'a>(row: &'a Row, label: &str) -> Option<&'a Ty> {
    match row {
        Row::Extend {
            label: l,
            field,
            rest,
        } => {
            if l == label {
                Some(field)
            } else {
                field_of(rest, label)
            }
        }
        Row::Var(_) | Row::Empty => None,
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

/// The labels `row` adds in front of `var` when it is nothing but `var` with
/// fields prepended and none of those fields mention `var`: what a recursive
/// call that spreads its parameter and overrides fields produces.
fn pure_extension(var: TypeVar, row: &Row) -> Option<Vec<String>> {
    let mut labels = Vec::new();
    let mut cursor = row;
    while let Row::Extend { label, field, rest } = cursor {
        if occurs(var, field) {
            return None;
        }
        labels.push(label.clone());
        cursor = rest;
    }
    (matches!(cursor, Row::Var(v) if *v == var) && !labels.is_empty()).then_some(labels)
}

fn spread_regress_message(labels: &[String]) -> String {
    let noun = if labels.len() == 1 { "field" } else { "fields" };
    format!(
        "cannot construct an infinite record type: each recursive call spreads the parameter \
         and adds {noun} {}, so the record would grow without bound. Read or constrain a field \
         of the parameter so the recursion has a fixed shape, or drop the never-read `...` spread",
        tag_list(labels, "and"),
    )
}

fn occurs_row(var: TypeVar, row: &Row) -> bool {
    match row {
        Row::Empty => false,
        Row::Var(v) => *v == var,
        Row::Extend { field, rest, .. } => occurs(var, field) || occurs_row(var, rest),
    }
}

pub(crate) fn subst_vars(ty: &Ty, mapping: &HashMap<TypeVar, TypeVar>) -> Ty {
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

    #[test]
    fn running_out_of_type_variable_ids_is_a_spanned_resource_error() {
        let lowered = crate::lower::lower("id = program(x) do x done id(1)").unwrap();
        let mut inf = Inferer {
            next: TypeVar::MAX - 3,
            ..Inferer::default()
        };
        inf.infer(&lowered.root);
        let spent: Vec<_> = inf
            .errors
            .iter()
            .filter(|e| e.message.starts_with("program too complex"))
            .collect();
        assert_eq!(spent.len(), 1, "{:?}", inf.errors);
        assert!(spent[0].span.end > spent[0].span.start);
    }

    #[test]
    fn type_variable_ids_stop_at_the_maximum_instead_of_wrapping() {
        let mut inf = Inferer {
            next: TypeVar::MAX,
            ..Inferer::default()
        };
        assert_eq!(inf.fresh_id(), TypeVar::MAX);
        assert_eq!(inf.fresh_id(), TypeVar::MAX);
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
            Ty::Variant(extend("A", Ty::Int, Row::Empty)),
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
            Ty::func(vec![Ty::Var(1)], Ty::Int),
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
        inf.subst.insert(1, Ty::Int);
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
            Ty::Int,
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
            appendable(&mut inf, &Ty::Int),
            Err("`join` needs strings or lists, but this is `Number`".into())
        );
        assert_eq!(
            appendable(&mut inf, &Ty::Bool),
            Err("`join` needs strings or lists, but this is `Bool`".into())
        );
        assert_eq!(
            appendable(&mut inf, &Ty::Record(extend("x", Ty::Int, Row::Empty))),
            Err("`join` needs strings or lists, but this is `{x: Number}`".into())
        );
        let shape = Ty::Variant(extend("Circle", Ty::Int, Row::Empty));
        assert_eq!(
            appendable(&mut inf, &shape),
            Err("`join` needs strings or lists, but this is `[Circle: Number]`".into())
        );
        let func = Ty::func(vec![Ty::Int], Ty::Int);
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
        inf.unify(&w, &Ty::Int, SPAN);
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
        inf.unify(&b, &Ty::Int, SPAN);
        assert!(inf.errors.is_empty(), "{:?}", inf.errors);
        let func = Ty::func(vec![Ty::Int], Ty::Int);
        let c = inf.fresh();
        inf.constrain(&c, Kinds::of(Kind::Eq)).unwrap();
        inf.unify(&c, &func, SPAN);
        assert_eq!(inf.errors[0].message, "can't compare functions with `==`");
    }

    #[test]
    fn an_open_list_row_refuses_a_tag_that_is_not_part_of_a_list() {
        let list_row = || Ty::Variant(extend("Empty", Ty::Unit, Row::Var(7)));
        let circle = Ty::Variant(extend("Circle", Ty::Int, Row::Var(8)));

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
        let record = Ty::Record(extend("x", Ty::Int, Row::Var(7)));
        inf.constrain(&record, Kinds::of(Kind::Numeric)).unwrap();
        let grown = Ty::Record(extend("y", Ty::Bool, Row::Var(8)));
        inf.unify(&record, &grown, SPAN);
        assert_eq!(
            inf.errors[0].message,
            "arithmetic needs numbers or records of numbers, but this is `{y: Bool | t1001}`"
        );
    }
}

#[cfg(kani)]
mod proofs {
    use super::*;

    #[kani::proof]
    fn occurs_finds_its_own_variable() {
        let var: TypeVar = kani::any();
        assert!(occurs(var, &Ty::Var(var)));
        assert!(occurs_row(var, &Row::Var(var)));
        let other: TypeVar = kani::any();
        kani::assume(other != var);
        assert!(!occurs(var, &Ty::Var(other)));
        assert!(!occurs_row(var, &Row::Empty));
    }

    #[kani::proof]
    fn occurs_ignores_closed_leaves() {
        let var: TypeVar = kani::any();
        for ty in [Ty::Int, Ty::Str, Ty::Bool, Ty::Unit] {
            assert!(!occurs(var, &ty));
        }
    }
}
