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

use crate::captures::for_each_node;
use crate::error::GoatError;
use crate::hir::{
    BinOp, Builtin, ContractBinding, Expr, ExprId, ExprKind, Interactive, MatchArm, PatternPayload,
    Span, Symbol,
};
use crate::kinds::{Kind, Kinds, Offender, Violation, is_list_tag};
use crate::lower::{DotCall, SELF_NAME, Take};
use crate::ty::{self, ABSENT, Group, METHOD, PLAIN, PRESENT, Row, Scheme, Ty, TypeVar};
use crate::vocab::{Vocab, list};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::Rc;

/// Most type terms (constructors, fields, variables) one expression's type may
/// hold. Composing generic functions with themselves doubles a type at every
/// level, and inference over a type that large is slower than quadratic, so a
/// crafted program would hang the checker; no hand-written type comes close.
/// A record literal's methods each hold the whole receiver type, so a literal
/// of n methods has a type of about n² terms, and the limit leaves room for
/// about thirty of them.
const MAX_TYPE_TERMS: usize = 8192;

/// How deep a type may nest, rows included: a row nests one level per field.
/// The checker recurses as deep as the type does, so this, not the number of
/// terms, keeps a type from overflowing the stack.
const MAX_TYPE_DEPTH: usize = 384;

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
    infer_program(root, None, &Vocab::empty(), DotCalls::default())
}

/// What a message about a dot call quotes: the lowering's side table and the
/// user source its receiver spans point into.
#[derive(Default)]
pub struct DotCalls {
    pub calls: HashMap<ExprId, DotCall>,
    pub takes: HashMap<ExprId, Take>,
    pub source: String,
    /// The `Field` of each dot call's callee, whose method flag the call settles.
    callees: HashSet<ExprId>,
}

impl DotCalls {
    pub fn new(
        calls: HashMap<ExprId, DotCall>,
        takes: HashMap<ExprId, Take>,
        source: String,
    ) -> Self {
        let callees = calls.values().map(|call| call.callee).collect();
        DotCalls {
            calls,
            takes,
            source,
            callees,
        }
    }
}

/// Like [`infer`], for a program that may be interactive: its three contract
/// bindings are then unified into the shape ADR 0015 gives them, over the
/// events and shapes of `vocab`.
pub fn infer_program(
    root: &Expr,
    interactive: Option<&Interactive>,
    vocab: &Vocab,
    dots: DotCalls,
) -> Result<Typed, Vec<GoatError>> {
    match infer_partial(root, interactive, vocab, dots) {
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
    dots: DotCalls,
) -> (Typed, Vec<GoatError>) {
    let names = ty::MessageNames::enter();
    let (typed, mut errors) = infer_with_variable_markers(root, interactive, vocab, dots);
    drop(names);
    for error in &mut errors {
        let labels = error.labels.iter_mut().map(|label| &mut label.message);
        ty::name_variables(std::iter::once(&mut error.message).chain(labels));
    }
    (typed, errors)
}

/// The first place two function types disagree, so a message can name the
/// kinds that clash rather than the whole function.
fn first_difference(a: &Ty, b: &Ty) -> (Ty, Ty) {
    if let (Ty::Func(a_args, a_ret), Ty::Func(b_args, b_ret)) = (a, b)
        && a_args.len() == b_args.len()
    {
        let pairs = a_args.iter().zip(b_args).chain([(&**a_ret, &**b_ret)]);
        if let Some((x, y)) = pairs.into_iter().find(|(x, y)| x != y) {
            return first_difference(x, y);
        }
    }
    (a.clone(), b.clone())
}

/// A type as a kid reads it in a sentence: `a Number`, or the written type.
fn kind_of(ty: &Ty) -> String {
    match ty {
        Ty::Int | Ty::Float | Ty::Str | Ty::Bool | Ty::Unit => format!("a {ty}"),
        _ => format!("`{ty}`"),
    }
}

/// How `var` sits inside `ty`, outermost step first: `its argument`,
/// `its `g` field`. Empty when `var` is `ty` itself, the route is unclear, or
/// it runs deeper than unification lets a type nest.
fn cycle_route(var: TypeVar, ty: &Ty) -> Vec<String> {
    fn in_row(var: TypeVar, row: &Row, route: &mut Vec<String>, noun: &str, depth: usize) -> bool {
        match row {
            _ if depth > MAX_UNFOLDED_DEPTH => false,
            Row::Extend {
                label, field, rest, ..
            }
            | Row::Maybe {
                label, field, rest, ..
            } => {
                route.push(format!("its `{label}` {noun}"));
                if in_ty(var, field, route, depth + 1) {
                    return true;
                }
                route.pop();
                in_row(var, rest, route, noun, depth + 1)
            }
            Row::Empty | Row::Var(_) => false,
        }
    }
    fn in_ty(var: TypeVar, ty: &Ty, route: &mut Vec<String>, depth: usize) -> bool {
        match ty {
            _ if depth > MAX_UNFOLDED_DEPTH => false,
            Ty::Var(v) => *v == var,
            Ty::Func(args, ret) => {
                for arg in args {
                    route.push("its argument".to_string());
                    if in_ty(var, arg, route, depth + 1) {
                        return true;
                    }
                    route.pop();
                }
                route.push("its result".to_string());
                if in_ty(var, ret, route, depth + 1) {
                    return true;
                }
                route.pop();
                false
            }
            Ty::Record(row) => in_row(var, row, route, "field", depth + 1),
            Ty::Variant(row) => in_row(var, row, route, "tag", depth + 1),
            Ty::Rec(_, body) => in_ty(var, body, route, depth + 1),
            _ => false,
        }
    }
    let mut route = Vec::new();
    if in_ty(var, ty, &mut route, 0) {
        route
    } else {
        Vec::new()
    }
}

fn infer_with_variable_markers(
    root: &Expr,
    interactive: Option<&Interactive>,
    vocab: &Vocab,
    dots: DotCalls,
) -> (Typed, Vec<GoatError>) {
    let mut inf = Inferer {
        dots,
        ..Inferer::default()
    };
    let ty = inf.infer(root);
    if let (true, Some(contract)) = (inf.errors.is_empty(), interactive) {
        inf.check_contract(contract, vocab);
    }
    inf.report_spent_ids(root.span);
    inf.default_numbers();
    inf.check_takes();
    inf.report_outgrown_types();
    let warnings = if inf.errors.is_empty() {
        inf.unused_tag_warnings()
    } else {
        Vec::new()
    };
    let root_ty = inf.finish_within_budget(&ty).unwrap_or(Ty::Unit);
    let node_types = inf
        .node_types
        .iter()
        .filter_map(|(id, t)| Some((*id, inf.finish_within_budget(t)?)))
        .collect();
    let schemes = inf
        .schemes
        .iter()
        .filter_map(|(symbol, s)| {
            let scheme = Scheme {
                vars: s.vars.clone(),
                ty: inf.finish_within_budget(&s.ty)?,
            };
            Some((*symbol, scheme))
        })
        .collect();
    let binder_types = inf
        .binders
        .iter()
        .filter_map(|(symbol, t)| Some((*symbol, inf.finish_within_budget(t)?)))
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
    subst: HashMap<TypeVar, Rc<Ty>>,
    row_subst: HashMap<TypeVar, Rc<Row>>,
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
    /// Where each parameter (or field path off one) was first used, for the
    /// message when a later use disagrees.
    first_uses: HashMap<(Symbol, String), Span>,
    /// A parameter given a function literal right at its call, by the text of
    /// that literal and of the body the call's function runs.
    literal_args: HashMap<Symbol, (String, String)>,
    /// Computed `=` bindings that keep a monotype where a value would have
    /// been generalized, by their name.
    restricted: HashMap<Symbol, String>,
    dots: DotCalls,
    /// The type `self` takes in the method the next `Func` is, set just before
    /// inferring it.
    method_self: Option<Ty>,
    /// The receiver variable of each record literal whose methods are being
    /// inferred, with the record it stands for: the literal's fields as
    /// variables, plus a row for whatever a later extension adds. The variable
    /// is never bound until the literal is done, so a method that calls a
    /// sibling through `self` mentions it without cycling through its own
    /// type; unifying it unifies its record instead.
    self_defs: HashMap<TypeVar, Ty>,
    /// The method flag of each `Field` a dot call or a `::` names.
    field_flags: HashMap<ExprId, Ty>,
    /// The argument spans of the call whose callee is the `r::f` inferred next.
    take_args: Option<(ExprId, Vec<Span>)>,
    /// The `r::f` takes that named a method and were reported.
    method_takes: HashSet<ExprId>,
    /// The parameter names of the plain functions written in record literals,
    /// by field label, for the hint a dot call on one gives.
    plain_fns: HashMap<String, Vec<String>>,
    node_types: HashMap<ExprId, Ty>,
    node_spans: HashMap<ExprId, Span>,
    schemes: HashMap<Symbol, Scheme>,
    binders: HashMap<Symbol, Ty>,
    constructed: Vec<(String, Span)>,
    matched: HashSet<String>,
    /// Pairs of types [`Inferer::unify_ty`] is already unifying or has unified,
    /// within one top-level [`Inferer::unify`].
    assumed: Assumed,
    /// Knots tied within the current top-level unify; see [`MAX_KNOTS_PER_UNIFY`].
    knots_tied: usize,
    /// Whether the current top-level unify already reported a spent budget.
    too_complex: bool,
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
    /// The span of the expression being inferred, which a variable created now
    /// takes as its origin.
    cursor: Option<Span>,
    /// Where each variable was created, for the label a failed call carries.
    /// Instantiating a scheme copies its variables' origins, so a type that
    /// came from a helper still points into the helper.
    origins: HashMap<TypeVar, Span>,
    /// The call whose arguments are being unified, the only place an error
    /// borrows an origin. An origin inside the call adds nothing.
    call: Option<Span>,
}

/// The pairs of types [`Inferer::unify_ty`] is already unifying or has
/// unified, within one top-level [`Inferer::unify`]. Pairs are kept as they are
/// met, not resolved, so binding a variable inside one does not make it a new
/// pair, and a pair is found by its hash without copying it.
#[derive(Default)]
struct Assumed {
    buckets: HashMap<u64, Vec<(Ty, Ty)>>,
    len: usize,
}

impl Assumed {
    /// Record the pair, and whether it was new.
    fn insert(&mut self, a: &Ty, b: &Ty) -> bool {
        let mut hasher = std::hash::DefaultHasher::new();
        (a, b).hash(&mut hasher);
        let bucket = self.buckets.entry(hasher.finish()).or_default();
        if bucket.iter().any(|(x, y)| x == a && y == b) {
            return false;
        }
        bucket.push((a.clone(), b.clone()));
        self.len += 1;
        true
    }

    fn clear(&mut self) {
        self.buckets.clear();
        self.len = 0;
    }
}

/// A type seen through the substitution: borrowed when nothing was bound, or
/// the shared type a variable is bound to.
enum Head<'a> {
    Borrowed(&'a Ty),
    Shared(Rc<Ty>),
}

impl Deref for Head<'_> {
    type Target = Ty;
    fn deref(&self) -> &Ty {
        match self {
            Head::Borrowed(ty) => ty,
            Head::Shared(ty) => ty,
        }
    }
}

/// A budget ran out, and the error is reported.
struct Spent;

/// How [`Inferer::unify_row`] sees past the front of a row.
enum Peel<'r> {
    Done,
    Bound(Rc<Row>),
    Rest(&'r Row),
    /// A field known present, as a plain field, the rest left unresolved:
    /// resolving the whole row here would walk it with no budget.
    Present(Row),
}

/// `row`'s first field when it is `label`: whether it is there (a presence),
/// its type, its method flag, and the rest of the row.
fn front<'r>(row: &'r Row, label: &str) -> Option<(Ty, &'r Ty, &'r Ty, &'r Row)> {
    match row {
        Row::Extend {
            label: l,
            field,
            method,
            rest,
        } if l == label => Some((PRESENT, field, method, rest)),
        Row::Maybe {
            label: l,
            pres,
            field,
            method,
            rest,
        } if l == label => Some((Ty::Var(*pres), field, method, rest)),
        _ => None,
    }
}

/// Whether `text` names a record the way a receiver does: `ball`, `a.b`.
fn is_path(text: &str) -> bool {
    text.split('.').all(|part| {
        part.chars()
            .next()
            .is_some_and(|c| c.is_alphabetic() || c == '_')
            && part.chars().all(|c| c.is_alphanumeric() || c == '_')
    })
}

/// Whether `expr` is a function whose first parameter is `self`.
fn is_method(expr: &Expr) -> bool {
    matches!(&expr.kind, ExprKind::Func { params, .. } if params.first().is_some_and(|p| p.name == SELF_NAME))
}

/// The order a record literal's fields are inferred in: source order, except
/// that the methods take each other's places so a method comes after the
/// siblings it calls through `self`. A caller that reaches a sibling's result
/// before the sibling is typed cannot tell it is the receiver (see
/// [`Inferer::settle_updater`]). Methods that call each other in a cycle keep
/// source order.
fn inference_order(fields: &[(String, Expr)]) -> Vec<usize> {
    let methods: Vec<usize> = (0..fields.len())
        .filter(|&i| is_method(&fields[i].1))
        .collect();
    let calls: Vec<Vec<usize>> = methods
        .iter()
        .map(|&i| {
            let mut called = Vec::new();
            for_each_node(&fields[i].1, &mut |e| {
                if let ExprKind::Field { record, label } = &e.kind
                    && matches!(&record.kind, ExprKind::Var { name, .. } if name == SELF_NAME)
                    && let Some(&j) = methods.iter().find(|&&j| fields[j].0 == *label)
                    && j != i
                    && !called.contains(&j)
                {
                    called.push(j);
                }
            });
            called
        })
        .collect();
    let mut done = vec![false; fields.len()];
    let mut ordered = Vec::with_capacity(methods.len());
    while ordered.len() < methods.len() {
        let pending = || (0..methods.len()).filter(|&m| !done[methods[m]]);
        let next = pending()
            .find(|&m| calls[m].iter().all(|&j| done[j]))
            .or_else(|| pending().next())
            .expect("a method is left");
        done[methods[next]] = true;
        ordered.push(methods[next]);
    }
    let mut ordered = ordered.into_iter();
    (0..fields.len())
        .map(|i| {
            if is_method(&fields[i].1) {
                ordered.next().expect("one per method")
            } else {
                i
            }
        })
        .collect()
}

/// Whether evaluating `expr` can do no work, so its binding may be generalized:
/// a function, a literal, a name, or a record or variant of such values.
/// Anything else is computed and keeps one type.
fn is_syntactic_value(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Var { .. }
        | ExprKind::Builtin(_)
        | ExprKind::Foreign { .. }
        | ExprKind::Func { .. } => true,
        ExprKind::Record { fields } => fields.iter().all(|(_, field)| is_syntactic_value(field)),
        ExprKind::Spread { base, fields } => {
            is_syntactic_value(base) && fields.iter().all(|(_, field)| is_syntactic_value(field))
        }
        ExprKind::Tag { payload, .. } => payload.as_deref().is_none_or(is_syntactic_value),
        _ => false,
    }
}

/// Knots one top-level unify may tie. Each knot mints fresh binders, so the
/// assumed-equal set (see [`Inferer::unify_ty`]) cannot bound a unify that
/// keeps tying new ones; this does.
const MAX_KNOTS_PER_UNIFY: usize = 16;

/// Terms a type may have while unification unfolds it or binds a variable to
/// it. Unfolding copies the whole `μ` into its body, so mismatched recursive
/// types can double at every step.
const MAX_UNFOLDED_TERMS: usize = 4 * MAX_TYPE_TERMS;

/// The same for how deep the type nests.
const MAX_UNFOLDED_DEPTH: usize = 4 * MAX_TYPE_DEPTH;

/// What walking a type may still spend: terms to count, and levels to descend.
struct Budget {
    terms: usize,
    levels: usize,
}

impl Budget {
    fn for_type() -> Budget {
        Budget {
            terms: MAX_TYPE_TERMS,
            levels: MAX_TYPE_DEPTH,
        }
    }

    fn for_unfolding() -> Budget {
        Budget {
            terms: MAX_UNFOLDED_TERMS,
            levels: MAX_UNFOLDED_DEPTH,
        }
    }

    fn spend(&mut self, depth: usize) -> Option<()> {
        self.terms = self.terms.checked_sub(1)?;
        (depth <= self.levels).then_some(())
    }
}

/// Distinct pairs of recursive types one top-level unify may compare. Growing
/// an open row while unfolding can mint a new pair at every step.
const MAX_UNFOLDINGS_PER_UNIFY: usize = 256;

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
        if let Some(span) = self.cursor
            && !span.in_prelude()
        {
            self.origins.insert(v, span);
        }
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
        let head = self.resolve(ty).unfold_head();
        match self.self_def(&head) {
            Some(def) => self.resolve(def),
            None => self.undecided_as_int(head),
        }
    }

    /// The record a receiver variable stands for while its literal is being
    /// inferred.
    fn self_def(&self, ty: &Ty) -> Option<&Ty> {
        match ty {
            Ty::Var(v) => self.self_defs.get(v),
            _ => None,
        }
    }

    /// `ty` with each receiver variable in it replaced by the recursive type
    /// it stands for, for output a person reads.
    fn open_selves(&self, ty: Ty) -> Ty {
        if self.self_defs.is_empty() {
            return ty;
        }
        self.open_selves_except(ty, &mut Vec::new())
    }

    fn open_selves_except(&self, ty: Ty, opened: &mut Vec<TypeVar>) -> Ty {
        let mut vars = BTreeSet::new();
        ty.free_vars(&mut vars);
        vars.into_iter().fold(ty, |ty, var| {
            let Some(def) = self.self_defs.get(&var).filter(|_| !opened.contains(&var)) else {
                return ty;
            };
            opened.push(var);
            let body = self.open_selves_except(self.resolve(def), opened);
            opened.pop();
            ty.substitute(var, &Ty::Rec(var, Box::new(body)))
        })
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
        self.open_selves(self.resolve(ty)).into_folded()
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
            Row::Extend {
                label,
                field,
                method,
                rest,
            } => Row::Extend {
                label: label.clone(),
                field: Box::new(self.resolve(field)),
                method: Box::new(self.resolve(method)),
                rest: Box::new(self.resolve_row(rest)),
            },
            Row::Maybe {
                label,
                pres,
                field,
                method,
                rest,
            } => match self.resolve(&Ty::Var(*pres)) {
                present if present == PRESENT => Row::Extend {
                    label: label.clone(),
                    field: Box::new(self.resolve(field)),
                    method: Box::new(self.resolve(method)),
                    rest: Box::new(self.resolve_row(rest)),
                },
                absent if absent == ABSENT => self.resolve_row(rest),
                Ty::Var(pres) => Row::Maybe {
                    label: label.clone(),
                    pres,
                    field: Box::new(self.resolve(field)),
                    method: Box::new(self.resolve(method)),
                    rest: Box::new(self.resolve_row(rest)),
                },
                _ => unreachable!("a presence variable is bound to a presence or a variable"),
            },
            Row::Empty => Row::Empty,
        }
    }

    /// For a parameter or a field chain off one, the parameter and the written
    /// path (`m`, `m.id`).
    fn param_path(&self, expr: &Expr) -> Option<(Symbol, String, String)> {
        match &expr.kind {
            ExprKind::Var { symbol, name } => self
                .params
                .contains_key(symbol)
                .then(|| (*symbol, name.clone(), name.clone())),
            ExprKind::Field { record, label } => {
                let (symbol, root, path) = self.param_path(record)?;
                Some((symbol, root, format!("{path}.{label}")))
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
        let param = self.param_path(used);
        let first = param
            .as_ref()
            .and_then(|(symbol, _, path)| self.first_uses.get(&(*symbol, path.clone())))
            .copied();
        self.note_first_use(used, span);
        let before = self.errors.len();
        self.unify(actual, expected, span);
        if reused
            && self.errors.len() > before
            && let Some((symbol, root, path)) = param
        {
            self.errors.truncate(before);
            let error =
                self.two_ways_error(symbol, (&root, &path), first, actual, (span, expected));
            self.errors.push(error);
        }
    }

    /// Remember where a parameter, or a field path off one, is first used.
    fn note_first_use(&mut self, used: &Expr, span: Span) {
        if let Some((symbol, _, path)) = self.param_path(used) {
            self.first_uses.entry((symbol, path)).or_insert(span);
        }
    }

    /// The error for a parameter used at two types: the two kinds found, a
    /// note on each use, and how to name the value so each use gets its own.
    /// `found` is the type the earlier use fixed, `second` what this use needs.
    fn two_ways_error(
        &self,
        symbol: Symbol,
        (root, path): (&str, &str),
        first: Option<Span>,
        found: &Ty,
        (span, needed): (Span, &Ty),
    ) -> GoatError {
        let (here, there) = first_difference(&self.shown(found), &self.shown(needed));
        let is_function = matches!(self.resolve(found), Ty::Func(..));
        let (here, there) = (kind_of(&here), kind_of(&there));
        let (thing, one_kind) = if is_function {
            ("a function", "take")
        } else {
            ("a value", "be")
        };
        let mut message = format!(
            "`{path}` gets {here} here and {there} there, but {thing} you pass in can only {one_kind} one kind of thing."
        );
        match self.literal_args.get(&symbol).filter(|_| path == root) {
            Some((literal, body)) => message.push_str(&format!(
                "\nGive the function a name first, then use it both ways:\n```\n{root} = {literal}\n{body}\n```"
            )),
            None if is_function => message.push_str(
                "\nPass a separate function for each kind, or give the function a name with `=` where you use it.",
            ),
            None => message.push_str(
                "\nPass a separate value for each kind, or give it a name with `=` where you use it.",
            ),
        }
        let mut error = GoatError::new(span, message);
        if let Some(first) = first {
            error = error.with_label(first, format!("`{path}` gets {here} here"));
        }
        error.with_label(span, format!("`{path}` gets {there} here"))
    }

    /// Remember the function literals passed straight to a function literal
    /// that is called on the spot, so a message can quote them.
    fn note_literal_args(&mut self, callee: &Expr, args: &[Expr]) {
        let ExprKind::Func { params, body } = &callee.kind else {
            return;
        };
        for (param, arg) in params.iter().zip(args) {
            if matches!(arg.kind, ExprKind::Func { .. }) {
                let body = self.quoted(body.span);
                let literal = self.quoted(arg.span);
                self.literal_args.insert(param.symbol, (literal, body));
            }
        }
    }

    /// The source text at `span`, kept to a short single line: a longer
    /// function literal reads `program(x) do … done`, anything else `…`.
    fn quoted(&self, span: Span) -> String {
        const SHORT: usize = 40;
        let text = self
            .dots
            .source
            .get(span.start..span.end)
            .unwrap_or("")
            .trim();
        if text.len() <= SHORT && !text.contains('\n') {
            return text.to_string();
        }
        match text.find(" do") {
            Some(at) if text.ends_with("done") => format!("{} do … done", &text[..at]),
            _ => "…".to_string(),
        }
    }

    fn unify(&mut self, a: &Ty, b: &Ty, span: Span) {
        self.unify_ty(a, b, span);
        self.assumed.clear();
        self.knots_tied = 0;
        self.too_complex = false;
    }

    fn report_too_complex(&mut self, span: Span) {
        if !self.too_complex {
            self.too_complex = true;
            self.errors.push(GoatError::new(
                span,
                "program too complex: these types grow too large to unify",
            ));
        }
    }

    fn unify_ty(&mut self, a: &Ty, b: &Ty, span: Span) {
        let (a_held, b_held) = (self.head(a), self.head(b));
        let (mut a, mut b): (&Ty, &Ty) = (&a_held, &b_held);
        if self.unify_selves(a, b, span) {
            return;
        }
        // Between two variables the newer is bound to the older, so a variable
        // unified once per statement stays one link from its root.
        if self.self_def(a).is_some()
            || matches!((a, b), (Ty::Var(x), Ty::Var(y)) if x < y && self.self_def(b).is_none())
        {
            std::mem::swap(&mut a, &mut b);
        }
        match (a, b) {
            (Ty::Var(x), Ty::Var(y)) if x == y => {}
            (Ty::Var(x), t) | (t, Ty::Var(x)) => {
                if !self.within_unfold_budget(t) {
                    self.report_too_complex(span);
                    return;
                }
                let bound = if !self.occurs_deep(*x, t) {
                    t.clone()
                } else if let Some(rec) = self.tie_ty_knot(*x, &self.resolve(t)) {
                    if !self.within_unfold_budget(&rec) {
                        self.report_too_complex(span);
                        return;
                    }
                    rec
                } else {
                    let route = cycle_route(*x, &self.resolve(t)).join(", then ");
                    let through = if route.is_empty() {
                        String::new()
                    } else {
                        format!(" (through {route})")
                    };
                    self.errors.push(GoatError::new(
                        span,
                        format!(
                            "this value would have to contain itself{through}, which can't be built"
                        ),
                    ));
                    return;
                };
                let bound = Rc::new(bound);
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
                        let (found, expected) = match a {
                            Ty::Var(v) if v == x => ("Number".to_string(), shown),
                            _ => (shown, "Number".to_string()),
                        };
                        let message =
                            format!("type mismatch: expected `{expected}`, found `{found}`");
                        self.report_with_origin(span, message, [&bound]);
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
                if a == b {
                    return;
                }
                if self.assumed.len > MAX_UNFOLDINGS_PER_UNIFY
                    || !self.within_unfold_budget(a)
                    || !self.within_unfold_budget(b)
                {
                    self.report_too_complex(span);
                    return;
                }
                if self.assumed.insert(a, b) {
                    let unfold = |ty: &Ty| matches!(ty, Ty::Rec(..)).then(|| ty.unfold_head());
                    let (a_open, b_open) = (unfold(a), unfold(b));
                    self.unify_ty(
                        a_open.as_ref().unwrap_or(a),
                        b_open.as_ref().unwrap_or(b),
                        span,
                    );
                }
            }
            (Ty::Int, Ty::Int)
            | (Ty::Float, Ty::Float)
            | (Ty::Str, Ty::Str)
            | (Ty::Bool, Ty::Bool)
            | (Ty::Unit, Ty::Unit) => {}
            (Ty::Func(a_args, a_ret), Ty::Func(b_args, b_ret)) => {
                if a_args.len() != b_args.len() {
                    let message = format!(
                        "function expects {} argument(s) but got {}",
                        a_args.len(),
                        b_args.len()
                    );
                    self.report_with_origin(span, message, [a, b]);
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
                let (a, b) = (self.shown(a), self.shown(b));
                let (found, expected) = match (a.to_string(), b.to_string()) {
                    (found, expected) if found == expected => {
                        (a.exact().to_string(), b.exact().to_string())
                    }
                    shown => shown,
                };
                let message = format!("type mismatch: expected `{expected}`, found `{found}`");
                self.report_with_origin(span, message, [&a, &b]);
            }
        }
    }

    /// Report a clash between two shapes. In a call, the error also points at
    /// where the helper's side of the clash was required, unless that is
    /// inside the call itself or in the prelude.
    fn report_with_origin<const N: usize>(
        &mut self,
        span: Span,
        message: String,
        shapes: [&Ty; N],
    ) {
        let origin = shapes
            .into_iter()
            .find_map(|ty| self.origin_of(ty).filter(|o| !self.inside_call(*o)));
        self.report_at_origin(span, message, origin);
    }

    fn report_at_origin(&mut self, span: Span, message: String, origin: Option<Span>) {
        let mut error = GoatError::new(span, message);
        if self.call.is_some()
            && let Some(origin) = origin
        {
            error = error.with_label(origin, "this is the use the call has to satisfy");
        }
        self.errors.push(error);
    }

    fn inside_call(&self, span: Span) -> bool {
        self.call
            .is_some_and(|call| call.start <= span.start && span.end <= call.end)
    }

    /// Where the open end of `ty` was created: a record or variant's row
    /// variable, or a function's result variable.
    fn origin_of(&self, ty: &Ty) -> Option<Span> {
        let var = match ty {
            Ty::Record(row) | Ty::Variant(row) => row_shape(row).1?,
            Ty::Func(_, ret) => match self.resolve(ret) {
                Ty::Var(v) => v,
                _ => return None,
            },
            _ => return None,
        };
        self.origins.get(&var).copied()
    }

    /// Unify where a side is a receiver variable. It is never bound: against a
    /// plain variable the plain one is bound to it (left to the caller), and
    /// against any other type its record is unified instead. Whether the pair
    /// is settled here.
    fn unify_selves(&mut self, a: &Ty, b: &Ty, span: Span) -> bool {
        if self.self_defs.is_empty() {
            return false;
        }
        let (a_def, b_def) = (self.self_def(a).cloned(), self.self_def(b).cloned());
        match (a_def, b_def) {
            (None, None) => false,
            (Some(_), Some(_)) if a == b => true,
            (Some(def), None) if !matches!(b, Ty::Var(_)) => {
                self.unify_through(a, b, &def, b, span);
                true
            }
            (None, Some(def)) if !matches!(a, Ty::Var(_)) => {
                self.unify_through(a, b, a, &def, span);
                true
            }
            (Some(a_def), Some(b_def)) => {
                self.unify_through(a, b, &a_def, &b_def, span);
                true
            }
            _ => false,
        }
    }

    fn unify_through(&mut self, a: &Ty, b: &Ty, left: &Ty, right: &Ty, span: Span) {
        if self.assumed.len > MAX_UNFOLDINGS_PER_UNIFY {
            self.report_too_complex(span);
        } else if self.assumed.insert(a, b) {
            self.unify_ty(left, right, span);
        }
    }

    fn unify_row(&mut self, a: &Row, b: &Row, span: Span, kind: RowKind) {
        match self.peel(a) {
            Peel::Done => {}
            Peel::Bound(row) => return self.unify_row(&row, b, span, kind),
            Peel::Rest(row) => return self.unify_row(row, b, span, kind),
            Peel::Present(row) => return self.unify_row(&row, b, span, kind),
        }
        match self.peel(b) {
            Peel::Done => {}
            Peel::Bound(row) => return self.unify_row(a, &row, span, kind),
            Peel::Rest(row) => return self.unify_row(a, row, span, kind),
            Peel::Present(row) => return self.unify_row(a, &row, span, kind),
        }
        match (a, b) {
            (Row::Empty, Row::Empty) => {}
            (Row::Var(x), Row::Var(y)) if x == y => {}
            (Row::Var(x), other) | (other, Row::Var(x)) => {
                if let Some(banned) = self.lacks.get(x).cloned()
                    && let Some(label) = self.lack(other, &banned)
                {
                    self.report_hidden_label(span, &label);
                }
                if self
                    .spend_on_row(other, &mut Budget::for_unfolding(), 0)
                    .is_none()
                {
                    self.report_too_complex(span);
                    return;
                }
                let bound = if !self.occurs_row_deep(*x, other) {
                    other.clone()
                } else if let Some(rec) = self.tie_row_knot(*x, kind, &self.resolve_row(other)) {
                    if self
                        .spend_on_row(&rec, &mut Budget::for_unfolding(), 0)
                        .is_none()
                    {
                        self.report_too_complex(span);
                        return;
                    }
                    rec
                } else {
                    let message = format!(
                        "this {} would have to contain itself, which can't be built",
                        kind.noun()
                    );
                    self.errors.push(GoatError::new(span, message));
                    return;
                };
                self.row_subst.insert(*x, Rc::new(bound.clone()));
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
            (
                Row::Maybe {
                    label,
                    pres,
                    field,
                    method,
                    rest,
                },
                _,
            ) => match front(b, label) {
                Some((b_pres, b_field, b_method, b_rest)) => {
                    self.unify_presence(&Ty::Var(*pres), &b_pres, span);
                    self.unify_method(label, method, b_method, span);
                    self.unify_ty(field, b_field, span);
                    self.unify_row(rest, b_rest, span, kind);
                }
                None => match self.surface_bounded(label, b, true, span) {
                    Err(Spent) => {}
                    Ok(Some((b_pres, b_field, b_method, b_rest))) => {
                        self.unify_presence(&Ty::Var(*pres), &b_pres, span);
                        self.unify_method(label, method, &b_method, span);
                        self.unify_ty(field, &b_field, span);
                        self.unify_row(rest, &b_rest, span, kind);
                    }
                    Ok(None) => {
                        self.subst.insert(*pres, Rc::new(ABSENT));
                        self.unify_row(rest, b, span, kind);
                    }
                },
            },
            (
                Row::Extend {
                    label,
                    field,
                    method,
                    rest,
                },
                _,
            ) => match front(b, label) {
                Some((b_pres, b_field, b_method, b_rest)) => {
                    self.unify_presence(&PRESENT, &b_pres, span);
                    self.unify_method(label, method, b_method, span);
                    self.unify_ty(field, b_field, span);
                    self.unify_row(rest, b_rest, span, kind);
                }
                None => match self.surface_bounded(label, b, false, span) {
                    Err(Spent) => {}
                    Ok(Some((b_pres, b_field, b_method, b_rest))) => {
                        self.unify_presence(&PRESENT, &b_pres, span);
                        self.unify_method(label, method, &b_method, span);
                        self.unify_ty(field, &b_field, span);
                        self.unify_row(rest, &b_rest, span, kind);
                    }
                    Ok(None) => {
                        let message = match kind {
                            RowKind::Record => format!("record has an unexpected field `{label}`"),
                            RowKind::Variant => format!(
                                "the tag `{label}` is not allowed here; the other side never has it"
                            ),
                        };
                        self.report_with_row_origin(span, message, [a, b]);
                    }
                },
            },
            (Row::Empty, Row::Maybe { pres, rest, .. }) => {
                self.subst.insert(*pres, Rc::new(ABSENT));
                self.unify_row(&Row::Empty, rest, span, kind);
            }
            (Row::Empty, Row::Extend { label, .. }) => {
                let message = match kind {
                    RowKind::Record => format!("record is missing field `{label}`"),
                    RowKind::Variant => format!(
                        "the tag `{label}` is expected here, but this value is never `{label}`"
                    ),
                };
                self.report_with_row_origin(span, message, [a, b]);
            }
        }
    }

    fn report_with_row_origin(&mut self, span: Span, message: String, rows: [&Row; 2]) {
        let origin = rows.into_iter().find_map(|row| {
            let origin = self.origins.get(&row_shape(row).1?).copied()?;
            Some(origin).filter(|o| !self.inside_call(*o))
        });
        self.report_at_origin(span, message, origin);
    }

    /// [`Self::surface`] on a row that is within [`MAX_UNFOLDED_TERMS`], for
    /// surfacing resolves the whole row.
    fn surface_bounded(
        &mut self,
        label: &str,
        row: &Row,
        optional: bool,
        span: Span,
    ) -> Result<Option<(Ty, Ty, Ty, Row)>, Spent> {
        if self
            .spend_on_row(row, &mut Budget::for_unfolding(), 0)
            .is_none()
        {
            self.report_too_complex(span);
            return Err(Spent);
        }
        Ok(self.surface(label, row, optional))
    }

    /// What stands between `row` and its first field: a row variable bound to
    /// a row, a field known to be absent, or a field known to be present.
    fn peel<'r>(&self, row: &'r Row) -> Peel<'r> {
        match row {
            Row::Var(v) => self
                .row_subst
                .get(v)
                .cloned()
                .map_or(Peel::Done, Peel::Bound),
            Row::Maybe {
                label,
                pres,
                field,
                method,
                rest,
            } => match self.resolve(&Ty::Var(*pres)) {
                absent if absent == ABSENT => Peel::Rest(rest),
                present if present == PRESENT => Peel::Present(Row::Extend {
                    label: label.clone(),
                    field: field.clone(),
                    method: method.clone(),
                    rest: rest.clone(),
                }),
                _ => Peel::Done,
            },
            _ => Peel::Done,
        }
    }

    /// `ty`, followed through the substitution until its outermost
    /// constructor or an unbound variable shows, without copying anything.
    fn head<'a>(&self, ty: &'a Ty) -> Head<'a> {
        let Ty::Var(v) = ty else {
            return Head::Borrowed(ty);
        };
        let Some(mut bound) = self.subst.get(v).cloned() else {
            return Head::Borrowed(ty);
        };
        while let Ty::Var(next) = &*bound {
            let Some(deeper) = self.subst.get(next).cloned() else {
                break;
            };
            bound = deeper;
        }
        Head::Shared(bound)
    }

    fn occurs_deep(&self, var: TypeVar, ty: &Ty) -> bool {
        match ty {
            Ty::Var(v) => {
                *v == var
                    || self
                        .subst
                        .get(v)
                        .is_some_and(|bound| self.occurs_deep(var, bound))
            }
            Ty::Func(args, ret) => {
                args.iter().any(|a| self.occurs_deep(var, a)) || self.occurs_deep(var, ret)
            }
            Ty::Record(row) | Ty::Variant(row) => self.occurs_row_deep(var, row),
            Ty::Rec(_, body) => self.occurs_deep(var, body),
            _ => false,
        }
    }

    fn occurs_row_deep(&self, var: TypeVar, row: &Row) -> bool {
        match row {
            Row::Empty => false,
            Row::Var(v) => {
                *v == var
                    || self
                        .row_subst
                        .get(v)
                        .is_some_and(|bound| self.occurs_row_deep(var, bound))
            }
            Row::Extend { field, rest, .. } | Row::Maybe { field, rest, .. } => {
                self.occurs_deep(var, field) || self.occurs_row_deep(var, rest)
            }
        }
    }

    fn spend_knot(&mut self) -> Option<()> {
        self.knots_tied += 1;
        (self.knots_tied <= MAX_KNOTS_PER_UNIFY).then_some(())
    }

    /// `x = t` where `t` mentions `x`: the recursive type `μv. t[x := v]`, if
    /// every mention is guarded (see [`Guard`]).
    fn tie_ty_knot(&mut self, x: TypeVar, t: &Ty) -> Option<Ty> {
        self.spend_knot()?;
        let binder = self.fresh_id();
        let body = plug(
            t,
            &Hole::Ty(x),
            &Ty::Var(binder),
            Guard::default(),
            &mut Vec::new(),
        );
        (!occurs(x, &body)).then(|| Ty::Rec(binder, Box::new(body)))
    }

    /// `x = row` where `row` mentions `x`. Allowed only when every mention is
    /// the same `kind` type, `[x]` or `[l: t | x]` (and likewise for records),
    /// guarded (see [`Guard`]): that type is then `row` behind the prefix, so
    /// it is the recursive type `μv. [prefix | row[mention := v]]`. `x` becomes
    /// `row` with that type in place of the mentions.
    fn tie_row_knot(&mut self, x: TypeVar, kind: RowKind, row: &Row) -> Option<Row> {
        self.spend_knot()?;
        let under_tag = match kind {
            RowKind::Variant => Guard::default().tag(),
            RowKind::Record => Guard::default().field(),
        };
        let mention = find_mention(row, x, kind, under_tag, &mut Vec::new())?;
        let hole = Hole::Mention(kind, mention.clone());
        let binder = self.fresh_id();
        let inner = plug_row(row, &hole, &Ty::Var(binder), under_tag, &mut Vec::new());
        if occurs_row(x, &inner) {
            return None;
        }
        let rec = Ty::Rec(binder, Box::new(kind.wrap(replace_tail(&mention, inner))));
        if occurs(x, &rec) {
            return None;
        }
        Some(plug_row(row, &hole, &rec, under_tag, &mut Vec::new()))
    }

    /// Surface `label` in `row`, returning whether it is present, its field
    /// type, and the row without it. An open row (ending in a row variable) is
    /// grown with a fresh field, present unless `optional`; a closed row
    /// missing the label yields `None`. Fields ahead of `label` keep their
    /// position and their presence. The recursion is as deep as the row is
    /// long, which [`MAX_TYPE_TERMS`] caps: every row grows by one inferred
    /// expression at a time and each is checked.
    fn surface(&mut self, label: &str, row: &Row, optional: bool) -> Option<(Ty, Ty, Ty, Row)> {
        match self.resolve_row(row) {
            Row::Empty => None,
            Row::Extend {
                label: l2,
                field,
                method,
                rest,
            } => {
                if l2 == label {
                    Some((PRESENT, *field, *method, *rest))
                } else {
                    let (p, f, m, r) = self.surface(label, &rest, optional)?;
                    Some((
                        p,
                        f,
                        m,
                        Row::Extend {
                            label: l2,
                            field,
                            method,
                            rest: Box::new(r),
                        },
                    ))
                }
            }
            Row::Maybe {
                label: l2,
                pres,
                field,
                method,
                rest,
            } => {
                if l2 == label {
                    Some((Ty::Var(pres), *field, *method, *rest))
                } else {
                    let (p, f, m, r) = self.surface(label, &rest, optional)?;
                    Some((
                        p,
                        f,
                        m,
                        Row::Maybe {
                            label: l2,
                            pres,
                            field,
                            method,
                            rest: Box::new(r),
                        },
                    ))
                }
            }
            Row::Var(v) => {
                let mut banned = self.lacks.get(&v).cloned().unwrap_or_default();
                if banned.contains(label) {
                    return None;
                }
                let kinds = self.row_kinds.get(&v).copied().unwrap_or_default();
                if kinds.appendable() && !is_list_tag(label) {
                    return None;
                }
                let field = self.fresh();
                let rest = self.fresh_row();
                if let Some(origin) = self.origins.get(&v).copied()
                    && let Row::Var(r) = &rest
                {
                    self.origins.insert(*r, origin);
                }
                let method = self.fresh();
                banned.insert(label.to_string());
                self.lack(&rest, &banned);
                if let (Ty::Var(f), Row::Var(r)) = (&field, &rest) {
                    self.kinds.insert(*f, kinds.for_fields());
                    self.row_kinds.insert(*r, kinds);
                }
                let (pres, grown) = if optional {
                    let pres = self.fresh_id();
                    (
                        Ty::Var(pres),
                        Row::Maybe {
                            label: label.to_string(),
                            pres,
                            field: Box::new(field.clone()),
                            method: Box::new(method.clone()),
                            rest: Box::new(rest.clone()),
                        },
                    )
                } else {
                    (
                        PRESENT,
                        Row::Extend {
                            label: label.to_string(),
                            field: Box::new(field.clone()),
                            method: Box::new(method.clone()),
                            rest: Box::new(rest.clone()),
                        },
                    )
                };
                self.row_subst.insert(v, Rc::new(grown));
                Some((pres, field, method, rest))
            }
        }
    }

    /// Make two method flags agree: a variable takes the other side, and a
    /// field cannot be a method in one record and a plain value in the other.
    fn unify_method(&mut self, label: &str, a: &Ty, b: &Ty, span: Span) {
        let (a, b) = (self.resolve(a), self.resolve(b));
        match (&a, &b) {
            _ if a == b => {}
            (Ty::Var(v), other) | (other, Ty::Var(v)) => {
                self.subst.insert(*v, Rc::new(other.clone()));
            }
            _ => self.errors.push(GoatError::new(
                span,
                format!(
                    "`{label}` is a method in one record and a plain function in the other, so they don't have the same shape. \
                     Start both with `self`, or neither."
                ),
            )),
        }
    }

    /// Make two presences agree: a variable takes the other side, and a field
    /// cannot be both there and not.
    fn unify_presence(&mut self, a: &Ty, b: &Ty, span: Span) {
        let (a, b) = (self.resolve(a), self.resolve(b));
        match (&a, &b) {
            _ if a == b => {}
            (Ty::Var(v), other) | (other, Ty::Var(v)) => {
                self.subst.insert(*v, Rc::new(other.clone()));
            }
            _ => self.errors.push(GoatError::new(
                span,
                "a field is here on one side and missing on the other",
            )),
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
            Row::Maybe {
                label, pres, rest, ..
            } => {
                if labels.contains(&label) {
                    self.subst.insert(pres, Rc::new(ABSENT));
                }
                self.lack(&rest, labels)
            }
        }
    }

    #[cold]
    fn report_hidden_label(&mut self, span: Span, label: &str) {
        self.errors.push(GoatError::new(
            span,
            format!(
                "`{label}` was taken out of this record with `...`, so a record that has `{label}` can't be put back in its place"
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
            (Ty::Var(v), _) if self.self_defs.contains_key(v) => {
                let def = self.self_defs[v].clone();
                bound.push(*v);
                let result = self.constrain_kind(&def, kind, bound);
                bound.pop();
                result
            }
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
            Row::Extend { field, rest, .. } | Row::Maybe { field, rest, .. } => {
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
                Row::Extend { label, rest, .. } | Row::Maybe { label, rest, .. } => {
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
            match self.origins.get(old).copied() {
                Some(origin) => self.origins.insert(*new, origin),
                None => self.origins.remove(new),
            };
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
        // A value that is the receiver of the literal being inferred (a method
        // call's result bound to a temporary) stays that variable: opening it
        // would copy the whole record type into every use.
        if let Ty::Var(var) = self.resolve(ty)
            && self.self_defs.contains_key(&var)
        {
            return Scheme::mono(Ty::Var(var));
        }
        let resolved = self.finish(ty);
        let mut in_ty = BTreeSet::new();
        resolved.free_vars(&mut in_ty);
        in_ty.retain(|v| function || !self.is_literal(*v));
        if !in_ty.is_empty() {
            let in_env = self.env_free_vars();
            let in_selves = self.self_def_vars();
            in_ty.retain(|v| {
                !in_env.contains(v) && !in_selves.contains(v) && !self.lone_vars.contains_key(v)
            });
        }
        Scheme {
            vars: in_ty.into_iter().collect(),
            ty: resolved,
        }
    }

    /// The variables inside the records receiver variables stand for. A method
    /// reaches them through `self`, which the environment holds as one
    /// variable, so generalizing must leave them alone too.
    fn self_def_vars(&self) -> BTreeSet<TypeVar> {
        let mut out = BTreeSet::new();
        for (var, def) in &self.self_defs {
            self.resolve(def).free_vars(&mut out);
            out.insert(*var);
        }
        out
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
    fn bind_var(&mut self, var: TypeVar, ty: Rc<Ty>) {
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
            self.row_subst.insert(var, Rc::new(Row::Empty));
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
            self.row_subst.insert(var, Rc::new(Row::Empty));
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
        self.cursor = Some(expr.span);
        let mut ty = self.infer_kind(expr);
        self.report_spent_ids(expr.span);
        if !self.within_term_budget(&ty) {
            self.errors.push(GoatError::new(
                expr.span,
                "program too complex: the type of this expression is larger than the checker handles",
            ));
            ty = self.fresh();
        }
        self.node_types.insert(expr.id, ty.clone());
        self.node_spans.insert(expr.id, expr.span);
        ty
    }

    /// Report the first expression whose type, with every variable
    /// substituted, has outgrown [`MAX_UNFOLDED_TERMS`], unless an error
    /// already stops the program. Each type was within
    /// [`MAX_TYPE_TERMS`] when inferred, but later bindings of the variables
    /// inside it can multiply it, and [`Self::finish`] walks the whole thing.
    fn report_outgrown_types(&mut self) {
        if !self.errors.is_empty() {
            return;
        }
        let outgrown = self
            .node_types
            .iter()
            .filter(|(_, ty)| !self.within_unfold_budget(ty))
            .filter_map(|(id, _)| self.node_spans.get(id).copied())
            .min_by_key(|span| (span.start, span.end));
        if let Some(span) = outgrown {
            self.errors.push(GoatError::new(
                span,
                "program too complex: the type of this expression is larger than the checker handles",
            ));
        }
    }

    /// [`Self::finish`], or `None` for a type over [`MAX_UNFOLDED_TERMS`],
    /// which [`Self::report_outgrown_types`] has reported.
    fn finish_within_budget(&self, ty: &Ty) -> Option<Ty> {
        self.within_unfold_budget(ty).then(|| self.finish(ty))
    }

    fn within_unfold_budget(&self, ty: &Ty) -> bool {
        self.spend_on_ty(ty, &mut Budget::for_unfolding(), 0)
            .is_some()
    }

    /// Whether `ty`, followed through the substitution, has at most
    /// [`MAX_TYPE_TERMS`] terms and nests at most [`MAX_TYPE_DEPTH`] deep.
    /// Counting stops once the budget is spent, so the cost is bounded however
    /// large the type is.
    fn within_term_budget(&self, ty: &Ty) -> bool {
        self.spend_on_ty(ty, &mut Budget::for_type(), 0).is_some()
    }

    fn spend_on_ty(&self, ty: &Ty, budget: &mut Budget, depth: usize) -> Option<()> {
        budget.spend(depth)?;
        match ty {
            Ty::Var(v) => match self.subst.get(v) {
                Some(bound) => self.spend_on_ty(bound, budget, depth + 1),
                None => Some(()),
            },
            Ty::Func(args, ret) => {
                for arg in args {
                    self.spend_on_ty(arg, budget, depth + 1)?;
                }
                self.spend_on_ty(ret, budget, depth + 1)
            }
            Ty::Record(row) | Ty::Variant(row) => self.spend_on_row(row, budget, depth + 1),
            Ty::Rec(_, body) => self.spend_on_ty(body, budget, depth + 1),
            Ty::Int | Ty::Float | Ty::Str | Ty::Bool | Ty::Unit => Some(()),
        }
    }

    fn spend_on_row(&self, row: &Row, budget: &mut Budget, depth: usize) -> Option<()> {
        budget.spend(depth)?;
        match row {
            Row::Var(v) => match self.row_subst.get(v) {
                Some(bound) => self.spend_on_row(bound, budget, depth + 1),
                None => Some(()),
            },
            Row::Extend { field, rest, .. } | Row::Maybe { field, rest, .. } => {
                self.spend_on_ty(field, budget, depth + 1)?;
                self.spend_on_row(rest, budget, depth + 1)
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
                name,
                value,
                rest,
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

            let mut scheme = self.generalize(&rec, matches!(value.kind, ExprKind::Func { .. }));
            if !scheme.vars.is_empty() && !is_syntactic_value(value) {
                self.restricted.insert(*symbol, name.clone());
                scheme = Scheme::mono(scheme.ty);
            }
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
                // A parameter is not a requirement, so it has no origin.
                self.cursor = None;
                let mut arg_tys: Vec<Ty> = params.iter().map(|_| self.fresh()).collect();
                if let Some(receiver) = self.method_self.take() {
                    arg_tys[0] = receiver;
                }
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
            ExprKind::App { callee, args } => self.infer_app(expr.id, expr.span, callee, args),
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
            ExprKind::Record { fields } => self.infer_record(fields, expr.span),
            ExprKind::Spread { base, fields } => self.infer_spread(base, fields),
            ExprKind::Restrict { record, labels } => self.infer_restrict(expr.span, record, labels),
            ExprKind::Field { record, label } => {
                let record_ty = self.infer(record);
                self.cursor = Some(expr.span);
                let field_ty = self.fresh();
                let method = self.fresh();
                if self.dots.callees.contains(&expr.id) || self.dots.takes.contains_key(&expr.id) {
                    self.field_flags.insert(expr.id, method.clone());
                }
                let rest = self.fresh_row();
                let expected = Ty::Record(Row::Extend {
                    label: label.clone(),
                    field: Box::new(field_ty.clone()),
                    method: Box::new(method.clone()),
                    rest: Box::new(rest),
                });
                self.unify(&record_ty, &expected, expr.span);
                if let Some(take) = self.dots.takes.get(&expr.id).cloned() {
                    self.check_take(expr.id, &take, &method, &record_ty);
                }
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
                    method: Box::new(PLAIN),
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
        self.note_first_use(lhs, lhs.span);
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
        } else {
            let ty = self.join_operands(operands);
            self.require(&ty, Kind::Eq, op, expr.span);
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
    fn infer_app(&mut self, id: ExprId, span: Span, callee: &Expr, args: &[Expr]) -> Ty {
        self.note_literal_args(callee, args);
        let before_callee = self.errors.len();
        if self.dots.takes.contains_key(&callee.id) {
            self.take_args = Some((callee.id, args.iter().map(|a| a.span).collect()));
        }
        let callee_ty = self.infer(callee);
        let mut arg_tys: Vec<Ty> = args.iter().map(|a| self.infer(a)).collect();
        self.cursor = Some(span);
        let ret = self.fresh();
        if self.method_takes.contains(&callee.id) {
            return ret;
        }
        if self.errors.len() > before_callee
            && let Some(message) = self.dropped_method_message(id, before_callee)
        {
            self.errors.truncate(before_callee);
            self.errors.push(GoatError::new(span, message));
            return ret;
        }
        if let Some(message) = self.misused_field_message(id, span, callee, args) {
            self.errors.push(GoatError::new(span, message));
            return ret;
        }
        let head = self.resolve_head(&callee_ty);
        if let Ty::Func(params, _) = &head {
            self.widen_arguments(params, &mut arg_tys);
        }
        match head {
            Ty::Func(..) | Ty::Var(_) => {
                let receiver = (self.dots.calls.contains_key(&id) && !arg_tys.is_empty())
                    .then(|| std::mem::replace(&mut arg_tys[0], self.fresh()));
                let hole = receiver.as_ref().map(|_| arg_tys[0].clone());
                let expected = Ty::func(arg_tys, ret.clone());
                let before = self.errors.len();
                self.call = Some(span);
                self.unify_use(callee, &callee_ty, &expected, span);
                self.call = None;
                if let (Some(receiver), Some(hole)) = (receiver, hole)
                    && self.errors.len() == before
                {
                    self.unify(&hole, &receiver, args[0].span);
                }
                if self.errors.len() > before
                    && let Some(message) = self.dot_call_message(id, &head, args, before)
                {
                    self.errors.truncate(before);
                    self.errors.push(GoatError::new(span, message));
                } else if self.errors.len() > before
                    && let ExprKind::Var { symbol, name } = &callee.kind
                    && self.restricted.contains_key(symbol)
                {
                    self.errors.truncate(before);
                    self.errors.push(GoatError::new(
                        span,
                        format!(
                            "`{name}` is a computed value, so it has one type, and this call needs a different one than an earlier use; \
                             write it as a function so it re-specializes per use, like `{name} = program(…) do … done`"
                        ),
                    ));
                }
            }
            // A `(…)` immediately after an expression is read as a call, so
            // calling a non-function is often a sequencing mistake. Reporting
            // lives in a cold helper to keep this frame small.
            other => self.report_not_callable(callee.span, &other),
        }
        ret
    }

    /// The source text of `args`, after the first `skip`, joined by commas.
    fn args_text(&self, args: &[Expr], skip: usize) -> Option<String> {
        let parts: Option<Vec<&str>> = args
            .iter()
            .skip(skip)
            .map(|a| self.dots.source.get(a.span.start..a.span.end))
            .collect();
        Some(parts?.join(", "))
    }

    /// The error for a dot call on a plain function (ADR 0034). A dot call on
    /// a field whose flag is not yet known makes it a method.
    fn misused_field_message(
        &mut self,
        id: ExprId,
        span: Span,
        callee: &Expr,
        args: &[Expr],
    ) -> Option<String> {
        let flag = self.field_flags.get(&callee.id).cloned()?;
        let flag = self.resolve(&flag);
        if let Some(dot) = self.dots.calls.get(&id).cloned() {
            if flag == METHOD {
                return None;
            }
            if flag != PLAIN {
                self.unify_method(&dot.label, &flag, &METHOD, span);
                return None;
            }
            let source = &self.dots.source;
            let receiver = source.get(dot.receiver.start..dot.receiver.end)?;
            let call = source.get(dot.span.start..dot.span.end)?;
            let method = &dot.label;
            let rest = self.args_text(args, 1)?;
            let hint = match self.plain_fns.get(method) {
                Some(names) => names.iter().fold("program(self".to_string(), |text, name| {
                    format!("{text}, {name}")
                }),
                None => "program(self, …".to_string(),
            };
            return Some(format!(
                "`{method}` has no `self`, so `{call}` can't hand it `{receiver}`. \
                 Call it with `{receiver}::{method}({rest})`. \
                 If `{method}` is meant to work on `{receiver}`, make it a method by writing `self` first: `{hint})`."
            ));
        }
        None
    }

    /// `r.f(…)` where `r`'s record has no `f` because the method that made `r`
    /// built a new record instead of starting from `...self`.
    fn dropped_method_message(&self, id: ExprId, before: usize) -> Option<String> {
        let dot = self.dots.calls.get(&id)?;
        let missing = format!("record is missing field `{}`", dot.label);
        self.errors[before..]
            .iter()
            .any(|e| e.message == missing)
            .then_some(())?;
        let inner = self.dots.calls.values().find(|c| c.span == dot.receiver)?;
        let call = self.dots.source.get(dot.receiver.start..dot.receiver.end)?;
        Some(format!(
            "`{call}` gave back a record with no `{}`. If `{}` builds a new record, start it with `...self` so the methods come along.",
            dot.label, inner.label
        ))
    }

    /// The message for a dot call `r.f(…)` whose unification failed, naming
    /// the receiver the dot passed first. `None` leaves the errors from
    /// `before` as they are: a call that is not a dot call, or a type mismatch
    /// that is not about the receiver.
    fn dot_call_message(
        &self,
        id: ExprId,
        head: &Ty,
        args: &[Expr],
        before: usize,
    ) -> Option<String> {
        let dot = self.dots.calls.get(&id)?;
        let source = &self.dots.source;
        let receiver = source.get(dot.receiver.start..dot.receiver.end)?;
        let method = &dot.label;
        let passed = args.len();
        if let Ty::Func(params, _) = head
            && params.len() != passed
        {
            let takes = params.len();
            let again = args
                .get(1)
                .is_some_and(|a| source.get(a.span.start..a.span.end) == Some(receiver));
            return Some(if again && takes + 1 == passed {
                format!(
                    "`{receiver}.{method}({receiver})` already hands `{receiver}` over: the dot does it. \
                     Write `{receiver}.{method}()`."
                )
            } else {
                format!(
                    "`{receiver}.{method}(…)` hands `{receiver}` to `{method}` first, so it passes {}, but `{method}` takes {takes}.",
                    count(passed, "argument"),
                )
            });
        }
        self.errors[before..]
            .iter()
            .any(|e| e.message.contains("contain itself"))
            .then(|| {
                format!(
                    "`{receiver}.{method}(…)` hands `{receiver}` to `{method}`, but then the type of `{method}` would have to contain itself."
                )
            })
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
                while let Row::Extend { field, rest, .. } | Row::Maybe { field, rest, .. } = cursor
                {
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
            self.bind_var(var, Rc::new(Ty::Int));
        }
    }

    /// `r::f` takes a function out of a record; a data field is read with
    /// `r.f`, so there is one way to read it. These errors come first: a call
    /// on the data field fails too, and that is the consequence.
    fn check_takes(&mut self) {
        let mut offenders: Vec<(Span, String)> = Vec::new();
        for (id, take) in &self.dots.takes {
            let Some(ty) = self.node_types.get(id) else {
                continue;
            };
            match self.undecided_as_int(self.resolve(ty).unfold_head()) {
                Ty::Func(..) | Ty::Var(_) => continue,
                _ => {}
            }
            let Some(receiver) = self.dots.source.get(take.receiver.start..take.receiver.end)
            else {
                continue;
            };
            let label = &take.label;
            let message =
                format!("`{label}` isn't a function, so read it with `{receiver}.{label}`");
            offenders.push((take.span, message));
        }
        offenders.sort_by_key(|(span, _)| (span.start, span.end));
        self.errors.splice(
            0..0,
            offenders
                .into_iter()
                .map(|(span, message)| GoatError::new(span, message)),
        );
    }

    /// `r::f` is for a function without `self`, so it settles an open flag as
    /// plain and reports a method, steering to the dot: to `r.f(…)`, or to
    /// `other.f(…)` when the first argument looks meant as the receiver.
    fn check_take(&mut self, id: ExprId, take: &Take, flag: &Ty, record: &Ty) {
        let args = match self.take_args.take() {
            Some((callee, spans)) if callee == id => spans,
            _ => Vec::new(),
        };
        match self.resolve(flag) {
            Ty::Var(v) => {
                self.subst.insert(v, Rc::new(PLAIN));
                return;
            }
            flag if flag != METHOD => return,
            _ => {}
        }
        self.method_takes.insert(id);
        let example = self.plain_function_of(record).map_or_else(
            || "math::double(5)".to_string(),
            |(label, arity)| {
                let receiver = self.dots.source.get(take.receiver.start..take.receiver.end);
                let dots = if arity == 0 { "" } else { "…" };
                format!("{}::{label}({dots})", receiver.unwrap_or("r"))
            },
        );
        let source = &self.dots.source;
        let text = |span: &Span| source.get(span.start..span.end);
        let Some(receiver) = text(&take.receiver) else {
            return;
        };
        let Some(args) = args.iter().map(text).collect::<Option<Vec<&str>>>() else {
            return;
        };
        let label = &take.label;
        let call = match args.split_first() {
            Some((first, rest)) if is_path(first) => {
                format!("{first}.{label}({})", rest.join(", "))
            }
            _ => format!("{receiver}.{label}({})", args.join(", ")),
        };
        self.errors.push(GoatError::new(
            take.span,
            format!(
                "`{label}` has `self`, so call it with a dot: `{call}`. \
                 `::` is for functions without `self`, like `{example}`."
            ),
        ));
    }

    /// A field of `record` that is a function without `self`, by label and
    /// arity, for an example of what `::` is for.
    fn plain_function_of(&self, record: &Ty) -> Option<(String, usize)> {
        let Ty::Record(row) = self.resolve_head(record) else {
            return None;
        };
        let mut next = row;
        loop {
            match next {
                Row::Extend {
                    label,
                    field,
                    method,
                    rest,
                } => {
                    if self.resolve(&method) == PLAIN
                        && let Ty::Func(params, _) = self.resolve_head(&field)
                    {
                        return Some((label, params.len()));
                    }
                    next = *rest;
                }
                Row::Maybe { rest, .. } => next = *rest,
                Row::Empty | Row::Var(_) => return None,
            }
        }
    }

    fn print_ty(&mut self) -> Ty {
        Ty::func(vec![self.fresh()], Ty::Unit)
    }

    /// A record literal. Its methods share one receiver type, `self`: the
    /// record's fields and a row `ρ` for whatever a later extension adds. The
    /// literal is typed like a `letrec` over its fields, so a method that
    /// returns `{...self, …}` returns that same type, and the one recursive
    /// type has one shape however many methods there are (ADR 0034).
    fn infer_record(&mut self, fields: &[(String, Expr)], span: Span) -> Ty {
        for (label, value) in fields {
            if let ExprKind::Func { params, .. } = &value.kind
                && !is_method(value)
            {
                let names = params.iter().map(|p| p.name.clone()).collect();
                self.plain_fns.insert(label.clone(), names);
            }
        }
        if !fields.iter().any(|(_, value)| is_method(value)) {
            let tys: Vec<Ty> = fields.iter().map(|(_, value)| self.infer(value)).collect();
            let row = fields
                .iter()
                .zip(tys)
                .rev()
                .fold(Row::Empty, |rest, ((label, _), field)| Row::Extend {
                    label: label.clone(),
                    field: Box::new(field),
                    method: Box::new(PLAIN),
                    rest: Box::new(rest),
                });
            return Ty::Record(row);
        }
        let flags: Vec<Ty> = fields
            .iter()
            .map(|(_, value)| if is_method(value) { METHOD } else { PLAIN })
            .collect();
        let slots: Vec<Ty> = fields.iter().map(|_| self.fresh()).collect();
        let tail = self.fresh_row();
        let self_row = fields.iter().zip(&slots).zip(&flags).rev().fold(
            tail,
            |rest, (((label, _), slot), flag)| Row::Extend {
                label: label.clone(),
                field: Box::new(slot.clone()),
                method: Box::new(flag.clone()),
                rest: Box::new(rest),
            },
        );
        let receiver = self.fresh_id();
        self.self_defs.insert(receiver, Ty::Record(self_row));
        let mut tys = vec![Ty::Unit; fields.len()];
        for at in inference_order(fields) {
            let (value, slot) = (&fields[at].1, &slots[at]);
            if is_method(value) {
                self.method_self = Some(Ty::Var(receiver));
                tys[at] = self.infer(value);
                self.settle_updater(slot, &tys[at], receiver, value.span);
            } else {
                tys[at] = self.infer(value);
                self.unify(slot, &tys[at], value.span);
            }
        }
        let tied = self.tie_methods(fields, &slots, &flags, &tys, receiver, span);
        let row = fields.iter().zip(&flags).zip(tied).rev().fold(
            Row::Empty,
            |rest, (((label, _), flag), field)| Row::Extend {
                label: label.clone(),
                field: Box::new(field),
                method: Box::new(flag.clone()),
                rest: Box::new(rest),
            },
        );
        Ty::Record(row)
    }

    /// A method that returns its own receiver (`{...self, …}`) has the type
    /// `s -> s`, which no later body can change. Unifying it with its field
    /// right away lets a sibling that calls it, even in a chain, see that the
    /// result is `s` instead of an unknown that each further call wraps in
    /// another layer of record type.
    fn settle_updater(&mut self, slot: &Ty, ty: &Ty, receiver: TypeVar, span: Span) {
        if let Ty::Func(params, ret) = self.resolve(ty)
            && params
                .first()
                .is_some_and(|p| self.resolve(p) == Ty::Var(receiver))
            && self.resolve(&ret) == Ty::Var(receiver)
        {
            self.unify(slot, ty, span);
        }
    }

    /// Settle the receiver of a literal with methods once its bodies are
    /// inferred. Each method's type is unified with its field's variable, with
    /// the receiver kept as the variable `receiver` and any result equal to
    /// the receiver's record written as that variable. The variable is then
    /// bound to `μs. {fields | ρ}`, the record with every `receiver` in it
    /// turned into the binder, so the one recursive type has one shape however
    /// many methods call each other through `self`. Returns the type of each
    /// field of the literal, which mentions the receiver by its variable.
    fn tie_methods(
        &mut self,
        fields: &[(String, Expr)],
        slots: &[Ty],
        flags: &[Ty],
        tys: &[Ty],
        receiver: TypeVar,
        span: Span,
    ) -> Vec<Ty> {
        let def = self.self_defs[&receiver].clone();
        if !self.within_unfold_budget(&def) || tys.iter().any(|ty| !self.within_unfold_budget(ty)) {
            return self.abandon_receiver(receiver, slots, span);
        }
        let record = self.resolve(&def);
        let owns: Vec<Ty> = fields
            .iter()
            .zip(tys)
            .filter(|((_, value), _)| is_method(value))
            .map(|(_, ty)| abstract_receiver(&self.resolve(ty), &record, receiver))
            .collect();
        let methods = fields
            .iter()
            .zip(slots)
            .filter(|((_, value), _)| is_method(value));
        for (((_, value), slot), own) in methods.zip(&owns) {
            self.unify(slot, own, value.span);
        }
        if !self.within_unfold_budget(&def) || slots.iter().any(|ty| !self.within_unfold_budget(ty))
        {
            return self.abandon_receiver(receiver, slots, span);
        }
        let binder = self.fresh_id();
        let Ty::Record(receiver_row) = self.resolve(&def) else {
            unreachable!("a record's receiver is a record")
        };
        let body = fields.iter().zip(flags).zip(slots).rev().fold(
            self.resolve_row(&row_after(&receiver_row, fields.len())),
            |rest, (((label, _), flag), slot)| Row::Extend {
                label: label.clone(),
                field: Box::new(self.resolve(slot)),
                method: Box::new(flag.clone()),
                rest: Box::new(rest),
            },
        );
        let recursive = Ty::Rec(
            binder,
            Box::new(Ty::Record(body).substitute(receiver, &Ty::Var(binder))),
        );
        self.self_defs.remove(&receiver);
        self.bind_var(receiver, Rc::new(recursive));
        slots.to_vec()
    }

    /// Give up on the receiver of a literal whose methods' types have grown
    /// past [`MAX_UNFOLDED_TERMS`] before they could be folded: resolving them
    /// would take longer than the program is worth.
    fn abandon_receiver(&mut self, receiver: TypeVar, slots: &[Ty], span: Span) -> Vec<Ty> {
        self.self_defs.remove(&receiver);
        self.errors.push(GoatError::new(
            span,
            "program too complex: the methods of this record have types larger than the checker handles",
        ));
        slots.to_vec()
    }

    /// `{...base, l: e}` updates a field `base` has, at that field's type, and
    /// adds one it lacks. When `base`'s row is not yet known, `l` is a
    /// presence-variable field in it (there or not, at `e`'s type) and a
    /// present one in the result, so the type is the same either way (ADR 0033).
    fn infer_spread(&mut self, base: &Expr, fields: &[(String, Expr)]) -> Ty {
        let base_ty = self.infer(base);
        let receiver = match &*self.head(&base_ty) {
            Ty::Var(var) if self.self_defs.contains_key(var) => Some(*var),
            _ => None,
        };
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
        let field_tys: Vec<(&str, (Ty, Ty), Span)> = fields
            .iter()
            .map(|(label, value)| {
                let flag = if is_method(value) { METHOD } else { PLAIN };
                (label.as_str(), (self.infer(value), flag), value.span)
            })
            .collect();
        // Resolved after the fields are inferred: reading `base.l` in a field
        // grows `base`'s row with `l`, which the override then updates.
        let copied = match &base.kind {
            ExprKind::Var { name, .. } => Copied::Named(name.clone()),
            _ => Copied::Anonymous,
        };
        let mut row = self.resolve_row(&tail);
        for (label, ty, span) in field_tys {
            row = self.override_field(row, label, ty, span, &copied);
        }
        let copy = Ty::Record(row);
        match receiver {
            Some(var) if self.resolve(&self.self_defs[&var]) == self.resolve(&copy) => Ty::Var(var),
            _ => copy,
        }
    }

    /// `row` with `label` set to a value of type `ty`, a method when `flag` is
    /// [`METHOD`]. An update keeps the field it replaces, flag included.
    fn override_field(
        &mut self,
        row: Row,
        label: &str,
        (ty, flag): (Ty, Ty),
        span: Span,
        copied: &Copied,
    ) -> Row {
        match self.resolve_row(&row) {
            Row::Extend {
                label: l,
                field,
                method,
                rest,
            } => {
                if l == label {
                    self.keep_field_type(label, &field, &ty, span, copied);
                    self.unify_method(label, &method, &flag, span);
                    Row::Extend {
                        label: l,
                        field,
                        method,
                        rest,
                    }
                } else {
                    let rest = self.override_field(*rest, label, (ty, flag), span, copied);
                    Row::Extend {
                        label: l,
                        field,
                        method,
                        rest: Box::new(rest),
                    }
                }
            }
            Row::Maybe {
                label: l,
                pres,
                field,
                method,
                rest,
            } => {
                if l == label {
                    self.keep_field_type(label, &field, &ty, span, copied);
                    self.unify_method(label, &method, &flag, span);
                    Row::Extend {
                        label: l,
                        field,
                        method,
                        rest,
                    }
                } else {
                    let rest = self.override_field(*rest, label, (ty, flag), span, copied);
                    Row::Maybe {
                        label: l,
                        pres,
                        field,
                        method,
                        rest: Box::new(rest),
                    }
                }
            }
            Row::Empty => Row::Extend {
                label: label.to_string(),
                field: Box::new(ty),
                method: Box::new(flag),
                rest: Box::new(Row::Empty),
            },
            Row::Var(v) => {
                let mut banned = self.lacks.get(&v).cloned().unwrap_or_default();
                if !banned.contains(label) {
                    let pres = self.fresh_id();
                    let rest = self.fresh_row();
                    let kinds = self.row_kinds.get(&v).copied().unwrap_or_default();
                    banned.insert(label.to_string());
                    self.lack(&rest, &banned);
                    if let Row::Var(r) = &rest {
                        self.row_kinds.insert(*r, kinds);
                    }
                    // Through unify, not a bare bind: `{...s, next: s}` puts
                    // `s`'s own row variable in the field, which needs a knot.
                    let maybe = Row::Maybe {
                        label: label.to_string(),
                        pres,
                        field: Box::new(ty.clone()),
                        method: Box::new(flag.clone()),
                        rest: Box::new(rest.clone()),
                    };
                    self.unify(&Ty::Record(Row::Var(v)), &Ty::Record(maybe), span);
                    return Row::Extend {
                        label: label.to_string(),
                        field: Box::new(ty),
                        method: Box::new(flag),
                        rest: Box::new(rest),
                    };
                }
                Row::Extend {
                    label: label.to_string(),
                    field: Box::new(ty),
                    method: Box::new(flag),
                    rest: Box::new(Row::Var(v)),
                }
            }
        }
    }

    /// A `...` override gives `label` a value of type `new` where the record
    /// already has it at `old`. A mismatch says so in the kid's terms when both
    /// types are known.
    fn keep_field_type(&mut self, label: &str, old: &Ty, new: &Ty, span: Span, copied: &Copied) {
        let (shown_old, shown_new) = (self.shown(old), self.shown(new));
        let before = self.errors.len();
        self.unify(old, new, span);
        let known = |ty: &Ty| {
            let mut vars = BTreeSet::new();
            ty.free_vars(&mut vars);
            vars.is_empty()
        };
        if self.errors.len() > before && known(&shown_old) && known(&shown_new) {
            self.errors.truncate(before);
            let (in_record, spread_of) = match copied {
                Copied::Named(name) => (format!("`{name}`"), name.as_str()),
                Copied::Anonymous => ("the record being copied".to_string(), "record"),
            };
            self.errors.push(GoatError::new(
                span,
                format!(
                    "`{label}` is a `{shown_old}` in {in_record}, and `{{...{spread_of}, {label}: …}}` keeps each field's type, so `{label}` can't become a `{shown_new}`. To keep the text too, give it its own field, like `{label}_text`."
                ),
            ));
        }
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
                method: Box::new(self.fresh()),
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
                        method: Box::new(self.fresh()),
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
            method: Box::new(PLAIN),
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
            self.row_subst.insert(var, Rc::new(Row::Empty));
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

fn occurs(var: TypeVar, ty: &Ty) -> bool {
    match ty {
        Ty::Var(v) => *v == var,
        Ty::Func(args, ret) => args.iter().any(|a| occurs(var, a)) || occurs(var, ret),
        Ty::Record(row) | Ty::Variant(row) => occurs_row(var, row),
        Ty::Rec(_, body) => occurs(var, body),
        _ => false,
    }
}

/// Where a mention sits, as the cycle through it would see it. A cycle is
/// guarded when it passes through a variant payload, or through both a record
/// field and a function type (parameter or result).
#[derive(Clone, Copy, Default)]
struct Guard {
    tag: bool,
    field: bool,
    func: bool,
}

impl Guard {
    fn tag(self) -> Self {
        Self { tag: true, ..self }
    }
    fn field(self) -> Self {
        Self {
            field: true,
            ..self
        }
    }
    fn func(self) -> Self {
        Self { func: true, ..self }
    }
    fn guarded(self) -> bool {
        self.tag || (self.field && self.func)
    }
}

/// `row`, which sits under the recursive types `bound` (outermost first), with
/// each of their binders replaced by the type it names. A mention under a
/// binder carries that binder in its prefix; unfolding makes it comparable to
/// the same mention outside.
fn unfolded(row: &Row, kind: RowKind, bound: &[&Ty]) -> Row {
    if bound.is_empty() {
        return row.clone();
    }
    let closed = bound.iter().rev().fold(kind.wrap(row.clone()), |ty, rec| {
        let Ty::Rec(binder, _) = rec else { return ty };
        ty.substitute(*binder, rec)
    });
    match closed {
        Ty::Record(row) | Ty::Variant(row) => row,
        _ => unreachable!("substitution keeps the constructor"),
    }
}

/// Whether `ty` is the mention `hole` names, up to unfolding the enclosing
/// recursive types `bound`.
fn is_mention(ty: &Ty, hole: &Hole, bound: &[&Ty]) -> bool {
    match (hole, ty) {
        (Hole::Mention(kind @ RowKind::Record, m), Ty::Record(row))
        | (Hole::Mention(kind @ RowKind::Variant, m), Ty::Variant(row)) => {
            row_shape(row) == row_shape(m) && unfolded(row, *kind, bound) == *m
        }
        _ => false,
    }
}

/// Replace the mentions of `hole` in `ty` with `with`, but only the guarded
/// ones (see [`Guard`]); `at` says where `ty` already sits and `bound` which
/// recursive types enclose it. A mention left behind is a cycle that is not
/// guarded.
fn plug<'a>(ty: &'a Ty, hole: &Hole, with: &Ty, at: Guard, bound: &mut Vec<&'a Ty>) -> Ty {
    if at.guarded()
        && (matches!(ty, Ty::Var(v) if *hole == Hole::Ty(*v)) || is_mention(ty, hole, bound))
    {
        return with.clone();
    }
    match ty {
        Ty::Func(args, ret) => Ty::Func(
            args.iter()
                .map(|a| plug(a, hole, with, at.func(), bound))
                .collect(),
            Box::new(plug(ret, hole, with, at.func(), bound)),
        ),
        Ty::Record(row) => Ty::Record(plug_row(row, hole, with, at.field(), bound)),
        Ty::Variant(row) => Ty::Variant(plug_row(row, hole, with, at.tag(), bound)),
        Ty::Rec(binder, body) => {
            bound.push(ty);
            let body = plug(body, hole, with, at, bound);
            bound.pop();
            Ty::Rec(*binder, Box::new(body))
        }
        other => other.clone(),
    }
}

/// [`plug`] over the fields of a row, which already sit at `at`.
fn plug_row<'a>(row: &'a Row, hole: &Hole, with: &Ty, at: Guard, bound: &mut Vec<&'a Ty>) -> Row {
    match row {
        Row::Extend {
            label,
            field,
            method,
            rest,
        } => Row::Extend {
            label: label.clone(),
            field: Box::new(plug(field, hole, with, at, bound)),
            method: method.clone(),
            rest: Box::new(plug_row(rest, hole, with, at, bound)),
        },
        Row::Maybe {
            label,
            pres,
            field,
            method,
            rest,
        } => Row::Maybe {
            label: label.clone(),
            pres: *pres,
            field: Box::new(plug(field, hole, with, at, bound)),
            method: method.clone(),
            rest: Box::new(plug_row(rest, hole, with, at, bound)),
        },
        other => other.clone(),
    }
}

/// The row, unfolded (see [`unfolded`]), of the first `kind` type at a guarded
/// position whose row ends in the row variable `x`.
fn find_mention<'a>(
    row: &'a Row,
    x: TypeVar,
    kind: RowKind,
    at: Guard,
    bound: &mut Vec<&'a Ty>,
) -> Option<Row> {
    let (Row::Extend { field, rest, .. } | Row::Maybe { field, rest, .. }) = row else {
        return None;
    };
    find_mention_in(field, x, kind, at, bound).or_else(|| find_mention(rest, x, kind, at, bound))
}

fn find_mention_in<'a>(
    ty: &'a Ty,
    x: TypeVar,
    kind: RowKind,
    at: Guard,
    bound: &mut Vec<&'a Ty>,
) -> Option<Row> {
    match ty {
        Ty::Func(args, ret) => args
            .iter()
            .find_map(|t| find_mention_in(t, x, kind, at.func(), bound))
            .or_else(|| find_mention_in(ret, x, kind, at.func(), bound)),
        Ty::Record(row) | Ty::Variant(row) => {
            let is_variant = matches!(ty, Ty::Variant(_));
            if at.guarded()
                && is_variant == (kind == RowKind::Variant)
                && row_shape(row).1 == Some(x)
            {
                return Some(unfolded(row, kind, bound));
            }
            let inner = if is_variant { at.tag() } else { at.field() };
            find_mention(row, x, kind, inner, bound)
        }
        Ty::Rec(_, body) => {
            bound.push(ty);
            let found = find_mention_in(body, x, kind, at, bound);
            bound.pop();
            found
        }
        _ => None,
    }
}

/// `row` with its tail replaced by `tail`.
fn replace_tail(row: &Row, tail: Row) -> Row {
    match row {
        Row::Extend {
            label,
            field,
            method,
            rest,
        } => Row::Extend {
            label: label.clone(),
            field: field.clone(),
            method: method.clone(),
            rest: Box::new(replace_tail(rest, tail)),
        },
        Row::Maybe {
            label,
            pres,
            field,
            method,
            rest,
        } => Row::Maybe {
            label: label.clone(),
            pres: *pres,
            field: field.clone(),
            method: method.clone(),
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
            Row::Extend { label, rest, .. } | Row::Maybe { label, rest, .. } => {
                labels.push(label.clone());
                cursor = rest;
            }
            Row::Var(v) => return (labels, Some(*v)),
            Row::Empty => return (labels, None),
        }
    }
}

/// `ty` with every part equal to the record type `receiver` replaced by the
/// variable `binder`.
fn abstract_receiver(ty: &Ty, receiver: &Ty, binder: TypeVar) -> Ty {
    if ty == receiver {
        Ty::Var(binder)
    } else {
        ty.map_children(&|part| abstract_receiver(part, receiver, binder))
    }
}

/// `row` without its first `n` fields.
fn row_after(row: &Row, n: usize) -> Row {
    match row {
        Row::Extend { rest, .. } | Row::Maybe { rest, .. } if n > 0 => row_after(rest, n - 1),
        other => other.clone(),
    }
}

fn field_of<'a>(row: &'a Row, label: &str) -> Option<&'a Ty> {
    match row {
        Row::Extend {
            label: l,
            field,
            rest,
            ..
        } => {
            if l == label {
                Some(field)
            } else {
                field_of(rest, label)
            }
        }
        Row::Maybe {
            label: l,
            field,
            rest,
            ..
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

/// What a spread copies, for the message when it would change a field's type.
enum Copied {
    Named(String),
    Anonymous,
}

fn count(n: usize, noun: &str) -> String {
    format!("{n} {noun}{}", if n == 1 { "" } else { "s" })
}

fn occurs_row(var: TypeVar, row: &Row) -> bool {
    match row {
        Row::Empty => false,
        Row::Var(v) => *v == var,
        Row::Extend { field, rest, .. } | Row::Maybe { field, rest, .. } => {
            occurs(var, field) || occurs_row(var, rest)
        }
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
        Row::Extend {
            label,
            field,
            method,
            rest,
        } => Row::Extend {
            label: label.clone(),
            field: Box::new(subst_vars(field, mapping)),
            method: Box::new(subst_vars(method, mapping)),
            rest: Box::new(subst_row(rest, mapping)),
        },
        Row::Maybe {
            label,
            pres,
            field,
            method,
            rest,
        } => Row::Maybe {
            label: label.clone(),
            pres: mapping.get(pres).copied().unwrap_or(*pres),
            field: Box::new(subst_vars(field, mapping)),
            method: Box::new(subst_vars(method, mapping)),
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
            method: Box::new(PLAIN),
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
    fn a_cycle_route_deeper_than_a_type_may_nest_is_left_out() {
        let mut ty = Ty::Var(1);
        for _ in 0..=MAX_UNFOLDED_DEPTH {
            ty = Ty::Func(vec![ty], Box::new(Ty::Unit));
        }
        assert!(cycle_route(1, &ty).is_empty());
        let shallow = Ty::Func(vec![Ty::Var(1)], Box::new(Ty::Unit));
        assert_eq!(cycle_route(1, &shallow), ["its argument"]);
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
        assert_eq!(inf.assumed.len, 0);
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
            assert!(inf.errors[0].message.contains("contain itself"), "{ty}");
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
            assert!(inf.errors[0].message.contains("contain itself"));
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
        inf.subst.insert(1, Rc::new(Ty::Int));
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
        assert_eq!(inf.errors[0].message, "can't compare functions");
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
