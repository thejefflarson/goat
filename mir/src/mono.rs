//! Monomorphization: checked HIR to ground-typed MIR, one `Func` per
//! `(binding, ground type)` specialization.

use crate::canon::{canonical, ground_fields, layout_fields};
use crate::mir::*;
use crate::rc::insert_rc;
use goat_checker::captures::{for_each_node, push_children};
use goat_checker::hir::{
    self, BinOp, Boundary, Builtin, ExprId, ExprKind, Param, PatternPayload, Span, Symbol,
};
use goat_checker::infer::Typed;
use goat_checker::ty::{Row, Ty, TypeVar};
use goat_checker::vocab::KEY_TAGS;
use goat_checker::{Checked, GoatError, Target};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

mod interactive;
mod structural;

type Subst = HashMap<TypeVar, Ty>;

// Caps the number of function specializations so a pathologically polymorphic
// but well-typed program cannot cause exponential monomorphization work.
const MAX_SPECS: usize = 50_000;

/// Lower a checked program to MIR and insert its reference counting.
/// Constructs whose runtime support has not landed yet (ADR 0005) come back as
/// spanned diagnostics; well-typed input never panics.
pub fn mono(checked: &Checked) -> Result<Program, Vec<GoatError>> {
    mono_for(checked, Profile::Desktop)
}

/// Like [`mono`], for the number widths of `profile`. An `Int` literal the
/// profile cannot hold becomes a runtime trap, the one an overflowing
/// operation takes (ADR 0017).
pub fn mono_for(checked: &Checked, profile: Profile) -> Result<Program, Vec<GoatError>> {
    let (lambdas, var_tys) = collect_lambdas(&checked.typed, &checked.root, &checked.captures);
    let mut labels = BTreeSet::new();
    collect_tags(&checked.root, &mut labels);
    if checked.interactive.is_some() {
        labels.extend(KEY_TAGS.map(String::from));
    }
    let mut foreign = HashMap::new();
    collect_foreign(&checked.root, &mut foreign);
    let mut m = Mono {
        profile,
        typed: &checked.typed,
        lambdas,
        var_tys,
        foreign,
        imports: Vec::new(),
        foreign_fns: HashMap::new(),
        specs: HashMap::new(),
        out: vec![None],
        work: Vec::new(),
        sigs: Vec::new(),
        layouts: Vec::new(),
        variants: HashMap::new(),
        families: Vec::new(),
        tags: labels.into_iter().zip(0..).collect(),
        wrappers: HashMap::new(),
        derived: HashMap::new(),
        errors: Vec::new(),
        data: Vec::new(),
    };

    let mut cx = FnCx::new(Subst::new());
    let root_ty = m.ground(&checked.typed.root_ty, &cx.subst);
    let ret = m.lower_ty(&root_ty);
    // A pointer root is dropped after it is computed (see `rc::insert_rc`), so
    // it cannot end in a tail call; a string root is handed to the host.
    let body = m.expr(&mut cx, &checked.root, !ret.is_discarded_root());
    m.out[0] = Some(cx.into_func(vec![], None, ret, body));
    let interactive = checked
        .interactive
        .is_some()
        .then(|| m.interactive(&root_ty));

    let mut step = 0usize;
    while let Some((id, target, subst, capture_tys)) = m.work.pop() {
        step += 1;
        if step > MAX_SPECS {
            m.errors.push(GoatError::new(Span::new(0, 0), "program too complex".to_string()));
            break;
        }
        let func = m.specialize_body(target, subst, capture_tys);
        m.out[id.0 as usize] = Some(func);
    }

    if !m.errors.is_empty() {
        let mut seen = Vec::new();
        m.errors.retain(|e| {
            let fresh = !seen.contains(e);
            if fresh {
                seen.push(e.clone());
            }
            fresh
        });
        return Err(m.errors);
    }

    let mut program = Program {
        profile,
        funcs: m
            .out
            .into_iter()
            .map(|f| f.expect("func lowered"))
            .collect(),
        entry: FuncId(0),
        layouts: m.layouts,
        sigs: m.sigs,
        data: m.data,
        foreign: m.imports,
        interactive,
    };
    insert_rc(&mut program);
    Ok(program)
}

/// Every tag label in the program, constructed or matched.
fn collect_tags(root: &hir::Expr, out: &mut BTreeSet<String>) {
    for_each_node(root, &mut |e| match &e.kind {
        ExprKind::Tag { name, .. } => {
            out.insert(name.clone());
        }
        ExprKind::Match { arms, .. } => {
            out.extend(arms.iter().map(|a| a.pattern.tag.clone()));
        }
        _ => {}
    });
}

/// The host function each `foreign` binding names.
fn collect_foreign(root: &hir::Expr, out: &mut HashMap<Symbol, ForeignFn>) {
    for_each_node(root, &mut |e| {
        if let ExprKind::Let { symbol, value, .. } = &e.kind
            && let ExprKind::Foreign {
                module,
                name,
                params,
                ret,
            } = &value.kind
        {
            out.insert(
                *symbol,
                ForeignFn {
                    module: module.clone(),
                    name: name.clone(),
                    params: params.iter().map(|&b| boundary_ty(b)).collect(),
                    ret: boundary_ty(*ret),
                },
            );
        }
    });
}

/// `e`, of type `ty`, as the `Float` nearest it: the one place an `Int`
/// widens.
fn widen(e: Expr, ty: &Ty) -> Expr {
    match (e, ty) {
        (Expr::Const(Const::Int(n)), _) => Expr::Const(Const::Float(n as f64)),
        (e, Ty::Int) => Expr::IntToFloat(Box::new(e)),
        (e, _) => e,
    }
}

fn boundary_ty(b: Boundary) -> MTy {
    match b {
        Boundary::Number => MTy::Float,
        Boundary::Int => MTy::Int,
        Boundary::Bool => MTy::Bool,
        Boundary::Unit => MTy::Unit,
        Boundary::Str => MTy::Ptr(HeapKind::Str),
    }
}

#[derive(Clone)]
struct Lambda<'a> {
    params: &'a [Param],
    body: &'a hir::Expr,
    /// The literal's type, in terms of the type variables its body is checked
    /// against.
    ty: &'a Ty,
    /// The enclosing variables the closure holds, in `Capture` index order.
    /// Function bindings are never captured: each use re-materializes them.
    captures: Vec<Symbol>,
}

struct Collector<'a> {
    typed: &'a Typed,
    captures: &'a HashMap<Target, Vec<Symbol>>,
    lambdas: HashMap<Target, Lambda<'a>>,
    var_tys: HashMap<Symbol, &'a Ty>,
}

/// Find every function literal, its captures, and the type template of every
/// variable a closure might capture.
fn collect_lambdas<'a>(
    typed: &'a Typed,
    root: &'a hir::Expr,
    captures: &'a HashMap<Target, Vec<Symbol>>,
) -> (HashMap<Target, Lambda<'a>>, HashMap<Symbol, &'a Ty>) {
    let mut c = Collector {
        typed,
        captures,
        lambdas: HashMap::new(),
        var_tys: HashMap::new(),
    };
    c.walk(root);
    (c.lambdas, c.var_tys)
}

impl<'a> Collector<'a> {
    fn walk(&mut self, root: &'a hir::Expr) {
        let typed = self.typed;
        let mut pending = vec![root];
        while let Some(e) = pending.pop() {
            match &e.kind {
                ExprKind::Let {
                    symbol,
                    value,
                    rest,
                    ..
                } => {
                    pending.extend(rest.as_deref());
                    match &value.kind {
                        ExprKind::Func { params, body } => {
                            let ty = &typed.schemes[symbol].ty;
                            self.lambda(Target::Named(*symbol), ty, params, body);
                        }
                        _ => {
                            self.var_tys.insert(*symbol, &typed.node_types[&value.id]);
                            pending.push(value);
                        }
                    }
                }
                ExprKind::Func { params, body } => {
                    self.lambda(Target::Anon(e.id), &typed.node_types[&e.id], params, body);
                }
                ExprKind::Match { arms, .. } => {
                    for binder in arms.iter().flat_map(|a| a.pattern.payload.binders()) {
                        self.var_tys
                            .insert(binder.symbol, &typed.binder_types[&binder.symbol]);
                    }
                    push_children(e, &mut pending);
                }
                _ => push_children(e, &mut pending),
            }
        }
    }

    fn lambda(&mut self, target: Target, ty: &'a Ty, params: &'a [Param], body: &'a hir::Expr) {
        if let Ty::Func(args, _) = ty {
            for (param, ty) in params.iter().zip(args) {
                self.var_tys.insert(param.symbol, ty);
            }
        }
        self.lambdas.insert(
            target,
            Lambda {
                params,
                body,
                ty,
                captures: self.captures[&target].clone(),
            },
        );
        self.walk(body);
    }
}

/// The first expression in `e` that refers to `symbol`.
fn first_use(root: &hir::Expr, symbol: Symbol) -> Option<ExprId> {
    let mut found = None;
    for_each_node(root, &mut |e| {
        if found.is_none() && matches!(&e.kind, ExprKind::Var { symbol: s, .. } if *s == symbol) {
            found = Some(e.id);
        }
    });
    found
}

/// One specialization of a function literal: its use type and the ground types
/// of its captures fix the body.
/// A function literal at one instantiation: its target, its type at the use,
/// and the types of its captured variables.
type SpecKey = (Target, Ty, Vec<Ty>);

/// The most specialized functions one program may need. Specialization is
/// exponential in the program: a chain of generic functions that each call the
/// next at two different types needs a copy per type path, from types of
/// constant size, so no checker-side size bound reaches it.
const MAX_SPECIALIZATIONS: usize = 1 << 14;

struct Mono<'a> {
    profile: Profile,
    typed: &'a Typed,
    lambdas: HashMap<Target, Lambda<'a>>,
    var_tys: HashMap<Symbol, &'a Ty>,
    /// The host function of each `foreign` binding.
    foreign: HashMap<Symbol, ForeignFn>,
    /// The host functions the program uses, which become its imports. A
    /// declaration nothing uses is not here.
    imports: Vec<ForeignFn>,
    /// The function that calls a foreign binding with its own parameters, for
    /// one used as a value.
    foreign_fns: HashMap<Symbol, FuncId>,
    specs: HashMap<SpecKey, FuncId>,
    out: Vec<Option<Func>>,
    work: Vec<(FuncId, Target, Subst, Vec<Ty>)>,
    sigs: Vec<Sig>,
    layouts: Vec<Layout>,
    /// The layout of each variant type, keyed by its canonical form. Types in
    /// one `Family` share an id. A recursive layout names itself, so a type is
    /// registered here before its payloads are lowered: reaching it again finds
    /// the id instead of lowering it forever.
    variants: HashMap<Ty, LayoutId>,
    families: Vec<Family>,
    /// The global tag number of each label, in sorted label order.
    tags: HashMap<String, u32>,
    /// The zero-capture closure wrapper for each function used as a value. The
    /// wrappers are the funcref-table members: the functions with an `env`.
    wrappers: HashMap<FuncId, FuncId>,
    /// The equality, printing and arithmetic functions derived from types.
    derived: HashMap<(structural::Derived, Ty), FuncId>,
    errors: Vec<GoatError>,
    data: Vec<Vec<u8>>,
}

/// The variant types that share one layout. A layout is a table from the global
/// tag number to payload slots, and every use of a value must see the same
/// table, so a value matched at two widths (`[A]` and `[A, B]`) needs both
/// types in one family. The layout is the union of the members' tags. That is
/// width-independent because a cell is sized and dispatched by its stored tag,
/// and sound because members agree on every tag they share: the checker's row
/// unification guarantees it for the types of one value, and `Mono::agrees`
/// enforces it before a type joins.
struct Family {
    layout: LayoutId,
    /// The payload type of each tag some member has, from its first provider.
    payloads: HashMap<String, Ty>,
}

/// Variant types assumed to join a family while `Mono::agrees` checks them: a
/// recursive type is compared against a family with itself assumed in it.
type Assumed = Vec<(Ty, LayoutId)>;

struct FnCx {
    subst: Subst,
    locals: HashMap<Symbol, Local>,
    /// The `Capture` index of each captured variable.
    captures: HashMap<Symbol, usize>,
    /// A capturing function's own name and `env`; the name refers to the
    /// closure being run, never to a stored capture.
    self_env: Option<(Symbol, Local)>,
    next: u32,
    tys: BTreeMap<Local, MTy>,
}

impl FnCx {
    fn new(subst: Subst) -> FnCx {
        FnCx {
            subst,
            locals: HashMap::new(),
            captures: HashMap::new(),
            self_env: None,
            next: 0,
            tys: BTreeMap::new(),
        }
    }

    fn fresh(&mut self, ty: MTy) -> Local {
        self.next += 1;
        let local = Local(self.next - 1);
        self.tys.insert(local, ty);
        local
    }

    fn into_func(self, params: Vec<(Local, MTy)>, env: Option<Env>, ret: MTy, body: Expr) -> Func {
        Func {
            params,
            env,
            ret,
            body,
            locals: self.tys,
        }
    }
}

impl Mono<'_> {
    /// Apply `subst`, defaulting unconstrained type variables to `Unit` and
    /// row variables to the empty row. The result is canonical (see
    /// `canon::canonical`), so equal types are `==` and safe to key on.
    fn ground(&self, ty: &Ty, subst: &Subst) -> Ty {
        canonical(&self.ground_in(ty, subst, &mut Vec::new()))
    }

    /// `bound` holds the `μ` binders enclosing `ty`; they are not in `subst`
    /// and stay as variables.
    fn ground_in(&self, ty: &Ty, subst: &Subst, bound: &mut Vec<TypeVar>) -> Ty {
        match ty {
            Ty::Var(v) if bound.contains(v) => ty.clone(),
            Ty::Var(v) => subst.get(v).cloned().unwrap_or_else(|| {
                if self.typed.number_vars.contains(v) {
                    Ty::Int
                } else {
                    Ty::Unit
                }
            }),
            Ty::Func(args, ret) => Ty::Func(
                args.iter()
                    .map(|a| self.ground_in(a, subst, bound))
                    .collect(),
                Box::new(self.ground_in(ret, subst, bound)),
            ),
            Ty::Record(row) => Ty::Record(self.ground_row(row, subst, bound)),
            Ty::Variant(row) => Ty::Variant(self.ground_row(row, subst, bound)),
            Ty::Rec(binder, body) => {
                bound.push(*binder);
                let body = self.ground_in(body, subst, bound);
                bound.pop();
                Ty::Rec(*binder, Box::new(body))
            }
            other => other.clone(),
        }
    }

    /// Ground `row` into a closed row with its fields stably sorted by label,
    /// the order of its layout slots.
    fn ground_row(&self, row: &Row, subst: &Subst, bound: &mut Vec<TypeVar>) -> Row {
        let mut fields = Vec::new();
        self.flatten_row(row, subst, bound, &mut fields);
        fields.sort_by(|a, b| a.0.cmp(&b.0));
        fields
            .into_iter()
            .rev()
            .fold(Row::Empty, |rest, (label, field)| Row::Extend {
                label,
                field: Box::new(field),
                rest: Box::new(rest),
            })
    }

    fn flatten_row(
        &self,
        row: &Row,
        subst: &Subst,
        bound: &mut Vec<TypeVar>,
        out: &mut Vec<(String, Ty)>,
    ) {
        match row {
            Row::Empty => {}
            Row::Var(v) => {
                if let Some(Ty::Record(tail) | Ty::Variant(tail)) = subst.get(v) {
                    self.flatten_row(tail, subst, bound, out);
                }
            }
            Row::Extend { label, field, rest } => {
                out.push((label.clone(), self.ground_in(field, subst, bound)));
                self.flatten_row(rest, subst, bound, out);
            }
        }
    }

    fn intern(&mut self, s: &str) -> DataId {
        let bytes = s.as_bytes();
        let index = self
            .data
            .iter()
            .position(|d| d == bytes)
            .unwrap_or_else(|| {
                self.data.push(bytes.to_vec());
                self.data.len() - 1
            });
        DataId(index as u32)
    }

    fn lower_ty(&mut self, ty: &Ty) -> MTy {
        match ty {
            Ty::Int => MTy::Int,
            Ty::Float => MTy::Float,
            Ty::Bool => MTy::Bool,
            Ty::Unit => MTy::Unit,
            Ty::Func(args, ret) => {
                let sig = Sig {
                    params: args.iter().map(|a| self.lower_ty(a)).collect(),
                    ret: self.lower_ty(ret),
                };
                let id = self.sigs.iter().position(|s| *s == sig).unwrap_or_else(|| {
                    self.sigs.push(sig);
                    self.sigs.len() - 1
                });
                MTy::Ptr(HeapKind::Closure(SigId(id as u32)))
            }
            Ty::Record(row) => {
                let mut fields = Vec::new();
                for (_, field) in layout_fields(row) {
                    fields.push(self.lower_ty(field));
                }
                let layout = Layout::Record(fields);
                let id = self
                    .layouts
                    .iter()
                    .position(|l| *l == layout)
                    .unwrap_or_else(|| {
                        self.layouts.push(layout);
                        self.layouts.len() - 1
                    });
                MTy::Ptr(HeapKind::Record(LayoutId(id as u32)))
            }
            Ty::Str => MTy::Ptr(HeapKind::Str),
            Ty::Variant(_) => MTy::Ptr(HeapKind::Variant(self.variant_layout(canonical(ty)))),
            Ty::Rec(..) => match ty.unfold_head() {
                Ty::Variant(_) => MTy::Ptr(HeapKind::Variant(self.variant_layout(canonical(ty)))),
                // A `μ` over a record or function: the cycle still passes
                // through a variant, which cuts it.
                Ty::Rec(..) => MTy::Unit,
                head => self.lower_ty(&head),
            },
            Ty::Var(_) => unreachable!("type variable survived grounding"),
        }
    }

    /// The layout of the variant type `key` (canonical): that of the first
    /// family whose tags it agrees with, else a new one. Registered before its
    /// payloads are lowered, so a payload that mentions `key` again resolves to
    /// this id; every cycle in a type crosses a variant, so lowering ends.
    fn variant_layout(&mut self, key: Ty) -> LayoutId {
        if let Some(&id) = self.variants.get(&key) {
            return id;
        }
        let mut joined = None;
        for family in &self.families {
            let mut assumed = vec![(key.clone(), family.layout)];
            if self.agrees(&key, family, &mut assumed) {
                joined = Some(assumed);
                break;
            }
        }
        let members = joined.unwrap_or_else(|| {
            let id = LayoutId(self.layouts.len() as u32);
            self.layouts.push(Layout::Variant(BTreeMap::new()));
            self.families.push(Family {
                layout: id,
                payloads: HashMap::new(),
            });
            vec![(key.clone(), id)]
        });
        self.variants.extend(members.iter().cloned());
        for (member, id) in &members {
            let row = variant_row(member);
            let family = self
                .families
                .iter_mut()
                .find(|f| f.layout == *id)
                .expect("layout belongs to a family");
            for (label, payload) in ground_fields(&row) {
                family
                    .payloads
                    .entry(label.clone())
                    .or_insert_with(|| payload.clone());
            }
        }
        for (member, id) in &members {
            let row = variant_row(member);
            for (label, payload) in ground_fields(&row) {
                let fields = payload_fields(payload)
                    .iter()
                    .map(|t| self.lower_ty(t))
                    .collect();
                let Layout::Variant(table) = &mut self.layouts[id.0 as usize] else {
                    unreachable!("a family's layout is a variant");
                };
                table.insert(self.tags[label], fields);
            }
        }
        self.variants[&key]
    }

    /// Whether the variant type `key` can join `family`: it shares a tag with
    /// the family, and every tag it shares has a compatible payload. Two uses
    /// of one value always share the value's own tag, so types with nothing in
    /// common stay apart. Nested variant types that must join a family for that
    /// to hold are added to `assumed`.
    fn agrees(&self, key: &Ty, family: &Family, assumed: &mut Assumed) -> bool {
        let row = variant_row(key);
        let mut shared = false;
        let agree = ground_fields(&row).all(|(label, payload)| {
            family.payloads.get(label).is_none_or(|have| {
                shared = true;
                self.compatible(payload, have, assumed)
            })
        });
        agree && shared
    }

    /// Whether two payload types lower to the same slots once the variants
    /// inside them are compared by family instead of by width. A variant not
    /// yet lowered is assumed to join the family of the one it is compared to.
    fn compatible(&self, a: &Ty, b: &Ty, assumed: &mut Assumed) -> bool {
        if a == b {
            return true;
        }
        match (a.unfold_head(), b.unfold_head()) {
            (a @ Ty::Variant(_), b @ Ty::Variant(_)) => {
                let (a, b) = (canonical(&a), canonical(&b));
                let family_of = |ty: &Ty, assumed: &Assumed| {
                    assumed
                        .iter()
                        .find(|(t, _)| t == ty)
                        .map(|(_, id)| *id)
                        .or_else(|| self.variants.get(ty).copied())
                };
                match (family_of(&a, assumed), family_of(&b, assumed)) {
                    (Some(x), Some(y)) => x == y,
                    (None, Some(y)) => {
                        assumed.push((a.clone(), y));
                        self.families
                            .iter()
                            .find(|f| f.layout == y)
                            .is_some_and(|f| self.agrees(&a, f, assumed))
                    }
                    _ => false,
                }
            }
            (Ty::Record(a), Ty::Record(b)) => {
                let a: Vec<_> = ground_fields(&a).collect();
                let b: Vec<_> = ground_fields(&b).collect();
                a.len() == b.len()
                    && a.iter()
                        .zip(&b)
                        .all(|((la, ta), (lb, tb))| la == lb && self.compatible(ta, tb, assumed))
            }
            (Ty::Func(pa, ra), Ty::Func(pb, rb)) => {
                pa.len() == pb.len()
                    && pa
                        .iter()
                        .zip(&pb)
                        .all(|(a, b)| self.compatible(a, b, assumed))
                    && self.compatible(&ra, &rb, assumed)
            }
            (a, b) => a == b,
        }
    }

    fn specialize(&mut self, cx: &FnCx, target: Target, site: &hir::Expr) -> (FuncId, Ty) {
        let use_ty = self.ground(&self.typed.node_types[&site.id], &cx.subst);
        let Lambda { ty, captures, .. } = self.lambdas[&target].clone();
        let capture_tys: Vec<Ty> = captures
            .iter()
            .map(|c| self.ground(self.var_tys[c], &cx.subst))
            .collect();
        let key = (target, use_ty, capture_tys);
        if let Some(&id) = self.specs.get(&key) {
            return (id, key.1);
        }
        if self.specs.len() >= MAX_SPECIALIZATIONS {
            if self.errors.is_empty() {
                self.errors.push(GoatError::new(
                    site.span,
                    "program too complex: it needs too many specialized functions",
                ));
            }
            // The program is rejected, so the placeholder is never emitted.
            return (FuncId(0), key.1);
        }
        let (_, use_ty, capture_tys) = &key;
        let id = FuncId(self.out.len() as u32);
        self.out.push(None);

        // The body also mentions the enclosing scope's type variables; the
        // captured variables' ground types recover them.
        let mut subst = Subst::new();
        match_ty(ty, use_ty, &mut subst);
        for (c, capture_ty) in captures.iter().zip(capture_tys) {
            match_ty(self.var_tys[c], capture_ty, &mut subst);
        }
        self.work.push((id, target, subst, capture_tys.clone()));
        let use_ty = use_ty.clone();
        self.specs.insert(key, id);
        (id, use_ty)
    }

    /// The closure value of `target` at a use site: a static closure when it
    /// captures nothing, else a fresh heap closure over the captured variables.
    fn closure_value(&mut self, cx: &mut FnCx, target: Target, site: &hir::Expr) -> Expr {
        let (id, ty) = self.specialize(cx, target, site);
        let captures = self.lambdas[&target].captures.clone();
        if captures.is_empty() {
            return self.closure_of(id, &ty);
        }
        let values = captures
            .into_iter()
            .map(|c| self.variable_value(cx, c))
            .collect();
        Expr::MakeClosure(id, values)
    }

    /// A captured or local variable's value.
    fn variable_value(&mut self, cx: &mut FnCx, symbol: Symbol) -> Expr {
        if let Some(&local) = cx.locals.get(&symbol) {
            return Expr::Local(local);
        }
        if let Some(&index) = cx.captures.get(&symbol) {
            return Expr::Capture(index);
        }
        unreachable!("the checker rejects a use of a function before its captures are bound")
    }

    /// A zero-capture closure over `target`: a wrapper that takes the closure
    /// as `env` and tail-calls `target`.
    fn closure_of(&mut self, target: FuncId, ty: &Ty) -> Expr {
        let wrapper = match self.wrappers.get(&target) {
            Some(&w) => w,
            None => {
                let MTy::Ptr(HeapKind::Closure(sig)) = self.lower_ty(ty) else {
                    unreachable!("function type lowers to a closure");
                };
                let Sig { params, ret } = self.sigs[sig.0 as usize].clone();
                let env = Local(params.len() as u32);
                let locals: Vec<_> = (0..params.len() as u32).map(Local).collect();
                let body = Expr::TailCall(
                    Callee::Direct(target),
                    locals.iter().map(|l| Expr::Local(*l)).collect(),
                );
                let id = FuncId(self.out.len() as u32);
                self.out.push(Some(Func {
                    params: locals.into_iter().zip(params).collect(),
                    env: Some(Env {
                        local: env,
                        sig,
                        captures: Vec::new(),
                    }),
                    ret,
                    body,
                    locals: BTreeMap::new(),
                }));
                self.wrappers.insert(target, id);
                id
            }
        };
        Expr::MakeClosure(wrapper, Vec::new())
    }

    fn specialize_body(&mut self, target: Target, subst: Subst, capture_tys: Vec<Ty>) -> Func {
        let Lambda {
            params,
            body,
            ty,
            captures,
        } = self.lambdas[&target].clone();
        let Ty::Func(arg_tys, ret_ty) = ty else {
            unreachable!("function literal without a function type");
        };
        let mut cx = FnCx::new(subst);
        let mut mparams = Vec::new();
        for (param, ty) in params.iter().zip(arg_tys) {
            let ty = self.ground(ty, &cx.subst);
            let mty = self.lower_ty(&ty);
            let local = cx.fresh(mty);
            cx.locals.insert(param.symbol, local);
            mparams.push((local, mty));
        }
        let ret = self.ground(ret_ty, &cx.subst);
        let env = if captures.is_empty() {
            None
        } else {
            Some(self.bind_env(&mut cx, target, ty, &captures, &capture_tys))
        };
        let ret = self.lower_ty(&ret);
        let body = self.expr(&mut cx, body, true);
        cx.into_func(mparams, env, ret, body)
    }

    /// Give a capturing function its `env` parameter.
    fn bind_env(
        &mut self,
        cx: &mut FnCx,
        target: Target,
        ty: &Ty,
        captures: &[Symbol],
        capture_tys: &[Ty],
    ) -> Env {
        let ty = self.ground(ty, &cx.subst);
        let MTy::Ptr(HeapKind::Closure(sig)) = self.lower_ty(&ty) else {
            unreachable!("function type lowers to a closure");
        };
        let local = cx.fresh(MTy::Ptr(HeapKind::Closure(sig)));
        cx.captures = captures.iter().copied().zip(0..).collect();
        if let Target::Named(symbol) = target {
            cx.self_env = Some((symbol, local));
        }
        Env {
            local,
            sig,
            captures: capture_tys.iter().map(|t| self.lower_ty(t)).collect(),
        }
    }

    /// Pin the type variables a value binding generalizes over (`m = mk(2)`
    /// is polymorphic in whatever `mk` leaves open) to the instantiation its
    /// first use in `rest` picks. The binding is evaluated once, so its value,
    /// and the type of any closure capturing it, must be lowered at that
    /// type; defaulting the variables to `Unit` would disagree with the use.
    fn instantiate_binding(&self, cx: &mut FnCx, symbol: Symbol, rest: &hir::Expr) {
        let Some(scheme) = self
            .typed
            .schemes
            .get(&symbol)
            .filter(|s| !s.vars.is_empty())
        else {
            return;
        };
        let Some(first_use) = first_use(rest, symbol) else {
            return;
        };
        let use_ty = self.ground(&self.typed.node_types[&first_use], &cx.subst);
        let mut found = Subst::new();
        match_ty(&scheme.ty, &use_ty, &mut found);
        for v in &scheme.vars {
            if let Some(ty) = found.remove(v) {
                cx.subst.entry(*v).or_insert(ty);
            }
        }
    }

    /// The import for the foreign binding `symbol`, registered on first use.
    fn import(&mut self, symbol: Symbol) -> ForeignId {
        let foreign = self.foreign[&symbol].clone();
        self.register_import(foreign)
    }

    fn register_import(&mut self, foreign: ForeignFn) -> ForeignId {
        let index = match self.imports.iter().position(|i| *i == foreign) {
            Some(index) => index,
            None => {
                self.imports.push(foreign);
                self.imports.len() - 1
            }
        };
        ForeignId(index as u32)
    }

    /// A foreign function used as a value: a closure over a function that
    /// forwards its parameters to the import.
    #[inline(never)]
    fn foreign_value(&mut self, cx: &FnCx, symbol: Symbol, use_id: ExprId) -> Expr {
        let target = match self.foreign_fns.get(&symbol) {
            Some(&f) => f,
            None => {
                let foreign = self.foreign[&symbol].clone();
                let locals: Vec<Local> = (0..foreign.params.len() as u32).map(Local).collect();
                let body = match foreign.intrinsic() {
                    Some(function) => Expr::FloatFn(function, Box::new(Expr::Local(Local(0)))),
                    None => Expr::CallForeign(self.import(symbol), locals.clone()),
                };
                let id = FuncId(self.out.len() as u32);
                self.out.push(Some(Func {
                    params: locals.into_iter().zip(foreign.params).collect(),
                    env: None,
                    ret: foreign.ret,
                    body,
                    locals: BTreeMap::new(),
                }));
                self.foreign_fns.insert(symbol, id);
                id
            }
        };
        let ty = self.ground(&self.typed.node_types[&use_id], &cx.subst);
        self.closure_of(target, &ty)
    }

    /// `import(args)`, or the compiler's own `math` function. Each argument is
    /// bound to a local, in order, because the call borrows its pointers (see
    /// `Expr::CallForeign`); an `Int` argument to a `Float` parameter widens.
    #[inline(never)]
    fn foreign_call(&mut self, cx: &mut FnCx, symbol: Symbol, args: &[hir::Expr]) -> Expr {
        let foreign = self.foreign[&symbol].clone();
        if let Some(function) = foreign.intrinsic()
            && let [arg] = args
        {
            let value = self.argument(cx, arg, true);
            return Expr::FloatFn(function, Box::new(value));
        }
        let bound: Vec<(Local, Expr)> = args
            .iter()
            .zip(foreign.params)
            .map(|(a, ty)| (cx.fresh(ty), self.argument(cx, a, ty == MTy::Float)))
            .collect();
        let call = Expr::CallForeign(self.import(symbol), bound.iter().map(|(l, _)| *l).collect());
        bound.into_iter().rev().fold(call, |body, (l, value)| {
            Expr::Let(l, Box::new(value), Box::new(body))
        })
    }

    /// `arg` lowered, widened when the parameter it is passed to is a `Float`.
    #[inline(never)]
    fn argument(&mut self, cx: &mut FnCx, arg: &hir::Expr, float_param: bool) -> Expr {
        let value = self.expr(cx, arg, false);
        if !float_param {
            return value;
        }
        let ty = self.ground(&self.typed.node_types[&arg.id], &cx.subst);
        widen(value, &ty)
    }

    fn node_mty(&mut self, cx: &FnCx, id: ExprId) -> MTy {
        let ty = self.ground(&self.typed.node_types[&id], &cx.subst);
        self.lower_ty(&ty)
    }

    fn push_func(&mut self, func: Func) -> FuncId {
        self.out.push(Some(func));
        FuncId(self.out.len() as u32 - 1)
    }

    /// The chain of `Let`s from `first`, lowered in a loop so a long block
    /// costs no stack.
    fn let_chain(&mut self, cx: &mut FnCx, first: &hir::Expr, tail: bool) -> Expr {
        let mut bound = Vec::new();
        let mut cursor = first;
        let body = loop {
            let ExprKind::Let {
                symbol,
                value,
                rest,
                ..
            } = &cursor.kind
            else {
                break self.expr(cx, cursor, tail);
            };
            let is_func = matches!(value.kind, ExprKind::Func { .. });
            if is_func || matches!(value.kind, ExprKind::Foreign { .. }) {
                match rest {
                    Some(rest) => cursor = rest,
                    None if is_func => {
                        break self.closure_value(cx, Target::Named(*symbol), value);
                    }
                    None => break self.foreign_value(cx, *symbol, value.id),
                }
                continue;
            }
            if let Some(rest) = rest {
                self.instantiate_binding(cx, *symbol, rest);
            }
            let ty = self.node_mty(cx, value.id);
            let value = self.expr(cx, value, false);
            let local = cx.fresh(ty);
            cx.locals.insert(*symbol, local);
            bound.push((local, value));
            match rest {
                Some(rest) => cursor = rest,
                None => break Expr::Local(local),
            }
        };
        bound.into_iter().rev().fold(body, |rest, (local, value)| {
            Expr::Let(local, Box::new(value), Box::new(rest))
        })
    }

    fn expr(&mut self, cx: &mut FnCx, e: &hir::Expr, tail: bool) -> Expr {
        match &e.kind {
            ExprKind::Unit => Expr::Const(Const::Unit),
            ExprKind::Int(n) => {
                let ty = self.ground(&self.typed.node_types[&e.id], &cx.subst);
                if ty == Ty::Float {
                    Expr::Const(Const::Float(*n as f64))
                } else if self.profile.fits_int(*n) {
                    Expr::Const(Const::Int(*n))
                } else {
                    Expr::Trap(INT_OVERFLOW.into())
                }
            }
            ExprKind::Float(x) => Expr::Const(Const::Float(*x)),
            ExprKind::Bool(b) => Expr::Const(Const::Bool(*b)),
            ExprKind::Var { symbol, .. } if self.foreign.contains_key(symbol) => {
                self.foreign_value(cx, *symbol, e.id)
            }
            ExprKind::Var { symbol, .. } => {
                let function = Target::Named(*symbol);
                match cx.self_env {
                    Some((me, env)) if me == *symbol => Expr::Local(env),
                    _ if self.lambdas.contains_key(&function) => {
                        self.closure_value(cx, function, e)
                    }
                    _ => self.variable_value(cx, *symbol),
                }
            }
            ExprKind::App { callee, args } => self.app(cx, e.span, callee, args, tail),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => Expr::If(
                Box::new(self.expr(cx, cond, false)),
                Box::new(self.expr(cx, then_branch, tail)),
                Box::new(match else_branch {
                    Some(e) => self.expr(cx, e, tail),
                    None => Expr::Const(Const::Unit),
                }),
            ),
            ExprKind::And { lhs, rhs } => Expr::If(
                Box::new(self.expr(cx, lhs, false)),
                Box::new(self.expr(cx, rhs, tail)),
                Box::new(Expr::Const(Const::Bool(false))),
            ),
            ExprKind::Or { lhs, rhs } => Expr::If(
                Box::new(self.expr(cx, lhs, false)),
                Box::new(Expr::Const(Const::Bool(true))),
                Box::new(self.expr(cx, rhs, tail)),
            ),
            ExprKind::Not(operand) => Expr::If(
                Box::new(self.expr(cx, operand, false)),
                Box::new(Expr::Const(Const::Bool(false))),
                Box::new(Expr::Const(Const::Bool(true))),
            ),
            ExprKind::Let { .. } => self.let_chain(cx, e, tail),
            ExprKind::Bin { op, lhs, rhs } => {
                let a = Box::new(self.expr(cx, lhs, false));
                let b = Box::new(self.expr(cx, rhs, false));
                self.bin(cx, (*op, e.span), (lhs, rhs), (a, b), tail)
            }
            ExprKind::Foreign { .. } => {
                unreachable!("a foreign function is only a declaration's value")
            }
            ExprKind::Builtin(Builtin::Print) => self.print_value(cx, e),
            ExprKind::Builtin(Builtin::Trap) => unreachable!("the checker rejects a bare `trap`"),
            ExprKind::Trap(message) => {
                let trap = Expr::Trap(message.clone());
                if e.span.in_prelude() {
                    trap
                } else {
                    Self::at_site(cx, e.span, trap)
                }
            }
            ExprKind::Func { .. } => self.closure_value(cx, Target::Anon(e.id), e),
            ExprKind::Str(s) => Expr::StrLit(self.intern(s)),
            ExprKind::Record { fields } => {
                let ty = self.ground(&self.typed.node_types[&e.id], &cx.subst);
                let MTy::Ptr(HeapKind::Record(layout)) = self.lower_ty(&ty) else {
                    unreachable!("record type lowers to a record pointer");
                };
                let mut order: Vec<_> = fields.iter().collect();
                order.sort_by(|a, b| a.0.cmp(&b.0));
                let values = order
                    .into_iter()
                    .map(|(_, v)| self.expr(cx, v, false))
                    .collect();
                Expr::AllocRecord(layout, values)
            }
            ExprKind::Tag { name, payload, .. } => self.tag(cx, e, name, payload.as_deref()),
            ExprKind::Match {
                scrutinee,
                arms,
                else_branch,
            } => self.match_(cx, scrutinee, arms, else_branch.as_deref(), tail),
            ExprKind::Field { record, label } => {
                let ty = self.ground(&self.typed.node_types[&record.id], &cx.subst);
                let Ty::Record(row) = ty.unfold_head() else {
                    unreachable!("field access on a non-record");
                };
                let index = field_index(&row, label);
                self.with_record(cx, record, |_, _, local| Expr::Field(local, index))
            }
            ExprKind::Spread { base, fields } => self.spread(cx, e, base, fields),
            ExprKind::Restrict { record, .. } => {
                let source_ty = self.ground(&self.typed.node_types[&record.id], &cx.subst);
                let ty = self.ground(&self.typed.node_types[&e.id], &cx.subst);
                let (Ty::Record(source_row), Ty::Record(row)) =
                    (source_ty.unfold_head(), ty.unfold_head())
                else {
                    unreachable!("restriction of a non-record");
                };
                let MTy::Ptr(HeapKind::Record(layout)) = self.lower_ty(&ty) else {
                    unreachable!("record type lowers to a record pointer");
                };
                self.with_record(cx, record, |_, _, local| {
                    let values = layout_fields(&row)
                        .map(|(label, _)| Expr::Field(local, field_index(&source_row, label)))
                        .collect();
                    Expr::AllocRecord(layout, values)
                })
            }
        }
    }

    /// `{...base, label: value, ...}`. A result of the base's own layout moves
    /// the base into `ReuseRecord`; one that adds or retypes a field allocates.
    #[inline(never)]
    fn spread(
        &mut self,
        cx: &mut FnCx,
        e: &hir::Expr,
        base: &hir::Expr,
        fields: &[(String, hir::Expr)],
    ) -> Expr {
        let base_ty = self.ground(&self.typed.node_types[&base.id], &cx.subst);
        let ty = self.ground(&self.typed.node_types[&e.id], &cx.subst);
        let (Ty::Record(base_row), Ty::Record(row)) = (base_ty.unfold_head(), ty.unfold_head())
        else {
            unreachable!("spread of a non-record");
        };
        let MTy::Ptr(HeapKind::Record(layout)) = self.lower_ty(&ty) else {
            unreachable!("record type lowers to a record pointer");
        };
        let reuses = self.lower_ty(&base_ty) == MTy::Ptr(HeapKind::Record(layout));
        self.with_record(cx, base, |m, cx, local| {
            let values = layout_fields(&row)
                .map(|(label, _)| match fields.iter().find(|(l, _)| l == label) {
                    Some((_, value)) => m.expr(cx, value, false),
                    None => Expr::Field(local, field_index(&base_row, label)),
                })
                .collect();
            if reuses {
                Expr::ReuseRecord(local, layout, values)
            } else {
                Expr::AllocRecord(layout, values)
            }
        })
    }

    /// `lhs op rhs` given the lowered operands. Called after they are lowered,
    /// not around them, so it adds nothing to the stack depth of a long chain
    /// of operators.
    #[inline(never)]
    /// A binary operator over operands of the types the checker gave them. An
    /// `Int` beside a `Float` is widened first, and `/` reads both as `Float`.
    fn bin(
        &mut self,
        cx: &mut FnCx,
        (op, span): (BinOp, Span),
        (lhs, rhs): (&hir::Expr, &hir::Expr),
        (a, b): (Box<Expr>, Box<Expr>),
        tail: bool,
    ) -> Expr {
        let lhs_ty = self.ground(&self.typed.node_types[&lhs.id], &cx.subst);
        let rhs_ty = self.ground(&self.typed.node_types[&rhs.id], &cx.subst);
        let scalars = [&lhs_ty, &rhs_ty]
            .iter()
            .all(|ty| matches!(ty, Ty::Int | Ty::Float));
        let (operand_ty, a, b) = if scalars && (lhs_ty != rhs_ty || op == BinOp::Div) {
            (Ty::Float, widen(*a, &lhs_ty), widen(*b, &rhs_ty))
        } else {
            (lhs_ty, *a, *b)
        };
        match op {
            BinOp::Add => self.arith(cx, Some(span), FloatOp::Add, &operand_ty, a, b),
            BinOp::Sub => self.arith(cx, Some(span), FloatOp::Sub, &operand_ty, a, b),
            BinOp::Mul => self.arith(cx, Some(span), FloatOp::Mul, &operand_ty, a, b),
            BinOp::Div => self.arith(cx, Some(span), FloatOp::Div, &operand_ty, a, b),
            BinOp::FloorDiv | BinOp::Mod => Self::whole_division(cx, (op, span), a, b),
            BinOp::Eq => self.equal(cx, &operand_ty, a, b, tail),
            BinOp::Ne => {
                let same = self.equal(cx, &operand_ty, a, b, false);
                Expr::If(
                    Box::new(same),
                    Box::new(Expr::Const(Const::Bool(false))),
                    Box::new(Expr::Const(Const::Bool(true))),
                )
            }
            BinOp::Lt => Expr::Cmp(CmpOp::Lt, Box::new(a), Box::new(b)),
            BinOp::Lte => Expr::Cmp(CmpOp::Le, Box::new(a), Box::new(b)),
            BinOp::Gt => Expr::Cmp(CmpOp::Gt, Box::new(a), Box::new(b)),
            BinOp::Gte => Expr::Cmp(CmpOp::Ge, Box::new(a), Box::new(b)),
        }
    }

    /// `print` used as a value: a closure over its printer for the argument
    /// type.
    #[inline(never)]
    fn print_value(&mut self, cx: &FnCx, e: &hir::Expr) -> Expr {
        let ty = self.ground(&self.typed.node_types[&e.id], &cx.subst);
        let Ty::Func(args, _) = &ty else {
            unreachable!("print has a function type");
        };
        let print = self.print_fn(&args[0]);
        self.closure_of(print, &ty)
    }

    /// Build `build(local)` where `local` holds `record`: a variable's own
    /// local, or else a fresh one the record is evaluated into first.
    fn with_record(
        &mut self,
        cx: &mut FnCx,
        record: &hir::Expr,
        build: impl FnOnce(&mut Self, &mut FnCx, Local) -> Expr,
    ) -> Expr {
        let borrowed = match &record.kind {
            ExprKind::Var { symbol, .. } => cx.locals.get(symbol).copied(),
            _ => None,
        };
        match borrowed {
            Some(local) => build(self, cx, local),
            None => {
                let ty = self.node_mty(cx, record.id);
                let rec = cx.fresh(ty);
                let source = self.expr(cx, record, false);
                let body = build(self, cx, rec);
                Expr::Let(rec, Box::new(source), Box::new(body))
            }
        }
    }

    /// `Name`, `Name(arg)` or `Name(a, b, ...)`: allocate the variant cell with
    /// the payload stored flat in its slots.
    fn tag(
        &mut self,
        cx: &mut FnCx,
        e: &hir::Expr,
        name: &str,
        payload: Option<&hir::Expr>,
    ) -> Expr {
        let ty = self.ground(&self.typed.node_types[&e.id], &cx.subst);
        let MTy::Ptr(HeapKind::Variant(layout)) = self.lower_ty(&ty) else {
            unreachable!("variant type lowers to a variant pointer");
        };
        let tag = self.tags[name];
        let Some(payload) = payload else {
            return Expr::AllocVariant(layout, tag, Vec::new());
        };
        let payload_ty = self.ground(&self.typed.node_types[&payload.id], &cx.subst);
        let Some(positional) = positional_fields(&payload_ty) else {
            let value = self.expr(cx, payload, false);
            return if payload_ty == Ty::Unit {
                Expr::Let(
                    cx.fresh(MTy::Unit),
                    Box::new(value),
                    Box::new(Expr::AllocVariant(layout, tag, Vec::new())),
                )
            } else {
                Expr::AllocVariant(layout, tag, vec![value])
            };
        };
        match &payload.kind {
            // A multi-argument tag: its record literal is labelled in
            // argument order, so evaluating it in order fills the slots in
            // order.
            ExprKind::Record { fields } => {
                let values = fields.iter().map(|(_, v)| self.expr(cx, v, false));
                Expr::AllocVariant(layout, tag, values.collect())
            }
            // A record of the same shape built elsewhere: take it apart.
            _ => {
                let Ty::Record(row) = payload_ty.unfold_head() else {
                    unreachable!("positional payloads are records");
                };
                let record = cx.fresh(self.lower_ty(&payload_ty));
                let value = self.expr(cx, payload, false);
                let slots = (0..positional.len())
                    .map(|n| Expr::Field(record, field_index(&row, &n.to_string())))
                    .collect();
                Expr::Let(
                    record,
                    Box::new(value),
                    Box::new(Expr::AllocVariant(layout, tag, slots)),
                )
            }
        }
    }

    /// `match scrutinee do arms else … done` as a `Switch` on the cell's tag.
    /// Each arm borrows its binders out of the cell with `Payload`; without an
    /// `else`, the checker has made the arms exhaustive, so the last one is the
    /// default.
    fn match_(
        &mut self,
        cx: &mut FnCx,
        scrutinee: &hir::Expr,
        arms: &[hir::MatchArm],
        else_branch: Option<&hir::Expr>,
        tail: bool,
    ) -> Expr {
        let scrutinee_ty = self.ground(&self.typed.node_types[&scrutinee.id], &cx.subst);
        let Ty::Variant(row) = scrutinee_ty.unfold_head() else {
            unreachable!("match on a non-variant");
        };
        let borrowed = match &scrutinee.kind {
            ExprKind::Var { symbol, .. } => cx.locals.get(symbol).copied(),
            _ => None,
        };
        let (local, bound) = match borrowed {
            Some(local) => (local, None),
            None => {
                let ty = self.lower_ty(&scrutinee_ty);
                (cx.fresh(ty), Some(self.expr(cx, scrutinee, false)))
            }
        };

        let mut lowered: Vec<(u32, Expr)> = Vec::new();
        for arm in arms {
            let pattern = &arm.pattern;
            let tag = self.tags[&pattern.tag];
            let payload_ty = ground_fields(&row)
                .find(|(label, _)| **label == pattern.tag)
                .map(|(_, ty)| ty.clone())
                .expect("checked match arm names a tag of the scrutinee");
            let bindings = self.bind_payload(cx, local, tag, &pattern.payload, &payload_ty);
            let body = self.expr(cx, &arm.body, tail);
            let arm = bindings.into_iter().rev().fold(body, |body, (l, v)| {
                Expr::Let(l, Box::new(v), Box::new(body))
            });
            lowered.push((tag, arm));
        }
        let default = match else_branch {
            Some(e) => self.expr(cx, e, tail),
            None => lowered
                .pop()
                .map_or_else(|| Expr::Trap("no arm matches".into()), |(_, arm)| arm),
        };
        let switch = Expr::Switch(local, lowered, Box::new(default));
        match bound {
            Some(value) => Expr::Let(local, Box::new(value), Box::new(switch)),
            None => switch,
        }
    }

    /// The `Let` bindings that give an arm's binders their values from the
    /// payload of tag `tag` in the cell `cell`.
    fn bind_payload(
        &mut self,
        cx: &mut FnCx,
        cell: Local,
        tag: u32,
        pattern: &PatternPayload,
        payload_ty: &Ty,
    ) -> Vec<(Local, Expr)> {
        let mut bindings = Vec::new();
        let mut bind = |cx: &mut FnCx, param: &Param, ty: MTy, value: Expr| {
            let local = cx.fresh(ty);
            cx.locals.insert(param.symbol, local);
            bindings.push((local, value));
        };
        match pattern {
            PatternPayload::None => {}
            PatternPayload::Fields(fields) => {
                let Ty::Record(row) = payload_ty.unfold_head() else {
                    unreachable!("a multi-argument payload is a record");
                };
                for (label, param) in fields {
                    let slot = label.parse().expect("pattern labels are positional");
                    let field_ty = ground_fields(&row)
                        .find(|(l, _)| *l == label)
                        .map(|(_, ty)| ty.clone())
                        .expect("a pattern label names a payload field");
                    let ty = self.lower_ty(&field_ty);
                    bind(cx, param, ty, Expr::Payload(cell, tag, slot));
                }
            }
            PatternPayload::Whole(param) => {
                let head = payload_ty.unfold_head();
                let value = match (&head, positional_fields(payload_ty)) {
                    (Ty::Unit, _) => Expr::Const(Const::Unit),
                    // The whole payload of a multi-argument tag is a record;
                    // the cell stores it flat, so build it from the slots.
                    (Ty::Record(row), Some(_)) => {
                        let MTy::Ptr(HeapKind::Record(layout)) = self.lower_ty(payload_ty) else {
                            unreachable!("record type lowers to a record pointer");
                        };
                        let slots = ground_fields(row)
                            .map(|(label, _)| {
                                let slot = label.parse().expect("labels are positional");
                                Expr::Payload(cell, tag, slot)
                            })
                            .collect();
                        Expr::AllocRecord(layout, slots)
                    }
                    _ => Expr::Payload(cell, tag, 0),
                };
                let ty = self.lower_ty(payload_ty);
                bind(cx, param, ty, value);
            }
        }
        bindings
    }

    /// `e` run after naming `span` as the user code a trap should be blamed on.
    fn at_site(cx: &mut FnCx, span: Span, e: Expr) -> Expr {
        let site = Expr::Site(span.start, span.end);
        Expr::Let(cx.fresh(MTy::Unit), Box::new(site), Box::new(e))
    }

    #[inline(never)]
    fn app(
        &mut self,
        cx: &mut FnCx,
        span: Span,
        callee: &hir::Expr,
        args: &[hir::Expr],
        tail: bool,
    ) -> Expr {
        if let (ExprKind::Builtin(Builtin::Print), [arg]) = (&callee.kind, args) {
            let ty = self.ground(&self.typed.node_types[&arg.id], &cx.subst);
            let print = self.print_fn(&ty);
            let value = self.expr(cx, arg, false);
            return if tail {
                Expr::TailCall(Callee::Direct(print), vec![value])
            } else {
                Expr::CallDirect(print, vec![value])
            };
        }
        if let ExprKind::Var { symbol, .. } = &callee.kind
            && self.foreign.contains_key(symbol)
        {
            return self.foreign_call(cx, *symbol, args);
        }
        let direct = match &callee.kind {
            ExprKind::Var { symbol, .. }
                if self
                    .lambdas
                    .get(&Target::Named(*symbol))
                    .is_some_and(|f| f.captures.is_empty()) =>
            {
                Some(self.specialize(cx, Target::Named(*symbol), callee).0)
            }
            _ => None,
        };
        let enters_prelude = !span.in_prelude()
            && matches!(&callee.kind, ExprKind::Var { symbol, .. }
                if self.lambdas.get(&Target::Named(*symbol)).is_some_and(|f| f.body.span.in_prelude()));
        let target = match direct {
            Some(id) => Callee::Direct(id),
            None => Callee::Closure(Box::new(self.expr(cx, callee, false))),
        };
        let hir_args = args;
        let callee_ty = self.ground(&self.typed.node_types[&callee.id], &cx.subst);
        let float_params: Vec<bool> = match callee_ty.unfold_head() {
            Ty::Func(params, _) => params.iter().map(|p| *p == Ty::Float).collect(),
            _ => Vec::new(),
        };
        let float_param = |i: usize| float_params.get(i).copied().unwrap_or(false);
        let mut args: Vec<Expr> = args
            .iter()
            .enumerate()
            .map(|(i, a)| self.argument(cx, a, float_param(i)))
            .collect();
        // The site is set after the arguments run, so a call nested in an
        // argument cannot overwrite it.
        let mut bound = Vec::new();
        if enters_prelude {
            for (i, (arg, hir_arg)) in args.iter_mut().zip(hir_args).enumerate() {
                let ty = if float_param(i) {
                    MTy::Float
                } else {
                    self.node_mty(cx, hir_arg.id)
                };
                let local = cx.fresh(ty);
                bound.push((local, std::mem::replace(arg, Expr::Local(local))));
            }
        }
        let call = match (tail, target) {
            (false, Callee::Direct(id)) => Expr::CallDirect(id, args),
            (false, Callee::Closure(c)) => Expr::CallClosure(c, args),
            (true, target) => Expr::TailCall(target, args),
        };
        if !enters_prelude {
            return call;
        }
        let call = Self::at_site(cx, span, call);
        bound.into_iter().rev().fold(call, |rest, (local, value)| {
            Expr::Let(local, Box::new(value), Box::new(rest))
        })
    }
}

/// Recover the substitution that makes `template` equal the ground `actual`.
fn match_ty(template: &Ty, actual: &Ty, subst: &mut Subst) {
    match_ty_in(template, actual, subst, &mut HashSet::new());
}

/// `seen` holds the pairs of recursive types already being matched: unfolding
/// a `μ` re-exposes the same `μ` one level down, so a repeated pair is
/// matched coinductively, as the checker unifies them.
fn match_ty_in(template: &Ty, actual: &Ty, subst: &mut Subst, seen: &mut HashSet<(Ty, Ty)>) {
    match (template, actual) {
        (Ty::Var(v), t) => {
            let prev = subst.insert(*v, t.clone());
            debug_assert!(
                prev.is_none_or(|p| canonical(&p) == canonical(t)),
                "inconsistent instantiation"
            );
        }
        (Ty::Rec(..), _) | (_, Ty::Rec(..)) => {
            if seen.insert((template.clone(), actual.clone())) {
                match_ty_in(&template.unfold_head(), &actual.unfold_head(), subst, seen);
            }
        }
        (Ty::Func(ta, tr), Ty::Func(aa, ar)) => {
            for (t, a) in ta.iter().zip(aa) {
                match_ty_in(t, a, subst, seen);
            }
            match_ty_in(tr, ar, subst, seen);
        }
        (Ty::Record(template), Ty::Record(actual)) => {
            match_row(template, actual, subst, seen, Ty::Record);
        }
        (Ty::Variant(template), Ty::Variant(actual)) => {
            match_row(template, actual, subst, seen, Ty::Variant);
        }
        (t, a) => debug_assert_eq!(t, a, "template does not match use site"),
    }
}

/// Match the fields `template` names against those of `actual`; its tail
/// variable, if open, takes the rest, wrapped by `wrap` into the row's type.
fn match_row(
    template: &Row,
    actual: &Row,
    subst: &mut Subst,
    seen: &mut HashSet<(Ty, Ty)>,
    wrap: fn(Row) -> Ty,
) {
    let mut rest: Vec<_> = ground_fields(actual).collect();
    let mut row = template;
    loop {
        match row {
            Row::Extend {
                label,
                field,
                rest: next,
            } => {
                if let Some(at) = rest.iter().position(|(l, _)| *l == label) {
                    match_ty_in(field, rest.remove(at).1, subst, seen);
                }
                row = next;
            }
            Row::Var(v) => {
                let tail = rest
                    .into_iter()
                    .rev()
                    .fold(Row::Empty, |r, (l, f)| Row::Extend {
                        label: l.clone(),
                        field: Box::new(f.clone()),
                        rest: Box::new(r),
                    });
                subst.insert(*v, wrap(tail));
                break;
            }
            Row::Empty => break,
        }
    }
}

/// The row of the variant type `key`, unfolded if it is recursive.
fn variant_row(key: &Ty) -> Row {
    match key.unfold_head() {
        Ty::Variant(row) => row,
        _ => unreachable!("a variant key unfolds to a variant"),
    }
}

/// The layout slot of `label` in a ground record row.
fn field_index(row: &Row, label: &str) -> usize {
    layout_fields(row)
        .position(|(l, _)| l == label)
        .expect("checked record has the field")
}

/// The fields of a payload record labelled exactly `0`, `1`, ... (what a
/// multi-argument tag builds, which no source record can spell), in argument
/// order.
fn positional_fields(payload: &Ty) -> Option<Vec<Ty>> {
    // A payload record that mentions its own variant is itself a `μ`.
    let Ty::Record(row) = payload.unfold_head() else {
        return None;
    };
    let mut fields = ground_fields(&row)
        .map(|(label, ty)| Some((label.parse::<usize>().ok()?, ty.clone())))
        .collect::<Option<Vec<_>>>()?;
    fields.sort_by_key(|(n, _)| *n);
    let dense = fields.iter().enumerate().all(|(i, (n, _))| i == *n);
    (dense && !fields.is_empty()).then(|| fields.into_iter().map(|(_, ty)| ty).collect())
}

/// The slots a tag's payload occupies: none for `Unit`, one per argument for a
/// positional record (stored flat, not behind a record), else one.
fn payload_fields(payload: &Ty) -> Vec<Ty> {
    match payload {
        Ty::Unit => Vec::new(),
        other => positional_fields(other).unwrap_or_else(|| vec![other.clone()]),
    }
}
