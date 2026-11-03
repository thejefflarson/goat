//! Monomorphization: checked HIR to ground-typed MIR, one `Func` per
//! `(binding, ground type)` specialization.

use crate::mir::*;
use goat_checker::hir::{self, BinOp, ExprId, ExprKind, Param, Span, Symbol};
use goat_checker::infer::Typed;
use goat_checker::ty::{Row, Ty, TypeVar};
use goat_checker::{Checked, GoatError};
use std::collections::{HashMap, HashSet};

type Subst = HashMap<TypeVar, Ty>;

/// Lower a checked program to MIR. Constructs whose runtime support has not
/// landed yet (ADR 0005) come back as spanned diagnostics; well-typed input
/// never panics.
pub fn mono(checked: &Checked) -> Result<Program, Vec<GoatError>> {
    let (lambdas, var_tys) = collect_lambdas(&checked.typed, &checked.root);
    let mut m = Mono {
        typed: &checked.typed,
        lambdas,
        var_tys,
        specs: Vec::new(),
        out: vec![None],
        work: Vec::new(),
        sigs: Vec::new(),
        layouts: Vec::new(),
        wrappers: HashMap::new(),
        errors: Vec::new(),
    };

    let mut cx = FnCx::new(Subst::new());
    let root_ty = m.ground(&checked.typed.root_ty, &cx.subst);
    let mut ret = m.lower_ty(&root_ty, checked.root.span);
    let owned = ret.is_ptr();
    let mut body = m.expr(&mut cx, &checked.root, !owned);
    if owned {
        // The program's value has no consumer, so release it here.
        let result = cx.fresh();
        let release = Expr::Let(
            cx.fresh(),
            Box::new(Expr::Drop(result)),
            Box::new(Expr::Const(Const::Unit)),
        );
        body = Expr::Let(result, Box::new(body), Box::new(release));
        ret = MTy::Unit;
    }
    m.out[0] = Some(Func {
        params: vec![],
        env: None,
        ret,
        body,
    });

    while let Some((id, target, subst, capture_tys)) = m.work.pop() {
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

    Ok(Program {
        funcs: m
            .out
            .into_iter()
            .map(|f| f.expect("func lowered"))
            .collect(),
        entry: FuncId(0),
        layouts: m.layouts,
        sigs: m.sigs,
        data: Vec::new(),
    })
}

/// A function literal's identity: a `name = program(...)` binding, or an
/// anonymous literal keyed by its expression.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Target {
    Named(Symbol),
    Anon(ExprId),
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
    lambdas: HashMap<Target, Lambda<'a>>,
    free: Vec<(Target, Vec<Symbol>)>,
    var_tys: HashMap<Symbol, &'a Ty>,
}

/// Find every function literal, its captures, and the type template of every
/// variable a closure might capture.
fn collect_lambdas<'a>(
    typed: &'a Typed,
    root: &'a hir::Expr,
) -> (HashMap<Target, Lambda<'a>>, HashMap<Symbol, &'a Ty>) {
    let mut c = Collector {
        typed,
        lambdas: HashMap::new(),
        free: Vec::new(),
        var_tys: HashMap::new(),
    };
    c.walk(root);
    resolve_captures(&mut c.lambdas, &c.free);
    (c.lambdas, c.var_tys)
}

impl<'a> Collector<'a> {
    fn walk(&mut self, e: &'a hir::Expr) {
        let typed = self.typed;
        match &e.kind {
            ExprKind::Let {
                symbol,
                value,
                rest,
                ..
            } => {
                match &value.kind {
                    ExprKind::Func { params, body } => {
                        let ty = &typed.schemes[symbol].ty;
                        self.lambda(Target::Named(*symbol), ty, params, body);
                    }
                    _ => {
                        self.var_tys.insert(*symbol, &typed.node_types[&value.id]);
                        self.walk(value);
                    }
                }
                if let Some(rest) = rest {
                    self.walk(rest);
                }
            }
            ExprKind::Func { params, body } => {
                self.lambda(Target::Anon(e.id), &typed.node_types[&e.id], params, body);
            }
            _ => for_each_child(e, &mut |c| self.walk(c)),
        }
    }

    fn lambda(&mut self, target: Target, ty: &'a Ty, params: &'a [Param], body: &'a hir::Expr) {
        if let Ty::Func(args, _) = ty {
            for (param, ty) in params.iter().zip(args) {
                self.var_tys.insert(param.symbol, ty);
            }
        }
        let mut free = free_symbols(params, body);
        if let Target::Named(me) = target {
            free.retain(|s| *s != me);
        }
        self.free.push((target, free));
        self.lambdas.insert(
            target,
            Lambda {
                params,
                body,
                ty,
                captures: Vec::new(),
            },
        );
        self.walk(body);
    }
}

/// Fix each literal's capture list: its free variables, where a referenced
/// function binding contributes that function's captures instead of itself.
/// Lists only grow and keep their order, so mutually recursive functions
/// settle on a common set.
fn resolve_captures(lambdas: &mut HashMap<Target, Lambda>, free: &[(Target, Vec<Symbol>)]) {
    let mut changed = true;
    while changed {
        changed = false;
        for (target, symbols) in free {
            let mut captures = lambdas[target].captures.clone();
            let before = captures.len();
            for s in symbols {
                let wanted = match lambdas.get(&Target::Named(*s)) {
                    Some(function) => function.captures.clone(),
                    None => vec![*s],
                };
                for c in wanted {
                    if !captures.contains(&c) {
                        captures.push(c);
                    }
                }
            }
            changed |= captures.len() != before;
            lambdas.get_mut(target).expect("collected").captures = captures;
        }
    }
}

/// The symbols `body` uses that neither it nor `params` bind, in order of
/// first use.
fn free_symbols(params: &[Param], body: &hir::Expr) -> Vec<Symbol> {
    fn scan(e: &hir::Expr, used: &mut Vec<Symbol>, bound: &mut HashSet<Symbol>) {
        match &e.kind {
            ExprKind::Var { symbol, .. } if !used.contains(symbol) => used.push(*symbol),
            ExprKind::Let { symbol, .. } => {
                bound.insert(*symbol);
            }
            ExprKind::Func { params, .. } => bound.extend(params.iter().map(|p| p.symbol)),
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

fn for_each_child<'a>(e: &'a hir::Expr, f: &mut impl FnMut(&'a hir::Expr)) {
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
        ExprKind::Field { record, .. } => f(record),
        ExprKind::Unit
        | ExprKind::Number(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Var { .. } => {}
    }
}

/// One specialization of a function literal: its use type and the ground types
/// of its captures fix the body.
struct Spec {
    target: Target,
    ty: Ty,
    capture_tys: Vec<Ty>,
    id: FuncId,
}

struct Mono<'a> {
    typed: &'a Typed,
    lambdas: HashMap<Target, Lambda<'a>>,
    var_tys: HashMap<Symbol, &'a Ty>,
    specs: Vec<Spec>,
    out: Vec<Option<Func>>,
    work: Vec<(FuncId, Target, Subst, Vec<Ty>)>,
    sigs: Vec<Sig>,
    layouts: Vec<Layout>,
    /// The zero-capture closure wrapper for each function used as a value. The
    /// wrappers are the funcref-table members: the functions with an `env`.
    wrappers: HashMap<FuncId, FuncId>,
    errors: Vec<GoatError>,
}

struct FnCx {
    subst: Subst,
    locals: HashMap<Symbol, Local>,
    /// Owned pointer locals in scope, including a closure's `env`; each tail
    /// leaf drops them.
    live: Vec<Local>,
    /// The `Capture` index of each captured variable.
    captures: HashMap<Symbol, usize>,
    /// A capturing function's own name and `env`; the name refers to the
    /// closure being run, never to a stored capture.
    self_env: Option<(Symbol, Local)>,
    next: u32,
}

impl FnCx {
    fn new(subst: Subst) -> FnCx {
        FnCx {
            subst,
            locals: HashMap::new(),
            live: Vec::new(),
            captures: HashMap::new(),
            self_env: None,
            next: 0,
        }
    }

    fn fresh(&mut self) -> Local {
        self.next += 1;
        Local(self.next - 1)
    }
}

impl Mono<'_> {
    /// Apply `subst`, defaulting unconstrained type variables to `Unit` and
    /// row variables to the empty row.
    fn ground(&self, ty: &Ty, subst: &Subst) -> Ty {
        match ty {
            Ty::Var(v) => subst.get(v).cloned().unwrap_or(Ty::Unit),
            Ty::Func(args, ret) => Ty::Func(
                args.iter().map(|a| self.ground(a, subst)).collect(),
                Box::new(self.ground(ret, subst)),
            ),
            Ty::Record(row) => Ty::Record(self.ground_row(row, subst)),
            other => other.clone(),
        }
    }

    /// Ground `row` into a closed row with its fields stably sorted by label,
    /// the order of its layout slots.
    fn ground_row(&self, row: &Row, subst: &Subst) -> Row {
        let mut fields = Vec::new();
        self.flatten_row(row, subst, &mut fields);
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

    fn flatten_row(&self, row: &Row, subst: &Subst, out: &mut Vec<(String, Ty)>) {
        match row {
            Row::Empty => {}
            Row::Var(v) => {
                if let Some(Ty::Record(bound)) = subst.get(v) {
                    self.flatten_row(bound, subst, out);
                }
            }
            Row::Extend { label, field, rest } => {
                out.push((label.clone(), self.ground(field, subst)));
                self.flatten_row(rest, subst, out);
            }
        }
    }

    fn error(&mut self, span: Span, message: impl Into<String>) {
        self.errors.push(GoatError::new(span, message));
    }

    fn unsupported(&mut self, span: Span, what: &str) -> Expr {
        self.error(span, format!("{what} are not supported yet"));
        Expr::Trap(String::new())
    }

    fn lower_ty(&mut self, ty: &Ty, span: Span) -> MTy {
        match ty {
            Ty::Number => MTy::Float,
            Ty::Bool => MTy::Bool,
            Ty::Unit => MTy::Unit,
            Ty::Func(args, ret) => {
                let sig = Sig {
                    params: args.iter().map(|a| self.lower_ty(a, span)).collect(),
                    ret: self.lower_ty(ret, span),
                };
                let id = self.sigs.iter().position(|s| *s == sig).unwrap_or_else(|| {
                    self.sigs.push(sig);
                    self.sigs.len() - 1
                });
                MTy::Ptr(HeapKind::Closure(SigId(id as u32)))
            }
            Ty::Record(row) => {
                let mut fields = Vec::new();
                for (_, field) in ground_fields(row) {
                    fields.push(self.lower_ty(field, span));
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
            Ty::Str => {
                self.unsupported(span, "strings");
                MTy::Unit
            }
            Ty::Var(_) => unreachable!("type variable survived grounding"),
        }
    }

    fn specialize(&mut self, cx: &FnCx, target: Target, use_id: ExprId) -> (FuncId, Ty) {
        let use_ty = self.ground(&self.typed.node_types[&use_id], &cx.subst);
        let Lambda { ty, captures, .. } = self.lambdas[&target].clone();
        let capture_tys: Vec<Ty> = captures
            .iter()
            .map(|c| self.ground(self.var_tys[c], &cx.subst))
            .collect();
        if let Some(spec) = self
            .specs
            .iter()
            .find(|s| s.target == target && s.ty == use_ty && s.capture_tys == capture_tys)
        {
            return (spec.id, use_ty);
        }
        let id = FuncId(self.out.len() as u32);
        self.out.push(None);

        // The body also mentions the enclosing scope's type variables; the
        // captured variables' ground types recover them.
        let mut subst = Subst::new();
        match_ty(ty, &use_ty, &mut subst);
        for (c, capture_ty) in captures.iter().zip(&capture_tys) {
            match_ty(self.var_tys[c], capture_ty, &mut subst);
        }
        self.work.push((id, target, subst, capture_tys.clone()));
        self.specs.push(Spec {
            target,
            ty: use_ty.clone(),
            capture_tys,
            id,
        });
        (id, use_ty)
    }

    /// The closure value of `target` at a use site: a static closure when it
    /// captures nothing, else a fresh heap closure over the captured variables.
    fn closure_value(&mut self, cx: &mut FnCx, target: Target, use_id: ExprId, span: Span) -> Expr {
        let (id, ty) = self.specialize(cx, target, use_id);
        let captures = self.lambdas[&target].captures.clone();
        if captures.is_empty() {
            return self.closure_of(id, &ty, span);
        }
        let values = captures
            .into_iter()
            .map(|c| self.variable_value(cx, c, span))
            .collect();
        Expr::MakeClosure(id, values)
    }

    /// An owned reference to a captured or local variable.
    fn variable_value(&mut self, cx: &mut FnCx, symbol: Symbol, span: Span) -> Expr {
        if let Some(&local) = cx.locals.get(&symbol) {
            return if cx.live.contains(&local) {
                self.use_closure(cx, local)
            } else {
                Expr::Local(local)
            };
        }
        if let Some(&index) = cx.captures.get(&symbol) {
            return Expr::Capture(index);
        }
        self.error(span, "a variable is used before it is defined");
        Expr::Trap(String::new())
    }

    /// A zero-capture closure over `target`: a wrapper that takes the closure
    /// as `env`, drops it, and tail-calls `target`.
    fn closure_of(&mut self, target: FuncId, ty: &Ty, span: Span) -> Expr {
        let wrapper = match self.wrappers.get(&target) {
            Some(&w) => w,
            None => {
                let MTy::Ptr(HeapKind::Closure(sig)) = self.lower_ty(ty, span) else {
                    unreachable!("function type lowers to a closure");
                };
                let Sig { params, ret } = self.sigs[sig.0 as usize].clone();
                let env = Local(params.len() as u32);
                let locals: Vec<_> = (0..params.len() as u32).map(Local).collect();
                let body = Expr::Let(
                    Local(env.0 + 1),
                    Box::new(Expr::Drop(env)),
                    Box::new(Expr::TailCall(
                        Callee::Direct(target),
                        locals.iter().map(|l| Expr::Local(*l)).collect(),
                    )),
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
            let local = cx.fresh();
            cx.locals.insert(param.symbol, local);
            let ty = self.ground(ty, &cx.subst);
            let mty = self.lower_ty(&ty, param.span);
            if mty.is_ptr() {
                cx.live.push(local);
            }
            mparams.push((local, mty));
        }
        let ret = self.ground(ret_ty, &cx.subst);
        let env = if captures.is_empty() {
            None
        } else {
            Some(self.bind_env(&mut cx, target, ty, &captures, &capture_tys, body.span))
        };
        Func {
            params: mparams,
            env,
            ret: self.lower_ty(&ret, body.span),
            body: self.expr(&mut cx, body, true),
        }
    }

    /// Give a capturing function its `env` parameter. The function owns `env`,
    /// so it is released at every exit like any other pointer local.
    fn bind_env(
        &mut self,
        cx: &mut FnCx,
        target: Target,
        ty: &Ty,
        captures: &[Symbol],
        capture_tys: &[Ty],
        span: Span,
    ) -> Env {
        let ty = self.ground(ty, &cx.subst);
        let MTy::Ptr(HeapKind::Closure(sig)) = self.lower_ty(&ty, span) else {
            unreachable!("function type lowers to a closure");
        };
        let local = cx.fresh();
        cx.live.push(local);
        cx.captures = captures.iter().copied().zip(0..).collect();
        if let Target::Named(symbol) = target {
            cx.self_env = Some((symbol, local));
        }
        Env {
            local,
            sig,
            captures: capture_tys.iter().map(|t| self.lower_ty(t, span)).collect(),
        }
    }

    /// Finish a leaf: in tail position, release the closure locals still in
    /// scope once `value` is computed.
    fn leaf(&self, cx: &mut FnCx, value: Expr, tail: bool) -> Expr {
        if !tail || cx.live.is_empty() {
            return value;
        }
        let result = cx.fresh();
        let mut body = Expr::Local(result);
        for l in cx.live.clone().into_iter().rev() {
            body = Expr::Let(cx.fresh(), Box::new(Expr::Drop(l)), Box::new(body));
        }
        Expr::Let(result, Box::new(value), Box::new(body))
    }

    /// A fresh owned reference to closure local `l`, which stays live.
    fn use_closure(&self, cx: &mut FnCx, l: Local) -> Expr {
        Expr::Let(cx.fresh(), Box::new(Expr::Dup(l)), Box::new(Expr::Local(l)))
    }

    fn expr(&mut self, cx: &mut FnCx, e: &hir::Expr, tail: bool) -> Expr {
        match &e.kind {
            ExprKind::Unit => self.leaf(cx, Expr::Const(Const::Unit), tail),
            ExprKind::Number(n) => self.leaf(cx, Expr::Const(Const::Float(*n)), tail),
            ExprKind::Bool(b) => self.leaf(cx, Expr::Const(Const::Bool(*b)), tail),
            ExprKind::Var { symbol, .. } => {
                let function = Target::Named(*symbol);
                let value = match cx.self_env {
                    Some((me, env)) if me == *symbol => self.use_closure(cx, env),
                    _ if self.lambdas.contains_key(&function) => {
                        self.closure_value(cx, function, e.id, e.span)
                    }
                    _ => self.variable_value(cx, *symbol, e.span),
                };
                self.leaf(cx, value, tail)
            }
            ExprKind::App { callee, args } => self.app(cx, callee, args, tail),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => Expr::If(
                Box::new(self.expr(cx, cond, false)),
                Box::new(self.expr(cx, then_branch, tail)),
                Box::new(match else_branch {
                    Some(e) => self.expr(cx, e, tail),
                    None => self.leaf(cx, Expr::Const(Const::Unit), tail),
                }),
            ),
            ExprKind::Let {
                symbol,
                value,
                rest,
                ..
            } => {
                if matches!(value.kind, ExprKind::Func { .. }) {
                    return match rest {
                        Some(rest) => self.expr(cx, rest, tail),
                        None => {
                            let function = Target::Named(*symbol);
                            let closure = self.closure_value(cx, function, value.id, e.span);
                            self.leaf(cx, closure, tail)
                        }
                    };
                }
                let ty = self.ground(&self.typed.node_types[&value.id], &cx.subst);
                let owned = self.lower_ty(&ty, value.span).is_ptr();
                let value = self.expr(cx, value, false);
                let local = cx.fresh();
                cx.locals.insert(*symbol, local);
                let rest = match rest {
                    Some(rest) if owned => {
                        cx.live.push(local);
                        let body = self.expr(cx, rest, tail);
                        cx.live.pop();
                        if tail {
                            body
                        } else {
                            let result = cx.fresh();
                            let release = Expr::Let(
                                cx.fresh(),
                                Box::new(Expr::Drop(local)),
                                Box::new(Expr::Local(result)),
                            );
                            Expr::Let(result, Box::new(body), Box::new(release))
                        }
                    }
                    Some(rest) => self.expr(cx, rest, tail),
                    None => Expr::Local(local),
                };
                Expr::Let(local, Box::new(value), Box::new(rest))
            }
            ExprKind::Bin { op, lhs, rhs } => {
                let a = Box::new(self.expr(cx, lhs, false));
                let b = Box::new(self.expr(cx, rhs, false));
                let value = match op {
                    BinOp::Add => Expr::BinFloat(FloatOp::Add, a, b),
                    BinOp::Sub => Expr::BinFloat(FloatOp::Sub, a, b),
                    BinOp::Mul => Expr::BinFloat(FloatOp::Mul, a, b),
                    BinOp::Div => Expr::BinFloat(FloatOp::Div, a, b),
                    BinOp::Lt => Expr::Cmp(CmpOp::Lt, a, b),
                    BinOp::Lte => Expr::Cmp(CmpOp::Le, a, b),
                    BinOp::Gt => Expr::Cmp(CmpOp::Gt, a, b),
                    BinOp::Gte => Expr::Cmp(CmpOp::Ge, a, b),
                };
                self.leaf(cx, value, tail)
            }
            ExprKind::Func { .. } => {
                let closure = self.closure_value(cx, Target::Anon(e.id), e.id, e.span);
                self.leaf(cx, closure, tail)
            }
            ExprKind::Str(_) => self.unsupported(e.span, "strings"),
            ExprKind::Record { fields } => {
                let ty = self.ground(&self.typed.node_types[&e.id], &cx.subst);
                let MTy::Ptr(HeapKind::Record(layout)) = self.lower_ty(&ty, e.span) else {
                    unreachable!("record type lowers to a record pointer");
                };
                let mut order: Vec<_> = fields.iter().collect();
                order.sort_by(|a, b| a.0.cmp(&b.0));
                let values = order
                    .into_iter()
                    .map(|(_, v)| self.expr(cx, v, false))
                    .collect();
                self.leaf(cx, Expr::AllocRecord(layout, values), tail)
            }
            ExprKind::Field { record, label } => {
                let ty = self.ground(&self.typed.node_types[&record.id], &cx.subst);
                let Ty::Record(row) = &ty else {
                    unreachable!("field access on a non-record");
                };
                let index = ground_fields(row)
                    .position(|(l, _)| l == label)
                    .expect("checked record has the field");
                let borrowed = match &record.kind {
                    ExprKind::Var { symbol, .. } => cx.locals.get(symbol).copied(),
                    _ => None,
                };
                let value = match borrowed {
                    Some(local) => Expr::Field(local, index),
                    None => {
                        let (rec, field, release) = (cx.fresh(), cx.fresh(), cx.fresh());
                        let source = self.expr(cx, record, false);
                        let drop = Expr::Let(
                            release,
                            Box::new(Expr::Drop(rec)),
                            Box::new(Expr::Local(field)),
                        );
                        let load =
                            Expr::Let(field, Box::new(Expr::Field(rec, index)), Box::new(drop));
                        Expr::Let(rec, Box::new(source), Box::new(load))
                    }
                };
                self.leaf(cx, value, tail)
            }
        }
    }

    fn app(&mut self, cx: &mut FnCx, callee: &hir::Expr, args: &[hir::Expr], tail: bool) -> Expr {
        let direct = match &callee.kind {
            ExprKind::Var { symbol, .. }
                if self
                    .lambdas
                    .get(&Target::Named(*symbol))
                    .is_some_and(|f| f.captures.is_empty()) =>
            {
                Some(self.specialize(cx, Target::Named(*symbol), callee.id).0)
            }
            _ => None,
        };
        let target = match direct {
            Some(id) => Callee::Direct(id),
            None => Callee::Closure(Box::new(self.expr(cx, callee, false))),
        };
        let args: Vec<Expr> = args.iter().map(|a| self.expr(cx, a, false)).collect();
        if !tail {
            return match target {
                Callee::Direct(id) => Expr::CallDirect(id, args),
                Callee::Closure(c) => Expr::CallClosure(c, args),
            };
        }
        if cx.live.is_empty() {
            return Expr::TailCall(target, args);
        }

        // Closure locals are released before the tail call, so the callee and
        // arguments are evaluated into temporaries first.
        let mut bindings = Vec::new();
        let target = match target {
            Callee::Closure(c) => {
                let t = cx.fresh();
                bindings.push((t, *c));
                Callee::Closure(Box::new(Expr::Local(t)))
            }
            direct => direct,
        };
        let mut temps = Vec::new();
        for arg in args {
            let t = cx.fresh();
            bindings.push((t, arg));
            temps.push(Expr::Local(t));
        }
        let mut body = Expr::TailCall(target, temps);
        for l in cx.live.clone() {
            body = Expr::Let(cx.fresh(), Box::new(Expr::Drop(l)), Box::new(body));
        }
        for (t, value) in bindings.into_iter().rev() {
            body = Expr::Let(t, Box::new(value), Box::new(body));
        }
        body
    }
}

/// Recover the substitution that makes `template` equal the ground `actual`.
fn match_ty(template: &Ty, actual: &Ty, subst: &mut Subst) {
    match (template, actual) {
        (Ty::Var(v), t) => {
            let prev = subst.insert(*v, t.clone());
            debug_assert!(prev.is_none_or(|p| p == *t), "inconsistent instantiation");
        }
        (Ty::Func(ta, tr), Ty::Func(aa, ar)) => {
            for (t, a) in ta.iter().zip(aa) {
                match_ty(t, a, subst);
            }
            match_ty(tr, ar, subst);
        }
        (Ty::Record(template), Ty::Record(actual)) => {
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
                            match_ty(field, rest.remove(at).1, subst);
                        }
                        row = next;
                    }
                    Row::Var(v) => {
                        let tail =
                            rest.into_iter()
                                .rev()
                                .fold(Row::Empty, |r, (l, f)| Row::Extend {
                                    label: l.clone(),
                                    field: Box::new(f.clone()),
                                    rest: Box::new(r),
                                });
                        subst.insert(*v, Ty::Record(tail));
                        break;
                    }
                    Row::Empty => break,
                }
            }
        }
        (t, a) => debug_assert_eq!(t, a, "template does not match use site"),
    }
}

/// The `(label, type)` pairs of a ground row, in layout order.
fn ground_fields(row: &Row) -> impl Iterator<Item = (&String, &Ty)> {
    let mut next = Some(row);
    std::iter::from_fn(move || match next? {
        Row::Extend { label, field, rest } => {
            next = Some(rest);
            Some((label, &**field))
        }
        Row::Empty | Row::Var(_) => None,
    })
}
