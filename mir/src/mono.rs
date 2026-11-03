//! Monomorphization: checked HIR to ground-typed MIR, one `Func` per
//! `(binding, ground type)` specialization.

use crate::mir::*;
use goat_checker::hir::{self, BinOp, ExprKind, Param, Span, Symbol};
use goat_checker::infer::Typed;
use goat_checker::ty::{Row, Ty, TypeVar};
use goat_checker::{Checked, GoatError};
use std::collections::HashMap;

type Subst = HashMap<TypeVar, Ty>;

/// Lower a checked program to MIR. Constructs whose runtime support has not
/// landed yet (ADR 0005) and captured variables (until closures land) come back
/// as spanned diagnostics; well-typed input never panics.
pub fn mono(checked: &Checked) -> Result<Program, Vec<GoatError>> {
    let mut funcs = HashMap::new();
    collect_funcs(&checked.root, &mut funcs);
    let mut m = Mono {
        typed: &checked.typed,
        funcs,
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
    let mut body = m.expr(&mut cx, &checked.root, true);
    if matches!(ret, MTy::Ptr(HeapKind::Record(_))) {
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

    while let Some((id, symbol, subst)) = m.work.pop() {
        let func = m.specialize_body(symbol, subst);
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

fn collect_funcs<'a>(e: &'a hir::Expr, out: &mut HashMap<Symbol, (&'a [Param], &'a hir::Expr)>) {
    match &e.kind {
        ExprKind::Let {
            symbol,
            value,
            rest,
            ..
        } => {
            if let ExprKind::Func { params, body } = &value.kind {
                out.insert(*symbol, (params, body));
            }
            collect_funcs(value, out);
            if let Some(rest) = rest {
                collect_funcs(rest, out);
            }
        }
        ExprKind::Func { body, .. } => collect_funcs(body, out),
        ExprKind::App { callee, args } => {
            collect_funcs(callee, out);
            args.iter().for_each(|a| collect_funcs(a, out));
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_funcs(cond, out);
            collect_funcs(then_branch, out);
            if let Some(e) = else_branch {
                collect_funcs(e, out);
            }
        }
        ExprKind::Bin { lhs, rhs, .. } => {
            collect_funcs(lhs, out);
            collect_funcs(rhs, out);
        }
        ExprKind::Record { fields } => fields.iter().for_each(|(_, v)| collect_funcs(v, out)),
        ExprKind::Field { record, .. } => collect_funcs(record, out),
        ExprKind::Unit
        | ExprKind::Number(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Var { .. } => {}
    }
}

struct Mono<'a> {
    typed: &'a Typed,
    funcs: HashMap<Symbol, (&'a [Param], &'a hir::Expr)>,
    specs: Vec<(Symbol, Ty, FuncId)>,
    out: Vec<Option<Func>>,
    work: Vec<(FuncId, Symbol, Subst)>,
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
    /// Owned closure locals in scope; each tail leaf drops them.
    live: Vec<Local>,
    next: u32,
}

impl FnCx {
    fn new(subst: Subst) -> FnCx {
        FnCx {
            subst,
            locals: HashMap::new(),
            live: Vec::new(),
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

    fn specialize(&mut self, cx: &FnCx, symbol: Symbol, use_id: hir::ExprId) -> (FuncId, Ty) {
        let use_ty = self.ground(&self.typed.node_types[&use_id], &cx.subst);
        if let Some((_, _, id)) = self
            .specs
            .iter()
            .find(|(s, t, _)| *s == symbol && *t == use_ty)
        {
            return (*id, use_ty);
        }
        let id = FuncId(self.out.len() as u32);
        self.out.push(None);
        self.specs.push((symbol, use_ty.clone(), id));
        let mut subst = Subst::new();
        match_ty(&self.typed.schemes[&symbol].ty, &use_ty, &mut subst);
        self.work.push((id, symbol, subst));
        (id, use_ty)
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

    fn specialize_body(&mut self, symbol: Symbol, subst: Subst) -> Func {
        let (params, body) = self.funcs[&symbol];
        let Ty::Func(arg_tys, ret_ty) = &self.typed.schemes[&symbol].ty else {
            unreachable!("function binding without a function type");
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
        Func {
            params: mparams,
            env: None,
            ret: self.lower_ty(&ret, body.span),
            body: self.expr(&mut cx, body, true),
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
            ExprKind::Var { symbol, name } => {
                let value = if let Some(&local) = cx.locals.get(symbol) {
                    if cx.live.contains(&local) {
                        self.use_closure(cx, local)
                    } else {
                        Expr::Local(local)
                    }
                } else if self.funcs.contains_key(symbol) {
                    let (id, ty) = self.specialize(cx, *symbol, e.id);
                    self.closure_of(id, &ty, e.span)
                } else {
                    self.error(
                        e.span,
                        format!(
                            "`{name}` is captured from an enclosing scope; \
                             closures are not supported yet (Phase 4)"
                        ),
                    );
                    Expr::Trap(String::new())
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
                            let (id, ty) = self.specialize(cx, *symbol, value.id);
                            let closure = self.closure_of(id, &ty, e.span);
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
                self.error(
                    e.span,
                    "function literals outside a `name = program(...)` binding are not supported yet",
                );
                Expr::Trap(String::new())
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
            ExprKind::Var { symbol, .. } if self.funcs.contains_key(symbol) => {
                Some(self.specialize(cx, *symbol, callee.id).0)
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
