//! Monomorphization: checked HIR to ground-typed MIR, one `Func` per
//! `(binding, ground type)` specialization.

use crate::mir::*;
use crate::rc::insert_rc;
use goat_checker::captures::for_each_child;
use goat_checker::hir::{self, BinOp, ExprId, ExprKind, Param, Symbol};
use goat_checker::infer::Typed;
use goat_checker::ty::{Row, Ty, TypeVar};
use goat_checker::{Checked, GoatError, Target};
use std::collections::HashMap;

type Subst = HashMap<TypeVar, Ty>;

/// Lower a checked program to MIR and insert its reference counting.
/// Constructs whose runtime support has not landed yet (ADR 0005) come back as
/// spanned diagnostics; well-typed input never panics. No construct is staged
/// out at present.
pub fn mono(checked: &Checked) -> Result<Program, Vec<GoatError>> {
    let (lambdas, var_tys) = collect_lambdas(&checked.typed, &checked.root, &checked.captures);
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
        data: Vec::new(),
    };

    let mut cx = FnCx::new(Subst::new());
    let root_ty = m.ground(&checked.typed.root_ty, &cx.subst);
    let ret = m.lower_ty(&root_ty);
    // A pointer root is dropped after it is computed (see `rc::insert_rc`), so
    // it cannot end in a tail call; a string root is handed to the host.
    let discarded = ret.is_ptr() && ret != MTy::Ptr(HeapKind::Str);
    let body = m.expr(&mut cx, &checked.root, !discarded);
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

    let mut program = Program {
        funcs: m
            .out
            .into_iter()
            .map(|f| f.expect("func lowered"))
            .collect(),
        entry: FuncId(0),
        layouts: m.layouts,
        sigs: m.sigs,
        data: m.data,
    };
    insert_rc(&mut program);
    Ok(program)
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
fn first_use(e: &hir::Expr, symbol: Symbol) -> Option<ExprId> {
    if matches!(&e.kind, ExprKind::Var { symbol: s, .. } if *s == symbol) {
        return Some(e.id);
    }
    let mut found = None;
    for_each_child(e, &mut |c| {
        if found.is_none() {
            found = first_use(c, symbol);
        }
    });
    found
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
    data: Vec<Vec<u8>>,
}

struct FnCx {
    subst: Subst,
    locals: HashMap<Symbol, Local>,
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
            Ty::Number => MTy::Float,
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
                for (_, field) in ground_fields(row) {
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
    fn closure_value(&mut self, cx: &mut FnCx, target: Target, use_id: ExprId) -> Expr {
        let (id, ty) = self.specialize(cx, target, use_id);
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
            let mty = self.lower_ty(&ty);
            mparams.push((local, mty));
        }
        let ret = self.ground(ret_ty, &cx.subst);
        let env = if captures.is_empty() {
            None
        } else {
            Some(self.bind_env(&mut cx, target, ty, &captures, &capture_tys))
        };
        Func {
            params: mparams,
            env,
            ret: self.lower_ty(&ret),
            body: self.expr(&mut cx, body, true),
        }
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
        let local = cx.fresh();
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

    fn expr(&mut self, cx: &mut FnCx, e: &hir::Expr, tail: bool) -> Expr {
        match &e.kind {
            ExprKind::Unit => Expr::Const(Const::Unit),
            ExprKind::Number(n) => Expr::Const(Const::Float(*n)),
            ExprKind::Bool(b) => Expr::Const(Const::Bool(*b)),
            ExprKind::Var { symbol, .. } => {
                let function = Target::Named(*symbol);
                match cx.self_env {
                    Some((me, env)) if me == *symbol => Expr::Local(env),
                    _ if self.lambdas.contains_key(&function) => {
                        self.closure_value(cx, function, e.id)
                    }
                    _ => self.variable_value(cx, *symbol),
                }
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
                    None => Expr::Const(Const::Unit),
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
                        None => self.closure_value(cx, Target::Named(*symbol), value.id),
                    };
                }
                if let Some(rest) = rest {
                    self.instantiate_binding(cx, *symbol, rest);
                }
                let value = self.expr(cx, value, false);
                let local = cx.fresh();
                cx.locals.insert(*symbol, local);
                let rest = match rest {
                    Some(rest) => self.expr(cx, rest, tail),
                    None => Expr::Local(local),
                };
                Expr::Let(local, Box::new(value), Box::new(rest))
            }
            ExprKind::Bin { op, lhs, rhs } => {
                let a = Box::new(self.expr(cx, lhs, false));
                let b = Box::new(self.expr(cx, rhs, false));
                match op {
                    BinOp::Add => Expr::BinFloat(FloatOp::Add, a, b),
                    BinOp::Sub => Expr::BinFloat(FloatOp::Sub, a, b),
                    BinOp::Mul => Expr::BinFloat(FloatOp::Mul, a, b),
                    BinOp::Div => Expr::BinFloat(FloatOp::Div, a, b),
                    BinOp::Lt => Expr::Cmp(CmpOp::Lt, a, b),
                    BinOp::Lte => Expr::Cmp(CmpOp::Le, a, b),
                    BinOp::Gt => Expr::Cmp(CmpOp::Gt, a, b),
                    BinOp::Gte => Expr::Cmp(CmpOp::Ge, a, b),
                }
            }
            ExprKind::Func { .. } => self.closure_value(cx, Target::Anon(e.id), e.id),
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
            ExprKind::Tag { .. } | ExprKind::Match { .. } => {
                unreachable!("the checker rejects variants until variant typing lands")
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
                match borrowed {
                    Some(local) => Expr::Field(local, index),
                    None => {
                        let rec = cx.fresh();
                        let source = self.expr(cx, record, false);
                        Expr::Let(rec, Box::new(source), Box::new(Expr::Field(rec, index)))
                    }
                }
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
        Expr::TailCall(target, args)
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
