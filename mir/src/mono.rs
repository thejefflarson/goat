//! Monomorphization: checked HIR to ground-typed MIR, one `Func` per
//! `(binding, ground type)` specialization.

use crate::mir::*;
use goat_checker::Checked;
use goat_checker::hir::{self, BinOp, ExprKind, Param, Symbol};
use goat_checker::infer::Typed;
use goat_checker::ty::{Row, Ty, TypeVar};
use std::collections::HashMap;

type Subst = HashMap<TypeVar, Ty>;

pub fn mono(checked: &Checked) -> Program {
    let mut funcs = HashMap::new();
    collect_funcs(&checked.root, &mut funcs);
    let mut m = Mono {
        typed: &checked.typed,
        funcs,
        specs: Vec::new(),
        out: vec![None],
        work: Vec::new(),
        sigs: Vec::new(),
    };

    let mut cx = FnCx::new(Subst::new());
    let root_ty = m.ground(&checked.typed.root_ty, &cx.subst);
    let ret = m.lower_ty(&root_ty);
    let body = m.expr(&mut cx, &checked.root);
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

    Program {
        funcs: m
            .out
            .into_iter()
            .map(|f| f.expect("func lowered"))
            .collect(),
        entry: FuncId(0),
        layouts: Vec::new(),
        sigs: m.sigs,
        data: Vec::new(),
    }
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
}

struct FnCx {
    subst: Subst,
    locals: HashMap<Symbol, Local>,
    next: u32,
}

impl FnCx {
    fn new(subst: Subst) -> FnCx {
        FnCx {
            subst,
            locals: HashMap::new(),
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

    fn ground_row(&self, row: &Row, subst: &Subst) -> Row {
        match row {
            Row::Empty | Row::Var(_) => Row::Empty,
            Row::Extend { label, field, rest } => Row::Extend {
                label: label.clone(),
                field: Box::new(self.ground(field, subst)),
                rest: Box::new(self.ground_row(rest, subst)),
            },
        }
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
            Ty::Str | Ty::Record(_) => unsupported("strings and records"),
            Ty::Var(_) => unreachable!("type variable survived grounding"),
        }
    }

    fn specialize(&mut self, cx: &FnCx, symbol: Symbol, use_id: hir::ExprId) -> FuncId {
        let use_ty = self.ground(&self.typed.node_types[&use_id], &cx.subst);
        if let Some((_, _, id)) = self
            .specs
            .iter()
            .find(|(s, t, _)| *s == symbol && *t == use_ty)
        {
            return *id;
        }
        let id = FuncId(self.out.len() as u32);
        self.out.push(None);
        self.specs.push((symbol, use_ty.clone(), id));
        let mut subst = Subst::new();
        match_ty(&self.typed.schemes[&symbol].ty, &use_ty, &mut subst);
        self.work.push((id, symbol, subst));
        id
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
            mparams.push((local, self.lower_ty(&ty)));
        }
        let ret = self.ground(ret_ty, &cx.subst);
        Func {
            params: mparams,
            env: None,
            ret: self.lower_ty(&ret),
            body: self.expr(&mut cx, body),
        }
    }

    fn expr(&mut self, cx: &mut FnCx, e: &hir::Expr) -> Expr {
        match &e.kind {
            ExprKind::Unit => Expr::Const(Const::Unit),
            ExprKind::Number(n) => Expr::Const(Const::Float(*n)),
            ExprKind::Bool(b) => Expr::Const(Const::Bool(*b)),
            ExprKind::Var { symbol, .. } => match cx.locals.get(symbol) {
                Some(local) => Expr::Local(*local),
                None => unsupported("function values and captured variables"),
            },
            ExprKind::App { callee, args } => {
                let ExprKind::Var { symbol, .. } = &callee.kind else {
                    unsupported("calling a non-variable");
                };
                if !self.funcs.contains_key(symbol) {
                    unsupported("calling a function value");
                }
                let id = self.specialize(cx, *symbol, callee.id);
                let args = args.iter().map(|a| self.expr(cx, a)).collect();
                Expr::CallDirect(id, args)
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => Expr::If(
                Box::new(self.expr(cx, cond)),
                Box::new(self.expr(cx, then_branch)),
                Box::new(match else_branch {
                    Some(e) => self.expr(cx, e),
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
                        Some(rest) => self.expr(cx, rest),
                        None => unsupported("function values"),
                    };
                }
                let value = self.expr(cx, value);
                let local = cx.fresh();
                cx.locals.insert(*symbol, local);
                let rest = match rest {
                    Some(rest) => self.expr(cx, rest),
                    None => Expr::Local(local),
                };
                Expr::Let(local, Box::new(value), Box::new(rest))
            }
            ExprKind::Bin { op, lhs, rhs } => {
                let a = Box::new(self.expr(cx, lhs));
                let b = Box::new(self.expr(cx, rhs));
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
            ExprKind::Func { .. } => unsupported("function values"),
            ExprKind::Str(_) => unsupported("strings"),
            ExprKind::Record { .. } | ExprKind::Field { .. } => unsupported("records"),
        }
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
        (Ty::Record(_), _) => unsupported("records"),
        (t, a) => debug_assert_eq!(t, a, "template does not match use site"),
    }
}

#[cold]
fn unsupported(what: &str) -> ! {
    panic!("mono: {what} not supported yet")
}
