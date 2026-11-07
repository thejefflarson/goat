#![allow(dead_code)]

use goat_checker::hir::Boundary;
use goat_mir::*;

pub fn int(n: i64) -> Expr {
    Expr::Const(Const::Int(n))
}

pub fn local(n: u32) -> Expr {
    Expr::Local(Local(n))
}

pub fn let_(n: u32, rhs: Expr, body: Expr) -> Expr {
    Expr::Let(Local(n), Box::new(rhs), Box::new(body))
}

pub fn add(a: Expr, b: Expr) -> Expr {
    Expr::BinInt(IntOp::Add, Box::new(a), Box::new(b))
}

pub fn func(ret: MTy, body: Expr) -> Func {
    Func {
        params: vec![],
        env: None,
        ret,
        body,
    }
}

pub fn program(funcs: Vec<Func>) -> Program {
    Program {
        funcs,
        entry: FuncId(0),
        layouts: vec![
            Layout::Record(vec![MTy::Int]),
            Layout::Variant(vec![vec![], vec![MTy::Int]]),
        ],
        sigs: vec![],
        data: vec![],
        foreign: vec![],
        interactive: None,
    }
}

pub fn float(x: f64) -> Expr {
    Expr::Const(Const::Float(x))
}

pub fn boolean(b: bool) -> Expr {
    Expr::Const(Const::Bool(b))
}

pub fn bin_float(op: FloatOp, a: Expr, b: Expr) -> Expr {
    Expr::BinFloat(op, Box::new(a), Box::new(b))
}

pub fn sub(a: Expr, b: Expr) -> Expr {
    Expr::BinInt(IntOp::Sub, Box::new(a), Box::new(b))
}

pub fn cmp(op: CmpOp, a: Expr, b: Expr) -> Expr {
    Expr::Cmp(op, Box::new(a), Box::new(b))
}

pub fn if_(c: Expr, t: Expr, e: Expr) -> Expr {
    Expr::If(Box::new(c), Box::new(t), Box::new(e))
}

pub fn call(f: u32, args: Vec<Expr>) -> Expr {
    Expr::CallDirect(FuncId(f), args)
}

pub fn func_with(params: Vec<(u32, MTy)>, ret: MTy, body: Expr) -> Func {
    Func {
        params: params.into_iter().map(|(n, t)| (Local(n), t)).collect(),
        env: None,
        ret,
        body,
    }
}

pub const RECORD: LayoutId = LayoutId(0);
pub const VARIANT: LayoutId = LayoutId(1);

pub fn record_ty() -> MTy {
    MTy::Ptr(HeapKind::Record(RECORD))
}

pub fn alloc_record(n: i64) -> Expr {
    Expr::AllocRecord(RECORD, vec![int(n)])
}

pub fn mul(a: Expr, b: Expr) -> Expr {
    Expr::BinInt(IntOp::Mul, Box::new(a), Box::new(b))
}

pub fn drop_(n: u32) -> Expr {
    Expr::Drop(Local(n))
}

pub fn call_closure(closure: Expr, args: Vec<Expr>) -> Expr {
    Expr::CallClosure(Box::new(closure), args)
}

pub fn closure_ty(sig: u32) -> MTy {
    MTy::Ptr(HeapKind::Closure(SigId(sig)))
}

/// A closure body whose environment is `env` and whose signature is `SigId(0)`.
pub fn closure_fn(
    params: Vec<(u32, MTy)>,
    env: u32,
    captures: Vec<MTy>,
    ret: MTy,
    body: Expr,
) -> Func {
    Func {
        env: Some(Env {
            local: Local(env),
            sig: SigId(0),
            captures,
        }),
        ..func_with(params, ret, body)
    }
}

pub const FNS: LayoutId = LayoutId(2);

/// Adds signature 0, `(sig_params) -> Int`, and a record of two such closures.
pub fn with_closures(mut p: Program, sig_params: Vec<MTy>) -> Program {
    p.sigs = vec![Sig {
        params: sig_params,
        ret: MTy::Int,
    }];
    p.layouts
        .push(Layout::Record(vec![closure_ty(0), closure_ty(0)]));
    p
}

/// A host that records every call it gets, in order, and answers `Unit` to
/// `forward` and `say`, twice its argument to `double`, and a fresh
/// `"<arg>!"` to `shout`.
#[derive(Default)]
pub struct Recorder {
    pub calls: Vec<(String, Vec<HostValue>)>,
}

impl Host for Recorder {
    fn signature(&self, _: &str, _: &str) -> Option<(Vec<Boundary>, Boundary)> {
        None
    }

    fn call(&mut self, _: &str, name: &str, args: &[HostValue]) -> Result<HostValue, String> {
        self.calls.push((name.to_string(), args.to_vec()));
        match (name, args) {
            ("forward" | "say", _) => Ok(HostValue::Unit),
            ("double", [HostValue::Number(x)]) => Ok(HostValue::Number(x * 2.0)),
            ("shout", [HostValue::Str(s)]) => Ok(HostValue::Str(format!("{s}!"))),
            ("greet", []) => Ok(HostValue::Str("hi".into())),
            _ => Err(format!("unexpected call to {name}")),
        }
    }
}

pub fn foreign_fn(name: &str, params: Vec<MTy>, ret: MTy) -> ForeignFn {
    ForeignFn {
        module: "test".into(),
        name: name.into(),
        params,
        ret,
    }
}
