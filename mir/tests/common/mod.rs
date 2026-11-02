#![allow(dead_code)]

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
