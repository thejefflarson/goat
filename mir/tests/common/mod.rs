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

pub const RECORD: LayoutId = LayoutId(0);
pub const VARIANT: LayoutId = LayoutId(1);

pub fn record_ty() -> MTy {
    MTy::Ptr(HeapKind::Record(RECORD))
}

pub fn alloc_record(n: i64) -> Expr {
    Expr::AllocRecord(RECORD, vec![int(n)])
}
