use std::collections::{BTreeMap, HashMap};

use crate::mir::*;

#[derive(Debug, Clone, PartialEq)]
pub struct VerifyError {
    pub func: FuncId,
    pub kind: ErrorKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ErrorKind {
    TypeMismatch { expected: MTy, found: MTy },
    NotNumeric(MTy),
    NotAPointer(MTy),
    NotAClosure(MTy),
    NotARecord(MTy),
    NotAVariant(MTy),
    NotAString(MTy),
    ArityMismatch { expected: usize, found: usize },
    UnboundLocal(Local),
    DuplicateLocal(Local),
    UseAfterDrop(Local),
    UseAfterMove(Local),
    Leak(Local),
    BranchOwnershipMismatch(Local),
    UnknownFunc(FuncId),
    UnknownLayout(LayoutId),
    UnknownSig(SigId),
    UnknownData(DataId),
    UnknownForeign(ForeignId),
    BadFieldIndex(usize),
    BadCapture(usize),
    BadTag(u32),
    NotUnique(Local),
    NotAToken(Local),
    ReuseSizeMismatch { from: LayoutId, to: LayoutId },
    DuplicateSwitchArm(u32),
    TailCallNotInTail,
    UnexpectedEnv(FuncId),
    MissingEnv(FuncId),
    EnvSigMismatch(SigId),
    BadEntry,
}

pub fn verify(program: &Program) -> Result<(), Vec<VerifyError>> {
    let mut errors = Vec::new();
    match program.funcs.get(program.entry.0 as usize) {
        Some(f) if f.params.is_empty() && f.env.is_none() => {}
        _ => errors.push(VerifyError {
            func: program.entry,
            kind: ErrorKind::BadEntry,
        }),
    }
    for (i, func) in program.funcs.iter().enumerate() {
        let mut checker = Checker {
            program,
            id: FuncId(i as u32),
            func,
            errors: &mut errors,
            types: HashMap::new(),
            own: HashMap::new(),
        };
        checker.run();
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Own {
    Live(u32),
    Token,
    Dropped,
    Moved,
}

impl Own {
    fn agrees_with(self, other: Own) -> bool {
        match (self, other) {
            (Own::Live(a), Own::Live(b)) => a == b,
            (Own::Token, Own::Token) => true,
            (Own::Live(_) | Own::Token, _) | (_, Own::Live(_) | Own::Token) => false,
            _ => true,
        }
    }
}

/// `Bad` marks an expression whose error was already reported.
#[derive(Clone, Copy, PartialEq)]
enum Ty {
    Val(MTy),
    Never,
    Bad,
}

type OwnMap = HashMap<Local, Own>;

struct Checker<'a> {
    program: &'a Program,
    id: FuncId,
    func: &'a Func,
    errors: &'a mut Vec<VerifyError>,
    types: HashMap<Local, MTy>,
    own: OwnMap,
}

impl<'a> Checker<'a> {
    fn err(&mut self, kind: ErrorKind) -> Ty {
        self.errors.push(VerifyError {
            func: self.id,
            kind,
        });
        Ty::Bad
    }

    fn run(&mut self) {
        if let Some(env) = &self.func.env {
            match self.program.sigs.get(env.sig.0 as usize) {
                None => {
                    self.err(ErrorKind::UnknownSig(env.sig));
                }
                Some(sig) => {
                    let params: Vec<MTy> = self.func.params.iter().map(|p| p.1).collect();
                    if sig.params != params || sig.ret != self.func.ret {
                        self.err(ErrorKind::EnvSigMismatch(env.sig));
                    }
                }
            }
            self.bind(env.local, MTy::Ptr(HeapKind::Closure(env.sig)));
        }
        for &(local, ty) in &self.func.params {
            self.bind(local, ty);
        }
        let body = self.expr(&self.func.body, true);
        self.expect(body, self.func.ret);
        if body != Ty::Never {
            self.report_leaks(self.own.keys().copied().collect());
        }
    }

    fn report_leaks(&mut self, mut locals: Vec<Local>) {
        locals.sort();
        for local in locals {
            if matches!(self.own.get(&local), Some(Own::Live(_) | Own::Token)) {
                self.err(ErrorKind::Leak(local));
            }
        }
    }

    fn bind(&mut self, local: Local, ty: MTy) {
        if self.types.insert(local, ty).is_some() {
            self.err(ErrorKind::DuplicateLocal(local));
        }
        if ty.is_ptr() {
            self.own.insert(local, Own::Live(1));
        }
    }

    fn expect(&mut self, found: Ty, expected: MTy) {
        if let Ty::Val(found) = found
            && found != expected
        {
            self.err(ErrorKind::TypeMismatch { expected, found });
        }
    }

    fn unify(&mut self, a: Ty, b: Ty) -> Ty {
        match (a, b) {
            (Ty::Bad, _) | (_, Ty::Bad) => Ty::Bad,
            (Ty::Never, other) | (other, Ty::Never) => other,
            (Ty::Val(a), Ty::Val(b)) if a == b => Ty::Val(a),
            (Ty::Val(expected), Ty::Val(found)) => {
                self.err(ErrorKind::TypeMismatch { expected, found })
            }
        }
    }

    /// Type of `local` if it is bound and, for pointers, still owned.
    fn borrow(&mut self, local: Local) -> Option<MTy> {
        let Some(&ty) = self.types.get(&local) else {
            self.err(ErrorKind::UnboundLocal(local));
            return None;
        };
        match self.own.get(&local) {
            Some(Own::Dropped) => {
                self.err(ErrorKind::UseAfterDrop(local));
                None
            }
            Some(Own::Moved | Own::Token) => {
                self.err(ErrorKind::UseAfterMove(local));
                None
            }
            _ => Some(ty),
        }
    }

    /// Consumes a reuse token, returning the layout of the cell it came from.
    fn take_token(&mut self, local: Local) -> Option<LayoutId> {
        let kind = match (self.types.get(&local), self.own.get(&local)) {
            (None, _) => {
                self.err(ErrorKind::UnboundLocal(local));
                return None;
            }
            (Some(MTy::Ptr(HeapKind::Variant(l) | HeapKind::List(l))), Some(Own::Token)) => {
                Some(*l)
            }
            _ => None,
        };
        match kind {
            Some(l) => {
                self.own.insert(local, Own::Moved);
                Some(l)
            }
            None => {
                self.err(ErrorKind::NotAToken(local));
                None
            }
        }
    }

    fn consume(&mut self, local: Local, how: Own) -> Option<MTy> {
        let ty = self.borrow(local)?;
        if let Some(Own::Live(n)) = self.own.get(&local).copied() {
            let next = if n > 1 { Own::Live(n - 1) } else { how };
            self.own.insert(local, next);
        }
        Some(ty)
    }

    fn borrow_ptr(&mut self, local: Local) -> Option<HeapKind> {
        match self.borrow(local)? {
            MTy::Ptr(kind) => Some(kind),
            other => {
                self.err(ErrorKind::NotAPointer(other));
                None
            }
        }
    }

    fn borrow_str(&mut self, local: Local) -> Option<()> {
        match self.borrow(local)? {
            MTy::Ptr(HeapKind::Str) => Some(()),
            other => {
                self.err(ErrorKind::NotAString(other));
                None
            }
        }
    }

    fn layout(&mut self, id: LayoutId) -> Option<&'a Layout> {
        let layout = self.program.layouts.get(id.0 as usize);
        if layout.is_none() {
            self.err(ErrorKind::UnknownLayout(id));
        }
        layout
    }

    fn record_fields(&mut self, id: LayoutId) -> Option<&'a [MTy]> {
        match self.layout(id)? {
            Layout::Record(fields) => Some(fields),
            Layout::Variant(_) => {
                self.err(ErrorKind::NotARecord(MTy::Ptr(HeapKind::Variant(id))));
                None
            }
        }
    }

    fn variant_tags(&mut self, id: LayoutId) -> Option<&'a BTreeMap<u32, Vec<MTy>>> {
        match self.layout(id)? {
            Layout::Variant(tags) => Some(tags),
            Layout::Record(_) => {
                self.err(ErrorKind::NotAVariant(MTy::Ptr(HeapKind::Record(id))));
                None
            }
        }
    }

    fn args(&mut self, args: &[Expr], expected: Option<&[MTy]>) {
        if let Some(expected) = expected
            && expected.len() != args.len()
        {
            self.err(ErrorKind::ArityMismatch {
                expected: expected.len(),
                found: args.len(),
            });
        }
        for (i, arg) in args.iter().enumerate() {
            let ty = self.expr(arg, false);
            if let Some(&want) = expected.and_then(|e| e.get(i)) {
                self.expect(ty, want);
            }
        }
    }

    fn call(&mut self, signature: Option<(Vec<MTy>, MTy)>, args: &[Expr]) -> Ty {
        self.args(args, signature.as_ref().map(|s| s.0.as_slice()));
        signature.map_or(Ty::Bad, |s| Ty::Val(s.1))
    }

    fn direct_signature(&mut self, id: FuncId) -> Option<(Vec<MTy>, MTy)> {
        let Some(func) = self.program.funcs.get(id.0 as usize) else {
            self.err(ErrorKind::UnknownFunc(id));
            return None;
        };
        if func.env.is_some() {
            self.err(ErrorKind::UnexpectedEnv(id));
            return None;
        }
        Some((func.params.iter().map(|p| p.1).collect(), func.ret))
    }

    fn closure_signature(&mut self, closure: &Expr) -> Option<(Vec<MTy>, MTy)> {
        match self.expr(closure, false) {
            Ty::Val(MTy::Ptr(HeapKind::Closure(sig))) => {
                let Some(sig) = self.program.sigs.get(sig.0 as usize) else {
                    self.err(ErrorKind::UnknownSig(sig));
                    return None;
                };
                Some((sig.params.clone(), sig.ret))
            }
            Ty::Val(other) => {
                self.err(ErrorKind::NotAClosure(other));
                None
            }
            _ => None,
        }
    }

    fn branch(&mut self, block: &Block, tail: bool, before: &OwnMap) -> (Ty, OwnMap) {
        self.own = before.clone();
        let ty = self.expr(block, tail);
        (ty, std::mem::take(&mut self.own))
    }

    /// Every non-diverging branch must leave each outer local in the same
    /// ownership state, so ownership is consistent on every path.
    fn join(&mut self, before: &OwnMap, branches: Vec<(Ty, OwnMap)>) -> Ty {
        let mut result = Ty::Never;
        let mut chosen: Option<OwnMap> = None;
        for (ty, state) in branches {
            result = self.unify(result, ty);
            if ty == Ty::Never {
                continue;
            }
            match &chosen {
                None => chosen = Some(state),
                Some(first) => {
                    let mut locals: Vec<Local> = before.keys().copied().collect();
                    locals.sort();
                    for local in locals {
                        if !first[&local].agrees_with(state[&local]) {
                            self.err(ErrorKind::BranchOwnershipMismatch(local));
                        }
                    }
                }
            }
        }
        self.own = chosen.unwrap_or_else(|| before.clone());
        result
    }

    fn expr(&mut self, e: &Expr, tail: bool) -> Ty {
        match e {
            Expr::Const(c) => Ty::Val(match c {
                Const::Int(_) => MTy::Int,
                Const::Float(_) => MTy::Float,
                Const::Bool(_) => MTy::Bool,
                Const::Unit => MTy::Unit,
            }),
            Expr::Local(x) => self.consume(*x, Own::Moved).map_or(Ty::Bad, Ty::Val),
            Expr::Let(..) => {
                let mut bound = Vec::new();
                let mut cursor = e;
                let result = loop {
                    let Expr::Let(x, rhs, body) = cursor else {
                        break self.expr(cursor, tail);
                    };
                    let rhs = self.expr(rhs, false);
                    let Ty::Val(ty) = rhs else { break rhs };
                    self.bind(*x, ty);
                    bound.push(*x);
                    cursor = body;
                };
                for x in bound.into_iter().rev() {
                    if result != Ty::Never {
                        self.report_leaks(vec![x]);
                    }
                    self.own.remove(&x);
                }
                result
            }
            Expr::BinInt(_, a, b) => self.binary(a, b, MTy::Int, MTy::Int),
            Expr::BinFloat(_, a, b) => self.binary(a, b, MTy::Float, MTy::Float),
            Expr::IntToFloat(value) => {
                let value = self.expr(value, false);
                self.expect(value, MTy::Int);
                Ty::Val(MTy::Float)
            }
            Expr::FloatFn(function, value) => {
                let value = self.expr(value, false);
                self.expect(value, MTy::Float);
                Ty::Val(match function {
                    FloatFn::Sqrt => MTy::Float,
                    FloatFn::Truncate => MTy::Int,
                })
            }
            Expr::Cmp(_, a, b) => {
                let a = self.expr(a, false);
                let b = self.expr(b, false);
                match a {
                    Ty::Val(t @ (MTy::Int | MTy::Float)) => self.expect(b, t),
                    Ty::Val(other) => {
                        self.err(ErrorKind::NotNumeric(other));
                    }
                    _ => {}
                }
                Ty::Val(MTy::Bool)
            }
            Expr::If(cond, then, otherwise) => {
                let c = self.expr(cond, false);
                self.expect(c, MTy::Bool);
                let before = self.own.clone();
                let t = self.branch(then, tail, &before);
                let o = self.branch(otherwise, tail, &before);
                self.join(&before, vec![t, o])
            }
            Expr::Switch(scrutinee, arms, default) => {
                let tags = match self.borrow_ptr(*scrutinee) {
                    Some(HeapKind::Variant(l) | HeapKind::List(l)) => self.variant_tags(l),
                    Some(other) => {
                        self.err(ErrorKind::NotAVariant(MTy::Ptr(other)));
                        None
                    }
                    None => None,
                };
                let before = self.own.clone();
                let mut seen = Vec::new();
                let mut branches = Vec::new();
                for (tag, block) in arms {
                    if seen.contains(tag) {
                        self.err(ErrorKind::DuplicateSwitchArm(*tag));
                    } else if tags.is_some_and(|t| !t.contains_key(tag)) {
                        self.err(ErrorKind::BadTag(*tag));
                    }
                    seen.push(*tag);
                    branches.push(self.branch(block, tail, &before));
                }
                branches.push(self.branch(default, tail, &before));
                self.join(&before, branches)
            }
            Expr::CallDirect(f, args) => {
                let sig = self.direct_signature(*f);
                self.call(sig, args)
            }
            Expr::CallClosure(closure, args) => {
                let sig = self.closure_signature(closure);
                self.call(sig, args)
            }
            Expr::TailCall(callee, args) => {
                if !tail {
                    self.err(ErrorKind::TailCallNotInTail);
                }
                let sig = match callee {
                    Callee::Direct(f) => self.direct_signature(*f),
                    Callee::Closure(closure) => self.closure_signature(closure),
                };
                if let Ty::Val(ret) = self.call(sig, args) {
                    self.expect(Ty::Val(ret), self.func.ret);
                }
                Ty::Never
            }
            Expr::MakeClosure(f, captures) => {
                let Some(target) = self.program.funcs.get(f.0 as usize) else {
                    return self.err(ErrorKind::UnknownFunc(*f));
                };
                let Some(env) = &target.env else {
                    return self.err(ErrorKind::MissingEnv(*f));
                };
                self.args(captures, Some(&env.captures));
                Ty::Val(MTy::Ptr(HeapKind::Closure(env.sig)))
            }
            Expr::Capture(i) => {
                let Some(env) = &self.func.env else {
                    return self.err(ErrorKind::MissingEnv(self.id));
                };
                let (local, ty) = (env.local, env.captures.get(*i).copied());
                if self.borrow(local).is_none() {
                    return Ty::Bad;
                }
                ty.map_or_else(|| self.err(ErrorKind::BadCapture(*i)), Ty::Val)
            }
            Expr::AllocRecord(layout, fields) => {
                let expected = self.record_fields(*layout);
                self.args(fields, expected);
                Ty::Val(MTy::Ptr(HeapKind::Record(*layout)))
            }
            Expr::Field(x, i) => match self.borrow_ptr(*x) {
                Some(HeapKind::Record(l)) => match self.record_fields(l) {
                    Some(fields) => fields
                        .get(*i)
                        .map_or_else(|| self.err(ErrorKind::BadFieldIndex(*i)), |&t| Ty::Val(t)),
                    None => Ty::Bad,
                },
                Some(other) => self.err(ErrorKind::NotARecord(MTy::Ptr(other))),
                None => Ty::Bad,
            },
            Expr::AllocVariant(layout, tag, fields) => {
                let tags = self.variant_tags(*layout);
                let expected = match tags.map(|t| t.get(tag)) {
                    Some(Some(payload)) => Some(payload.as_slice()),
                    Some(None) => {
                        self.err(ErrorKind::BadTag(*tag));
                        None
                    }
                    None => None,
                };
                self.args(fields, expected);
                Ty::Val(MTy::Ptr(HeapKind::Variant(*layout)))
            }
            Expr::Unpack(x, tag, binds, body) => {
                let payload = match self.borrow_ptr(*x) {
                    Some(HeapKind::Variant(l) | HeapKind::List(l)) => {
                        self.variant_tags(l).and_then(|tags| {
                            let found = tags.get(tag);
                            if found.is_none() {
                                self.err(ErrorKind::BadTag(*tag));
                            }
                            found
                        })
                    }
                    Some(other) => {
                        self.err(ErrorKind::NotAVariant(MTy::Ptr(other)));
                        None
                    }
                    None => None,
                };
                if self.own.get(x) != Some(&Own::Live(1)) {
                    self.err(ErrorKind::NotUnique(*x));
                } else {
                    self.own.insert(*x, Own::Token);
                }
                if let Some(payload) = payload {
                    if payload.len() != binds.len() {
                        self.err(ErrorKind::ArityMismatch {
                            expected: payload.len(),
                            found: binds.len(),
                        });
                    }
                    for (bind, ty) in binds.iter().zip(payload) {
                        self.bind(*bind, *ty);
                    }
                }
                let result = self.expr(body, tail);
                if result != Ty::Never {
                    self.report_leaks(binds.clone());
                }
                for bind in binds {
                    self.own.remove(bind);
                }
                result
            }
            Expr::ReuseVariant(x, layout, tag, fields) => {
                let tags = self.variant_tags(*layout);
                let expected = match tags.map(|t| t.get(tag)) {
                    Some(Some(payload)) => Some(payload.as_slice()),
                    Some(None) => {
                        self.err(ErrorKind::BadTag(*tag));
                        None
                    }
                    None => None,
                };
                self.args(fields, expected);
                if let Some(from) = self.take_token(*x)
                    && let (Some(Layout::Variant(old)), Some(to)) =
                        (self.program.layouts.get(from.0 as usize), tags)
                    && max_payload(old) != max_payload(to)
                {
                    self.err(ErrorKind::ReuseSizeMismatch { from, to: *layout });
                }
                Ty::Val(MTy::Ptr(HeapKind::Variant(*layout)))
            }
            Expr::ReuseRecord(x, layout, fields) => self.reuse_record(*x, *layout, fields),
            Expr::Free(x) => {
                self.take_token(*x);
                Ty::Val(MTy::Unit)
            }
            Expr::Payload(x, tag, i) => match self.borrow_ptr(*x) {
                Some(HeapKind::Variant(l) | HeapKind::List(l)) => {
                    let Some(tags) = self.variant_tags(l) else {
                        return Ty::Bad;
                    };
                    let Some(payload) = tags.get(tag) else {
                        return self.err(ErrorKind::BadTag(*tag));
                    };
                    payload
                        .get(*i)
                        .map_or_else(|| self.err(ErrorKind::BadFieldIndex(*i)), |&t| Ty::Val(t))
                }
                Some(other) => self.err(ErrorKind::NotAVariant(MTy::Ptr(other))),
                None => Ty::Bad,
            },
            Expr::StrLit(d) => {
                if self.program.data.get(d.0 as usize).is_none() {
                    return self.err(ErrorKind::UnknownData(*d));
                }
                Ty::Val(MTy::Ptr(HeapKind::Str))
            }
            Expr::StrEq(a, b) => {
                let (a, b) = (self.borrow_str(*a), self.borrow_str(*b));
                if a.is_none() || b.is_none() {
                    return Ty::Bad;
                }
                Ty::Val(MTy::Bool)
            }
            Expr::StrLen(s) | Expr::StrChars(s) => {
                if self.borrow_str(*s).is_none() {
                    return Ty::Bad;
                }
                Ty::Val(MTy::Int)
            }
            Expr::StrByte(s, i) | Expr::StrChar(s, i) => {
                let (s, i) = (self.borrow_str(*s), self.borrow(*i));
                if let Some(found) = i {
                    self.expect(Ty::Val(found), MTy::Int);
                }
                if s.is_none() || i.is_none() {
                    return Ty::Bad;
                }
                Ty::Val(if matches!(e, Expr::StrChar(..)) {
                    MTy::Ptr(HeapKind::Str)
                } else {
                    MTy::Int
                })
            }
            Expr::Write(write) => {
                match write {
                    Write::Number(value) => match self.expr(value, false) {
                        Ty::Val(MTy::Int | MTy::Float) | Ty::Never | Ty::Bad => {}
                        found => self.expect(found, MTy::Float),
                    },
                    Write::Str(x) => {
                        self.borrow_str(*x);
                    }
                    Write::Lit(d) if self.program.data.get(d.0 as usize).is_none() => {
                        return self.err(ErrorKind::UnknownData(*d));
                    }
                    Write::Lit(_) | Write::End => {}
                }
                Ty::Val(MTy::Unit)
            }
            Expr::CallForeign(f, args) => {
                let Some(foreign) = self.program.foreign.get(f.0 as usize) else {
                    return self.err(ErrorKind::UnknownForeign(*f));
                };
                if foreign.params.len() != args.len() {
                    self.err(ErrorKind::ArityMismatch {
                        expected: foreign.params.len(),
                        found: args.len(),
                    });
                }
                for (&arg, &want) in args.iter().zip(&foreign.params) {
                    if let Some(found) = self.borrow(arg) {
                        self.expect(Ty::Val(found), want);
                    }
                }
                Ty::Val(foreign.ret)
            }
            Expr::Dup(x) => {
                if self.borrow_ptr(*x).is_none() {
                    return Ty::Bad;
                }
                if let Some(Own::Live(n)) = self.own.get(x).copied() {
                    self.own.insert(*x, Own::Live(n + 1));
                }
                Ty::Val(MTy::Unit)
            }
            Expr::Drop(x) => {
                if self.borrow_ptr(*x).is_none() {
                    return Ty::Bad;
                }
                self.consume(*x, Own::Dropped);
                Ty::Val(MTy::Unit)
            }
            Expr::Trap(_) => Ty::Never,
            Expr::Site(..) => Ty::Val(MTy::Unit),
        }
    }

    #[inline(never)]
    fn reuse_record(&mut self, x: Local, layout: LayoutId, fields: &[Expr]) -> Ty {
        let expected = self.record_fields(layout);
        self.args(fields, expected);
        match self.borrow_ptr(x) {
            Some(HeapKind::Record(from)) => {
                if self.record_fields(from) != expected {
                    self.err(ErrorKind::ReuseSizeMismatch { from, to: layout });
                }
            }
            Some(other) => {
                self.err(ErrorKind::NotARecord(MTy::Ptr(other)));
            }
            None => {}
        }
        self.consume(x, Own::Moved);
        Ty::Val(MTy::Ptr(HeapKind::Record(layout)))
    }

    fn binary(&mut self, a: &Expr, b: &Expr, operand: MTy, result: MTy) -> Ty {
        let a = self.expr(a, false);
        self.expect(a, operand);
        let b = self.expr(b, false);
        self.expect(b, operand);
        Ty::Val(result)
    }
}

fn max_payload(tags: &BTreeMap<u32, Vec<MTy>>) -> usize {
    tags.values().map(Vec::len).max().unwrap_or(0)
}
