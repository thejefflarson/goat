use std::collections::BTreeMap;

use goat_mir::*;

/// Fill each function's `locals` by walking its body, for hand-built MIR whose
/// binder types no one recorded.
pub fn infer_locals(program: &mut Program) {
    let tables: Vec<_> = program
        .funcs
        .iter()
        .map(|func| {
            let mut cx = Infer {
                program,
                func,
                types: BTreeMap::new(),
            };
            cx.ty(&func.body);
            cx.types
        })
        .collect();
    for (func, table) in program.funcs.iter_mut().zip(tables) {
        func.locals = table;
    }
}

struct Infer<'p> {
    program: &'p Program,
    func: &'p Func,
    types: BTreeMap<Local, MTy>,
}

impl Infer<'_> {
    fn local(&self, x: Local) -> Option<MTy> {
        self.func
            .local_ty(x)
            .or_else(|| self.types.get(&x).copied())
    }

    fn all(&mut self, es: &[Expr]) {
        es.iter().for_each(|e| {
            self.ty(e);
        });
    }

    fn payload_tys(&self, x: Local, tag: u32) -> Option<Vec<MTy>> {
        let Some(MTy::Ptr(HeapKind::Variant(l) | HeapKind::List(l))) = self.local(x) else {
            return None;
        };
        match self.program.layouts.get(l.0 as usize)? {
            Layout::Variant(tags) => tags.get(tag as usize).cloned(),
            Layout::Record(_) => None,
        }
    }

    fn ty(&mut self, e: &Expr) -> Option<MTy> {
        let program = self.program;
        match e {
            Expr::Const(c) => Some(match c {
                Const::Int(_) => MTy::Int,
                Const::Float(_) => MTy::Float,
                Const::Bool(_) => MTy::Bool,
                Const::Unit => MTy::Unit,
            }),
            Expr::Local(x) => self.local(*x),
            Expr::Let(..) => {
                let mut cursor = e;
                while let Expr::Let(x, rhs, body) = cursor {
                    if let Some(t) = self.ty(rhs) {
                        self.types.insert(*x, t);
                    }
                    cursor = body;
                }
                self.ty(cursor)
            }
            Expr::BinInt(_, a, b) => {
                self.ty(a);
                self.ty(b);
                Some(MTy::Int)
            }
            Expr::BinFloat(_, a, b) => {
                self.ty(a);
                self.ty(b);
                Some(MTy::Float)
            }
            Expr::IntToFloat(value) => {
                self.ty(value);
                Some(MTy::Float)
            }
            Expr::Cmp(_, a, b) => {
                self.ty(a);
                self.ty(b);
                Some(MTy::Bool)
            }
            Expr::If(c, t, o) => {
                self.ty(c);
                let then = self.ty(t);
                then.or(self.ty(o))
            }
            Expr::Switch(_, arms, default) => {
                let mut found = None;
                for (_, block) in arms {
                    found = found.or(self.ty(block));
                }
                found.or(self.ty(default))
            }
            Expr::CallDirect(f, args) => {
                self.all(args);
                program.funcs.get(f.0 as usize).map(|f| f.ret)
            }
            Expr::CallClosure(c, args) => {
                let closure = self.ty(c);
                self.all(args);
                match closure {
                    Some(MTy::Ptr(HeapKind::Closure(sig))) => {
                        program.sigs.get(sig.0 as usize).map(|s| s.ret)
                    }
                    _ => None,
                }
            }
            Expr::TailCall(callee, args) => {
                if let Callee::Closure(c) = callee {
                    self.ty(c);
                }
                self.all(args);
                None
            }
            Expr::MakeClosure(f, captures) => {
                self.all(captures);
                let env = program.funcs.get(f.0 as usize)?.env.as_ref()?;
                Some(MTy::Ptr(HeapKind::Closure(env.sig)))
            }
            Expr::Capture(i) => self.func.env.as_ref()?.captures.get(*i).copied(),
            Expr::AllocRecord(layout, fields) | Expr::ReuseRecord(_, layout, fields) => {
                self.all(fields);
                Some(MTy::Ptr(HeapKind::Record(*layout)))
            }
            Expr::Field(x, i) => match self.local(*x) {
                Some(MTy::Ptr(HeapKind::Record(l))) => match program.layouts.get(l.0 as usize) {
                    Some(Layout::Record(fields)) => fields.get(*i).copied(),
                    _ => None,
                },
                _ => None,
            },
            Expr::AllocVariant(layout, _, fields) | Expr::ReuseVariant(_, layout, _, fields) => {
                self.all(fields);
                Some(MTy::Ptr(HeapKind::Variant(*layout)))
            }
            Expr::Payload(x, tag, i) => self.payload_tys(*x, *tag)?.get(*i).copied(),
            Expr::Unpack(x, tag, binds, body) => {
                if let Some(payload) = self.payload_tys(*x, *tag) {
                    for (bind, ty) in binds.iter().zip(payload) {
                        self.types.insert(*bind, ty);
                    }
                }
                self.ty(body)
            }
            Expr::Free(_) | Expr::Dup(_) | Expr::Drop(_) => Some(MTy::Unit),
            Expr::StrLit(_) => Some(MTy::Ptr(HeapKind::Str)),
            Expr::StrEq(..) => Some(MTy::Bool),
            Expr::Write(write) => {
                if let Write::Number(value) = write {
                    self.ty(value);
                }
                Some(MTy::Unit)
            }
            Expr::CallForeign(f, _) => program.foreign.get(f.0 as usize).map(|f| f.ret),
            Expr::Trap(_) => None,
            Expr::Site(..) => Some(MTy::Unit),
        }
    }
}
