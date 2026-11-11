//! Reference-count insertion: the Perceus "owned parameters" pass over RC-free
//! MIR. Mono emits MIR with no `Dup` or `Drop`; this pass adds exactly the ones
//! that make every owned pointer be consumed once on every path.
//!
//! The invariants it relies on and maintains:
//!
//! - A pointer-typed local (parameter, `env`, `Let` or `Unpack` binder) owns one
//!   reference. A by-value `Local(x)` use moves that reference.
//! - The last use of `x` on a path moves it; an earlier use is preceded by a
//!   `Dup`. "Last" is decided by backward liveness, one function at a time.
//! - `Field`, `Payload`, `Capture` and a `Switch` scrutinee borrow their
//!   operand and never move it. When the borrow is the last use, the `Drop` is
//!   deferred to the end of the enclosing statement (the function body, a
//!   branch, or the gap between a `Let`'s value and its body) so the loaded
//!   value is computed first.
//! - An owned local that is dead on entry to a branch is dropped at the start
//!   of that branch, so every branch leaves each outer local in the same state.
//! - A tail call evaluates its callee and arguments into temporaries before the
//!   deferred drops, because nothing can run after the call.
//! - Evaluation order is preserved and no expression is removed or
//!   duplicated, so effectful calls (even `Unit`-typed ones) are untouched.
//!   `insert_rc` checks it: each function's `effects` (foreign calls and
//!   writes, in order) must come out as it went in.
//! - `CallForeign` borrows its arguments for the call, like `Write::Str`; a
//!   pointer it returns is a fresh owned reference.
//! - Immortal objects (`rc == u32::MAX`) get the same `Dup`/`Drop` nodes as any
//!   other pointer; every backend treats those as no-ops on the sentinel, which
//!   keeps the verifier's exactly-once rule uniform.
//! - `ReuseRecord` moves its base after its fields, like a by-value use of it.
//! - `Unpack`, `ReuseVariant` and `Free` (in-place reuse) are not produced by
//!   mono and are passed through with their operand treated as consumed.

use std::collections::BTreeSet;

use crate::mir::*;

type Set = BTreeSet<Local>;

/// Insert `Dup` and `Drop` throughout `program`, which must contain none. The
/// entry's value, when it is a pointer other than a string, has no consumer and
/// is dropped here, so the entry then returns `Unit`; a string root is handed
/// to the host, and so is an interactive program's, which holds its model and
/// closures.
pub fn insert_rc(program: &mut Program) {
    let bodies: Vec<Expr> = program
        .funcs
        .iter()
        .map(|func| Cx::new(func).rewrite())
        .collect();
    for (func, body) in program.funcs.iter_mut().zip(bodies) {
        assert_eq!(
            effects(&func.body),
            effects(&body),
            "reference counting changed a function's effects"
        );
        func.body = body;
    }
    if program.interactive.is_none()
        && let Some(entry) = program.funcs.get_mut(program.entry.0 as usize)
        && entry.ret.is_discarded_root()
    {
        let body = std::mem::replace(&mut entry.body, Expr::Const(Const::Unit));
        let next = max_local(entry) + 1;
        let (result, discard) = (Local(next), Local(next + 1));
        entry.body = Expr::Let(
            result,
            Box::new(body),
            Box::new(Expr::Let(
                discard,
                Box::new(Expr::Drop(result)),
                Box::new(Expr::Const(Const::Unit)),
            )),
        );
        entry.ret = MTy::Unit;
    }
}

fn max_local(func: &Func) -> u32 {
    let mut max = 0;
    func.params.iter().for_each(|(l, _)| max = max.max(l.0));
    if let Some(env) = &func.env {
        max = max.max(env.local.0);
    }
    func.body.for_each_node(&mut |e| {
        let mut note = |l: &Local| max = max.max(l.0);
        match e {
            Expr::Let(x, ..) => note(x),
            Expr::Unpack(_, _, binds, _) => binds.iter().for_each(note),
            _ => {}
        }
    });
    max
}

/// The rewritten expression, the owned locals it uses that are bound outside
/// it, and those among them whose last use is a borrow that has not yet been
/// followed by its `Drop`.
struct Out {
    expr: Expr,
    uses: Set,
    pending: Set,
}

impl Out {
    fn new(expr: Expr) -> Out {
        Out {
            expr,
            uses: Set::new(),
            pending: Set::new(),
        }
    }
}

#[derive(Default)]
struct Parts {
    exprs: Vec<Expr>,
    uses: Set,
    pending: Set,
}

impl Parts {
    fn into_out(self, build: impl FnOnce(Vec<Expr>) -> Expr) -> Out {
        Out {
            expr: build(self.exprs),
            uses: self.uses,
            pending: self.pending,
        }
    }
}

struct Cx<'p> {
    func: &'p Func,
    next: u32,
}

impl<'p> Cx<'p> {
    fn new(func: &'p Func) -> Cx<'p> {
        Cx {
            func,
            next: max_local(func) + 1,
        }
    }

    fn rewrite(mut self) -> Expr {
        let func = self.func;
        let out = self.go(&func.body, &Set::new());
        let mut owned: Vec<Local> = self.func.params.iter().map(|p| p.0).collect();
        owned.extend(self.func.env.as_ref().map(|e| e.local));
        let unused: Vec<Local> = owned
            .into_iter()
            .filter(|l| self.owned(*l) && !out.uses.contains(l))
            .collect();
        let body = self.with_pending(out.expr, &out.pending);
        self.drops(unused, body)
    }

    fn owned(&self, x: Local) -> bool {
        self.func.local_ty(x).is_some_and(MTy::is_ptr)
    }

    fn fresh(&mut self) -> Local {
        self.next += 1;
        Local(self.next - 1)
    }

    /// `body` preceded by a `Drop` of each local.
    fn drops(&mut self, locals: impl IntoIterator<Item = Local>, body: Expr) -> Expr {
        let locals: Vec<Local> = locals.into_iter().collect();
        locals.into_iter().rev().fold(body, |body, l| {
            Expr::Let(self.fresh(), Box::new(Expr::Drop(l)), Box::new(body))
        })
    }

    /// `e`, then a `Drop` of each pending local, yielding `e`'s value.
    fn with_pending(&mut self, e: Expr, pending: &Set) -> Expr {
        if pending.is_empty() {
            return e;
        }
        let result = self.fresh();
        let tail = self.drops(pending.iter().copied(), Expr::Local(result));
        Expr::Let(result, Box::new(e), Box::new(tail))
    }

    /// Rewrite `e`, where `after` holds the owned locals still needed once `e`
    /// has finished (so a by-value use of one of them must `Dup` first).
    fn go(&mut self, e: &Expr, after: &Set) -> Out {
        match e {
            Expr::Const(_) | Expr::StrLit(_) | Expr::Trap(_) | Expr::Dup(_) | Expr::Site(..) => {
                Out::new(e.clone())
            }
            Expr::Local(x) => self.local(*x, after),
            Expr::Drop(x) | Expr::Free(x) => self.consumed(e.clone(), *x),
            Expr::Capture(_) => match self.func.env.as_ref().map(|env| env.local) {
                Some(env) => self.borrow(e.clone(), env, after),
                None => Out::new(e.clone()),
            },
            Expr::Field(x, _)
            | Expr::Payload(x, ..)
            | Expr::StrLen(x)
            | Expr::Write(Write::Str(x)) => self.borrow(e.clone(), *x, after),
            Expr::StrEq(a, b) | Expr::StrByte(a, b) => {
                let b = self.borrow(Expr::Const(Const::Unit), *b, after);
                let live: Set = after | &b.uses;
                let a = self.borrow(Expr::Const(Const::Unit), *a, &live);
                Out {
                    expr: e.clone(),
                    uses: &a.uses | &b.uses,
                    pending: &a.pending | &b.pending,
                }
            }
            Expr::Write(Write::Number(value)) => {
                let out = self.go(value, after);
                Out {
                    expr: Expr::Write(Write::Number(Box::new(out.expr))),
                    ..out
                }
            }
            Expr::IntToFloat(value) | Expr::FloatFn(_, value) => {
                let out = self.go(value, after);
                Out {
                    expr: e.with_operand(out.expr),
                    ..out
                }
            }
            Expr::Write(Write::Lit(_) | Write::End) => Out::new(e.clone()),
            Expr::CallForeign(_, args) => {
                let mut live = after.clone();
                let mut out = Out::new(e.clone());
                for &arg in args.iter().rev() {
                    let borrowed = self.borrow(Expr::Const(Const::Unit), arg, &live);
                    live.extend(borrowed.uses.iter().copied());
                    out.uses.extend(borrowed.uses);
                    out.pending.extend(borrowed.pending);
                }
                out
            }
            Expr::Let(..) => self.let_chain(e, after),
            Expr::BinInt(op, a, b) => self.binary(a, b, after, |a, b| Expr::BinInt(*op, a, b)),
            Expr::BinFloat(op, a, b) => self.binary(a, b, after, |a, b| Expr::BinFloat(*op, a, b)),
            Expr::Cmp(op, a, b) => self.binary(a, b, after, |a, b| Expr::Cmp(*op, a, b)),
            Expr::If(cond, then, otherwise) => self.if_(cond, then, otherwise, after),
            Expr::Switch(x, arms, default) => self.switch(*x, arms, default, after),
            Expr::CallDirect(f, args) => {
                let parts = self.seq(&args.iter().collect::<Vec<_>>(), after);
                parts.into_out(|args| Expr::CallDirect(*f, args))
            }
            Expr::CallClosure(callee, args) => {
                let (callee, parts) = self.call_parts(Some(callee), args, after);
                parts.into_out(|args| {
                    let callee = callee.unwrap_or(Expr::Const(Const::Unit));
                    Expr::CallClosure(Box::new(callee), args)
                })
            }
            Expr::TailCall(callee, args) => self.tail_call(callee, args, after),
            Expr::MakeClosure(f, fields) => {
                let parts = self.seq(&fields.iter().collect::<Vec<_>>(), after);
                parts.into_out(|fields| Expr::MakeClosure(*f, fields))
            }
            Expr::AllocRecord(layout, fields) => {
                let parts = self.seq(&fields.iter().collect::<Vec<_>>(), after);
                parts.into_out(|fields| Expr::AllocRecord(*layout, fields))
            }
            Expr::AllocVariant(layout, tag, fields) => {
                let parts = self.seq(&fields.iter().collect::<Vec<_>>(), after);
                parts.into_out(|fields| Expr::AllocVariant(*layout, *tag, fields))
            }
            Expr::ReuseVariant(token, layout, tag, fields) => {
                let mut parts = self.seq(&fields.iter().collect::<Vec<_>>(), after);
                if self.owned(*token) {
                    parts.uses.insert(*token);
                }
                parts.into_out(|fields| Expr::ReuseVariant(*token, *layout, *tag, fields))
            }
            Expr::ReuseRecord(base, layout, fields) => {
                self.reuse_record(*base, *layout, fields, after)
            }
            Expr::Unpack(x, tag, binds, body) => self.unpack(*x, *tag, binds, body, after),
        }
    }

    fn consumed(&self, expr: Expr, x: Local) -> Out {
        let mut out = Out::new(expr);
        if self.owned(x) {
            out.uses.insert(x);
        }
        out
    }

    /// A by-value use of `x`: a `Dup` first when `x` is still needed after.
    fn local(&mut self, x: Local, after: &Set) -> Out {
        let mut out = self.consumed(Expr::Local(x), x);
        if out.uses.contains(&x) && after.contains(&x) {
            out.expr = Expr::Let(
                self.fresh(),
                Box::new(Expr::Dup(x)),
                Box::new(Expr::Local(x)),
            );
        }
        out
    }

    /// A load that leaves `x` owned. When it is `x`'s last use, `x` is dropped
    /// once the enclosing statement has finished.
    fn borrow(&self, expr: Expr, x: Local, after: &Set) -> Out {
        let mut out = self.consumed(expr, x);
        if out.uses.contains(&x) && !after.contains(&x) {
            out.pending.insert(x);
        }
        out
    }

    /// Rewrite `items`, evaluated in order, the last one first so that each is
    /// told what the later ones still need.
    fn seq(&mut self, items: &[&Expr], after: &Set) -> Parts {
        let mut live = after.clone();
        let mut parts = Parts::default();
        for item in items.iter().rev() {
            let out = self.go(item, &live);
            live.extend(out.uses.iter().copied());
            parts.uses.extend(out.uses);
            parts.pending.extend(out.pending);
            parts.exprs.push(out.expr);
        }
        parts.exprs.reverse();
        parts
    }

    /// A call's operands: the callee (when it is an expression) is evaluated
    /// before the arguments.
    fn call_parts(
        &mut self,
        callee: Option<&Expr>,
        args: &[Expr],
        after: &Set,
    ) -> (Option<Expr>, Parts) {
        let items: Vec<&Expr> = callee.into_iter().chain(args).collect();
        let mut parts = self.seq(&items, after);
        let callee = callee.map(|_| parts.exprs.remove(0));
        (callee, parts)
    }

    fn binary(
        &mut self,
        a: &Expr,
        b: &Expr,
        after: &Set,
        build: impl FnOnce(Box<Expr>, Box<Expr>) -> Expr,
    ) -> Out {
        let b = self.go(b, after);
        let live: Set = after | &b.uses;
        let a = self.go(a, &live);
        Out {
            expr: build(Box::new(a.expr), Box::new(b.expr)),
            uses: &a.uses | &b.uses,
            pending: &a.pending | &b.pending,
        }
    }

    fn tail_call(&mut self, callee: &Callee, args: &[Expr], after: &Set) -> Out {
        let closure = match callee {
            Callee::Closure(c) => Some(&**c),
            Callee::Direct(_) => None,
        };
        let (closure, parts) = self.call_parts(closure, args, after);
        let mut target = match (callee, closure) {
            (Callee::Direct(f), _) => Callee::Direct(*f),
            (Callee::Closure(old), new) => {
                Callee::Closure(Box::new(new.unwrap_or_else(|| (**old).clone())))
            }
        };
        let mut args = parts.exprs;
        if parts.pending.is_empty() {
            return Out {
                expr: Expr::TailCall(target, args),
                uses: parts.uses,
                pending: Set::new(),
            };
        }

        // Nothing runs after a tail call, so the deferred drops go between the
        // operands and the call; the operands are bound first to keep the
        // order in which they were evaluated.
        let mut bindings = Vec::new();
        if let Callee::Closure(c) = &mut target {
            let t = self.fresh();
            bindings.push((t, std::mem::replace(&mut **c, Expr::Local(t))));
        }
        for arg in &mut args {
            let t = self.fresh();
            bindings.push((t, std::mem::replace(arg, Expr::Local(t))));
        }
        let mut body = self.drops(parts.pending, Expr::TailCall(target, args));
        for (t, value) in bindings.into_iter().rev() {
            body = Expr::Let(t, Box::new(value), Box::new(body));
        }
        Out {
            expr: body,
            uses: parts.uses,
            pending: Set::new(),
        }
    }

    /// Close the scope of `binders` over `body`: each one the body does not use
    /// is dropped up front, and each one whose last use is a borrow is dropped
    /// after the body. Returns the body and what it leaves free.
    fn scope(&mut self, binders: &[Local], body: Out) -> (Expr, Set, Set) {
        let (mut uses, mut pending) = (body.uses, body.pending);
        let mut unused = Vec::new();
        let mut deferred = Set::new();
        for &x in binders {
            let used = uses.remove(&x);
            if pending.remove(&x) {
                deferred.insert(x);
            } else if self.owned(x) && !used {
                unused.push(x);
            }
        }
        let expr = self.with_pending(body.expr, &deferred);
        (self.drops(unused, expr), uses, pending)
    }

    /// A chain of `Let`s, rewritten from the last body back to the first
    /// binding in a loop so a long block costs no stack. Every body in the
    /// chain has the same `after`: whatever follows the whole chain.
    fn let_chain(&mut self, first: &Expr, after: &Set) -> Out {
        let mut bindings = Vec::new();
        let mut cursor = first;
        while let Expr::Let(x, rhs, body) = cursor {
            bindings.push((*x, &**rhs));
            cursor = body;
        }
        let mut out = self.go(cursor, after);
        for (x, rhs) in bindings.into_iter().rev() {
            let (body_expr, mut uses, pending) = self.scope(&[x], out);
            let live: Set = after | &uses;
            let rhs = self.go(rhs, &live);
            let body_expr = self.drops(rhs.pending, body_expr);
            uses.extend(rhs.uses);
            out = Out {
                expr: Expr::Let(x, Box::new(rhs.expr), Box::new(body_expr)),
                uses,
                pending,
            };
        }
        out
    }

    /// The fields are evaluated while `base` is still live, then the op moves
    /// it, after a `Dup` when it is needed later (so the cell is shared and the
    /// op allocates).
    fn reuse_record(&mut self, base: Local, layout: LayoutId, fields: &[Expr], after: &Set) -> Out {
        let mut live = after.clone();
        live.insert(base);
        let parts = self.seq(&fields.iter().collect::<Vec<_>>(), &live);
        let mut out = parts.into_out(|fields| Expr::ReuseRecord(base, layout, fields));
        out.uses.insert(base);
        if after.contains(&base) {
            let reuse = out.expr;
            out.expr = Expr::Let(self.fresh(), Box::new(Expr::Dup(base)), Box::new(reuse));
        }
        out
    }

    fn unpack(&mut self, x: Local, tag: u32, binds: &[Local], body: &Expr, after: &Set) -> Out {
        let body = self.go(body, after);
        let (body_expr, mut uses, pending) = self.scope(binds, body);
        if self.owned(x) {
            uses.insert(x);
        }
        Out {
            expr: Expr::Unpack(x, tag, binds.to_vec(), Box::new(body_expr)),
            uses,
            pending,
        }
    }

    /// A branch that starts by dropping every local in `dying` it does not use.
    fn branch(&mut self, out: Out, dying: &Set) -> Expr {
        let missing: Vec<Local> = dying.difference(&out.uses).copied().collect();
        let body = self.with_pending(out.expr, &out.pending);
        self.drops(missing, body)
    }

    fn if_(&mut self, cond: &Expr, then: &Expr, otherwise: &Expr, after: &Set) -> Out {
        let then = self.go(then, after);
        let otherwise = self.go(otherwise, after);
        let branch_uses: Set = &then.uses | &otherwise.uses;
        let dying: Set = branch_uses.difference(after).copied().collect();
        let then_expr = self.branch(then, &dying);
        let else_expr = self.branch(otherwise, &dying);

        let live: Set = after | &branch_uses;
        let cond = self.go(cond, &live);
        let expr = if cond.pending.is_empty() {
            Expr::If(
                Box::new(cond.expr),
                Box::new(then_expr),
                Box::new(else_expr),
            )
        } else {
            let c = self.fresh();
            let branches = Expr::If(
                Box::new(Expr::Local(c)),
                Box::new(then_expr),
                Box::new(else_expr),
            );
            let body = self.drops(cond.pending, branches);
            Expr::Let(c, Box::new(cond.expr), Box::new(body))
        };
        Out {
            expr,
            uses: &cond.uses | &branch_uses,
            pending: Set::new(),
        }
    }

    fn switch(&mut self, x: Local, arms: &[(u32, Block)], default: &Block, after: &Set) -> Out {
        let mut outs: Vec<Out> = arms.iter().map(|(_, b)| self.go(b, after)).collect();
        outs.push(self.go(default, after));
        let mut uses: Set = outs.iter().flat_map(|o| o.uses.iter().copied()).collect();
        if self.owned(x) {
            uses.insert(x);
        }
        let dying: Set = uses.difference(after).copied().collect();
        let mut blocks: Vec<Expr> = outs.into_iter().map(|o| self.branch(o, &dying)).collect();
        let default = blocks.pop().unwrap_or_else(|| default.clone());
        let arms = arms.iter().map(|(t, _)| *t).zip(blocks).collect();
        Out {
            expr: Expr::Switch(x, arms, Box::new(default)),
            uses,
            pending: Set::new(),
        }
    }
}
