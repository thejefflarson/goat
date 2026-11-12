//! Functions mono derives from a ground type instead of from source: structural
//! equality (`==`), the printer behind `print`, and field-wise arithmetic on
//! records. Each is a plain MIR function memoized on the canonical form of its
//! type, so a recursive type reuses the function it is already building and the
//! derivation terminates, and the interpreter and every backend run it without
//! knowing it exists.
//!
//! A recursive call sits in tail position wherever the shape allows it (the
//! last field of a variant payload, the tail of a list), so comparing or
//! printing a long list uses constant stack.

use super::{FnCx, Mono, Subst, payload_fields, positional_fields};
use crate::canon::{canonical, ground_fields};
use crate::mir::*;
use goat_checker::hir::{BinOp, Span};
use goat_checker::ty::{Row, Ty};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Derived {
    Eq,
    Arith(FloatOp),
    /// Writes a value without ending the line.
    Show,
    /// What follows the first element of a list: `, x, y]`.
    ShowRest,
    /// Writes a value and ends the line: what `print` calls.
    Print,
}

struct ListShape {
    element: Ty,
    rest: Ty,
    empty: Option<u32>,
    link: Option<u32>,
}

impl Derived {
    fn arity(self) -> usize {
        match self {
            Derived::Eq | Derived::Arith(_) => 2,
            Derived::Show | Derived::ShowRest | Derived::Print => 1,
        }
    }
}

fn call(f: FuncId, args: Vec<Expr>, tail: bool) -> Expr {
    if tail {
        Expr::TailCall(Callee::Direct(f), args)
    } else {
        Expr::CallDirect(f, args)
    }
}

fn int_counterpart(op: FloatOp) -> IntOp {
    match op {
        FloatOp::Add => IntOp::Add,
        FloatOp::Sub => IntOp::Sub,
        FloatOp::Mul => IntOp::Mul,
        FloatOp::Div => IntOp::Div,
    }
}

fn boolean(b: bool) -> Expr {
    Expr::Const(Const::Bool(b))
}

/// The labels of a variant row, each once, with its payload type: a row can
/// repeat a label, and only the first can be matched.
fn tags(row: &Row) -> Vec<(&String, &Ty)> {
    let mut seen: Vec<&String> = Vec::new();
    ground_fields(row)
        .filter(|(label, _)| {
            let first = !seen.contains(label);
            seen.push(label);
            first
        })
        .collect()
}

impl Mono<'_> {
    /// The function of `kind` for `ty`, building it the first time. It is
    /// registered before its body is built, so a body that needs it again
    /// (a recursive type) finds the id.
    fn derive(
        &mut self,
        kind: Derived,
        ty: &Ty,
        ret: MTy,
        build: impl FnOnce(&mut Self, &mut FnCx, &[Local]) -> Expr,
    ) -> FuncId {
        let ty = canonical(ty);
        if let Some(&id) = self.derived.get(&(kind, ty.clone())) {
            return id;
        }
        let id = FuncId(self.out.len() as u32);
        self.out.push(None);
        self.derived.insert((kind, ty.clone()), id);

        let mty = self.lower_ty(&ty);
        let mut cx = FnCx::new(Subst::new());
        let locals: Vec<Local> = (0..kind.arity()).map(|_| cx.fresh(mty)).collect();
        let body = build(self, &mut cx, &locals);
        let params = locals.iter().map(|&l| (l, mty)).collect();
        self.out[id.0 as usize] = Some(cx.into_func(params, None, ret, body));
        id
    }

    /// `parts` run in order; the value is the last one's.
    fn sequence(&self, cx: &mut FnCx, mut parts: Vec<Expr>) -> Expr {
        let last = parts.pop().unwrap_or(Expr::Const(Const::Unit));
        parts.into_iter().rev().fold(last, |rest, part| {
            Expr::Let(cx.fresh(MTy::Unit), Box::new(part), Box::new(rest))
        })
    }

    fn text(&mut self, text: &str) -> Expr {
        Expr::Write(Write::Lit(self.intern(text)))
    }

    /// `Switch` on `local`, whose last arm doubles as the default as in a
    /// checked `match`.
    fn switch_on(local: Local, mut arms: Vec<(u32, Expr)>) -> Expr {
        let default = arms
            .pop()
            .map_or_else(|| Expr::Trap("no arm matches".into()), |(_, arm)| arm);
        Expr::Switch(local, arms, Box::new(default))
    }

    /// `a op b` on two values of type `ty`. An `Int` operation that overflows
    /// traps, blamed on `span` when the operation is the user's own.
    pub(super) fn arith(
        &mut self,
        cx: &mut FnCx,
        span: Option<Span>,
        op: FloatOp,
        ty: &Ty,
        a: Expr,
        b: Expr,
    ) -> Expr {
        match ty.unfold_head() {
            Ty::Float => Expr::BinFloat(op, Box::new(a), Box::new(b)),
            Ty::Int => Self::int_arith(cx, span, int_counterpart(op), a, b),
            Ty::Record(_) => {
                let f = self.arith_fn(op, ty);
                Expr::CallDirect(f, vec![a, b])
            }
            _ => Expr::Trap("arithmetic on a type that is not a number".into()),
        }
    }

    /// `//` or `%`, out of line so `bin`, which a long chain of operators
    /// recurses through, keeps a small frame.
    #[inline(never)]
    pub(super) fn whole_division(
        cx: &mut FnCx,
        (op, span): (BinOp, Span),
        a: Expr,
        b: Expr,
    ) -> Expr {
        let op = if op == BinOp::Mod {
            IntOp::Mod
        } else {
            IntOp::FloorDiv
        };
        Self::int_arith(cx, Some(span), op, a, b)
    }

    /// The site is set after both operands run, so an operand's own call cannot
    /// overwrite it before the overflow check.
    pub(super) fn int_arith(
        cx: &mut FnCx,
        span: Option<Span>,
        op: IntOp,
        a: Expr,
        b: Expr,
    ) -> Expr {
        let Some(span) = span.filter(|span| !span.in_prelude()) else {
            return Expr::BinInt(op, Box::new(a), Box::new(b));
        };
        let (x, y) = (cx.fresh(MTy::Int), cx.fresh(MTy::Int));
        let operation = Expr::BinInt(op, Box::new(Expr::Local(x)), Box::new(Expr::Local(y)));
        let blamed = Self::at_site(cx, span, operation);
        Expr::Let(
            x,
            Box::new(a),
            Box::new(Expr::Let(y, Box::new(b), Box::new(blamed))),
        )
    }

    fn arith_fn(&mut self, op: FloatOp, ty: &Ty) -> FuncId {
        let ret = self.lower_ty(&canonical(ty));
        self.derive(Derived::Arith(op), ty, ret, |m, cx, params| {
            let (a, b) = (params[0], params[1]);
            let Ty::Record(row) = ty.unfold_head() else {
                return Expr::Trap("arithmetic on a type that is not a record".into());
            };
            let MTy::Ptr(HeapKind::Record(layout)) = ret else {
                unreachable!("a record type lowers to a record pointer");
            };
            let fields = ground_fields(&row)
                .enumerate()
                .map(|(i, (_, field))| {
                    m.arith(cx, None, op, field, Expr::Field(a, i), Expr::Field(b, i))
                })
                .collect();
            Expr::AllocRecord(layout, fields)
        })
    }

    /// Whether `a` and `b`, both of type `ty`, are equal. A function inside the
    /// type is a checker error, so it cannot reach here.
    pub(super) fn equal(&mut self, cx: &mut FnCx, ty: &Ty, a: Expr, b: Expr, tail: bool) -> Expr {
        match ty.unfold_head() {
            Ty::Int | Ty::Float => Expr::Cmp(CmpOp::Eq, Box::new(a), Box::new(b)),
            Ty::Bool => {
                let (l, r) = (cx.fresh(MTy::Bool), cx.fresh(MTy::Bool));
                let differs = Expr::If(
                    Box::new(Expr::Local(r)),
                    Box::new(boolean(false)),
                    Box::new(boolean(true)),
                );
                let test = Expr::If(
                    Box::new(Expr::Local(l)),
                    Box::new(Expr::Local(r)),
                    Box::new(differs),
                );
                Expr::Let(
                    l,
                    Box::new(a),
                    Box::new(Expr::Let(r, Box::new(b), Box::new(test))),
                )
            }
            Ty::Str => {
                let (l, r) = (
                    cx.fresh(MTy::Ptr(HeapKind::Str)),
                    cx.fresh(MTy::Ptr(HeapKind::Str)),
                );
                Expr::Let(
                    l,
                    Box::new(a),
                    Box::new(Expr::Let(r, Box::new(b), Box::new(Expr::StrEq(l, r)))),
                )
            }
            Ty::Unit => self.sequence(cx, vec![a, b, boolean(true)]),
            Ty::Record(_) | Ty::Variant(_) => {
                let f = self.equal_fn(ty);
                call(f, vec![a, b], tail)
            }
            Ty::Func(..) | Ty::Rec(..) | Ty::Var(_) => {
                Expr::Trap("equality on a type that cannot be compared".into())
            }
        }
    }

    /// The conjunction of the tests, in order, as nested `If`s; the last may
    /// be a tail call.
    fn all_equal(&mut self, cx: &mut FnCx, pairs: Vec<(Ty, Expr, Expr)>, tail: bool) -> Expr {
        let pairs: Vec<_> = pairs
            .into_iter()
            .filter(|(ty, ..)| ty.unfold_head() != Ty::Unit)
            .collect();
        let count = pairs.len();
        let mut chain = None;
        for (i, (ty, a, b)) in pairs.into_iter().enumerate().rev() {
            let test = self.equal(cx, &ty, a, b, tail && i + 1 == count);
            chain = Some(match chain {
                None => test,
                Some(rest) => Expr::If(Box::new(test), Box::new(rest), Box::new(boolean(false))),
            });
        }
        chain.unwrap_or_else(|| boolean(true))
    }

    fn equal_fn(&mut self, ty: &Ty) -> FuncId {
        self.derive(Derived::Eq, ty, MTy::Bool, |m, cx, params| {
            let (a, b) = (params[0], params[1]);
            match ty.unfold_head() {
                Ty::Record(row) => {
                    let pairs = ground_fields(&row)
                        .enumerate()
                        .map(|(i, (_, field))| {
                            (field.clone(), Expr::Field(a, i), Expr::Field(b, i))
                        })
                        .collect();
                    m.all_equal(cx, pairs, true)
                }
                Ty::Variant(row) => {
                    let mut arms = Vec::new();
                    for (label, payload) in tags(&row) {
                        let tag = m.tags[label];
                        let pairs = payload_fields(payload)
                            .into_iter()
                            .enumerate()
                            .map(|(i, field)| {
                                (field, Expr::Payload(a, tag, i), Expr::Payload(b, tag, i))
                            })
                            .collect();
                        let same = m.all_equal(cx, pairs, true);
                        let other = Expr::Switch(b, vec![(tag, same)], Box::new(boolean(false)));
                        arms.push((tag, other));
                    }
                    let Some((_, last)) = arms.pop() else {
                        return boolean(false);
                    };
                    Expr::Switch(a, arms, Box::new(last))
                }
                _ => Expr::Trap("equality on a type that cannot be compared".into()),
            }
        })
    }

    /// The function behind `print` for an argument of type `ty`.
    pub(super) fn print_fn(&mut self, ty: &Ty) -> FuncId {
        self.derive(Derived::Print, ty, MTy::Unit, |m, cx, params| {
            let shown = m.show(cx, ty, Expr::Local(params[0]), false);
            m.sequence(cx, vec![shown, Expr::Write(Write::End)])
        })
    }

    /// Write `value`, of type `ty`. A string inside a larger value is quoted;
    /// one printed by itself is not.
    fn show(&mut self, cx: &mut FnCx, ty: &Ty, value: Expr, nested: bool) -> Expr {
        match ty.unfold_head() {
            Ty::Int | Ty::Float => Expr::Write(Write::Number(Box::new(value))),
            Ty::Bool => {
                let b = cx.fresh(MTy::Bool);
                let (yes, no) = (self.text("true"), self.text("false"));
                let pick = Expr::If(Box::new(Expr::Local(b)), Box::new(yes), Box::new(no));
                Expr::Let(b, Box::new(value), Box::new(pick))
            }
            Ty::Str => {
                let s = cx.fresh(MTy::Ptr(HeapKind::Str));
                let written = if nested {
                    let quote = self.text("\"");
                    let closing = self.text("\"");
                    let body = Expr::Write(Write::Str(s));
                    self.sequence(cx, vec![quote, body, closing])
                } else {
                    Expr::Write(Write::Str(s))
                };
                Expr::Let(s, Box::new(value), Box::new(written))
            }
            Ty::Unit => {
                let name = self.text("Unit");
                self.sequence(cx, vec![value, name])
            }
            Ty::Record(_) | Ty::Variant(_) => {
                let f = self.show_fn(ty);
                Expr::CallDirect(f, vec![value])
            }
            Ty::Func(..) | Ty::Rec(..) | Ty::Var(_) => {
                let name = self.text("<function>");
                let ty = match ty {
                    Ty::Var(_) => MTy::Unit,
                    _ => self.lower_ty(ty),
                };
                Expr::Let(cx.fresh(ty), Box::new(value), Box::new(name))
            }
        }
    }

    fn show_fn(&mut self, ty: &Ty) -> FuncId {
        self.derive(Derived::Show, ty, MTy::Unit, |m, cx, params| {
            let v = params[0];
            match ty.unfold_head() {
                Ty::Record(row) => m.show_record(cx, ty, &row, v),
                Ty::Variant(row) => match m.list_shape(ty) {
                    Some(shape) => m.show_list(cx, &shape, v),
                    None => m.show_variant(cx, &row, v),
                },
                _ => Expr::Trap("printing a type with no printer".into()),
            }
        })
    }

    fn show_record(&mut self, cx: &mut FnCx, ty: &Ty, row: &Row, v: Local) -> Expr {
        let positional = positional_fields(ty).is_some();
        let (open, close) = if positional { ("(", ")") } else { ("{", "}") };
        let mut parts = vec![self.text(open)];
        for (i, (label, field)) in ground_fields(row).enumerate() {
            if i > 0 {
                parts.push(self.text(", "));
            }
            if !positional {
                parts.push(self.text(&format!("{label}: ")));
            }
            parts.push(self.show(cx, field, Expr::Field(v, i), true));
        }
        parts.push(self.text(close));
        self.sequence(cx, parts)
    }

    fn show_variant(&mut self, cx: &mut FnCx, row: &Row, v: Local) -> Expr {
        let mut arms = Vec::new();
        for (label, payload) in tags(row) {
            let tag = self.tags[label];
            let mut parts = vec![self.text(label)];
            let slots = payload_fields(payload);
            if !slots.is_empty() {
                parts.push(self.text("("));
                for (i, slot) in slots.iter().enumerate() {
                    if i > 0 {
                        parts.push(self.text(", "));
                    }
                    parts.push(self.show(cx, slot, Expr::Payload(v, tag, i), true));
                }
                parts.push(self.text(")"));
            }
            arms.push((tag, self.sequence(cx, parts)));
        }
        Self::switch_on(v, arms)
    }

    /// What a list `ty` is made of: a variant of `Empty` and `Link(first,
    /// rest)`, where `rest` is again a list. A list literal is a finite chain
    /// of such types, and one built by a function is a recursive type whose
    /// `rest` is itself. A value of only `Empty` is the empty list of no
    /// particular element type.
    fn list_shape(&self, ty: &Ty) -> Option<ListShape> {
        self.list_shape_in(ty, &mut Vec::new())
    }

    /// `seen` holds the lists above `ty` in the chain, so a recursive type
    /// ends the walk where it returns to one.
    fn list_shape_in(&self, ty: &Ty, seen: &mut Vec<Ty>) -> Option<ListShape> {
        let Ty::Variant(row) = ty.unfold_head() else {
            return None;
        };
        seen.push(canonical(ty));
        let mut shape = ListShape {
            element: Ty::Unit,
            rest: Ty::Unit,
            empty: None,
            link: None,
        };
        for (label, payload) in tags(&row) {
            match label.as_str() {
                "Empty" if *payload == Ty::Unit => shape.empty = Some(self.tags[label]),
                "Link" => {
                    let slots = positional_fields(payload)?;
                    let [first, rest] = slots.as_slice() else {
                        return None;
                    };
                    if !seen.contains(&canonical(rest)) {
                        self.list_shape_in(rest, seen)?;
                    }
                    shape.element = first.clone();
                    shape.rest = rest.clone();
                    shape.link = Some(self.tags[label]);
                }
                _ => return None,
            }
        }
        Some(shape)
    }

    /// `[1, 2, 3]`, written with one call per element in constant stack.
    fn show_list(&mut self, cx: &mut FnCx, shape: &ListShape, v: Local) -> Expr {
        let mut arms = Vec::new();
        if let Some(tag) = shape.empty {
            arms.push((tag, self.text("[]")));
        }
        if let Some(tag) = shape.link {
            let rest = self.show_rest_fn(&shape.rest);
            let open = self.text("[");
            let first = self.show(cx, &shape.element, Expr::Payload(v, tag, 0), true);
            let more = call(rest, vec![Expr::Payload(v, tag, 1)], true);
            arms.push((tag, self.sequence(cx, vec![open, first, more])));
        }
        Self::switch_on(v, arms)
    }

    /// The list `ty` after its first element has been written.
    fn show_rest_fn(&mut self, ty: &Ty) -> FuncId {
        self.derive(Derived::ShowRest, ty, MTy::Unit, |m, cx, params| {
            let Some(shape) = m.list_shape(ty) else {
                return Expr::Trap("printing a type with no printer".into());
            };
            let v = params[0];
            let mut arms = Vec::new();
            if let Some(tag) = shape.empty {
                arms.push((tag, m.text("]")));
            }
            if let Some(tag) = shape.link {
                let rest = m.show_rest_fn(&shape.rest);
                let comma = m.text(", ");
                let first = m.show(cx, &shape.element, Expr::Payload(v, tag, 0), true);
                let more = call(rest, vec![Expr::Payload(v, tag, 1)], true);
                arms.push((tag, m.sequence(cx, vec![comma, first, more])));
            }
            Self::switch_on(v, arms)
        })
    }
}
