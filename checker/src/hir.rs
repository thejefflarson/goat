//! The high-level intermediate representation: an owned, name-resolved tree.
//!
//! Unlike the parser's borrowed `Ast<'a>`, the HIR owns its data and carries a
//! resolved [`Symbol`] on every binding and use, so later phases (inference,
//! codegen) never touch the source string or re-run name resolution. Spans are
//! byte offsets into the source, kept only for diagnostics.

use crate::ty::Group;
use std::fmt;
use std::sync::Arc;

/// A resolved name. Every binding occurrence (declaration, function parameter)
/// gets a fresh `Symbol`; every use carries the `Symbol` of the binding it
/// resolved to. This is the scope-aware alpha-renaming the old `Renamer` never
/// did correctly.
pub type Symbol = u32;

/// A stable identifier for an expression node, used to key the inferred type of
/// each node after checking.
pub type ExprId = u32;

/// Which source text a [`Span`]'s offsets index into.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum FileId {
    #[default]
    User,
    Prelude,
}

/// A half-open byte range `[start, end)` into the source named by `file`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub file: FileId,
}

impl Span {
    pub const fn new(start: usize, end: usize) -> Span {
        Span::in_file(start, end, FileId::User)
    }

    pub const fn in_file(start: usize, end: usize, file: FileId) -> Span {
        Span { start, end, file }
    }

    /// From the start of `self` to the end of `other`, in `self`'s file.
    pub fn to(self, other: Span) -> Span {
        Span::in_file(self.start, other.end, self.file)
    }

    pub fn in_prelude(self) -> bool {
        self.file == FileId::Prelude
    }
}

/// The functions the compiler provides without the prelude defining them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Builtin {
    /// `print`: `(a) -> Unit`, for any `a`.
    Print,
    /// `trap("message")`: stops the program. Only valid called with a
    /// string literal, which lowering turns into `ExprKind::Trap`.
    Trap,
}

impl Builtin {
    pub const ALL: [Builtin; 2] = [Builtin::Print, Builtin::Trap];

    pub fn named(name: &str) -> Option<Builtin> {
        Self::ALL.into_iter().find(|b| b.name() == name)
    }

    pub fn name(self) -> &'static str {
        match self {
            Builtin::Print => "print",
            Builtin::Trap => "trap",
        }
    }
}

/// The types that may cross the host boundary of a `foreign` function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Boundary {
    /// `Number`: a `Float` on this target.
    Number,
    Int,
    Bool,
    Unit,
    Str,
}

impl Boundary {
    pub fn named(name: &str) -> Option<Boundary> {
        match name {
            "Number" => Some(Boundary::Number),
            "Int" => Some(Boundary::Int),
            "Bool" => Some(Boundary::Bool),
            "Unit" => Some(Boundary::Unit),
            "String" => Some(Boundary::Str),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    /// `//`: Int-only floor division.
    FloorDiv,
    /// `%`: Int-only remainder, taking the sign of the divisor.
    Mod,
    Lt,
    Lte,
    Gt,
    Gte,
    Eq,
    Ne,
}

impl BinOp {
    /// `+ - * /`: defined on numbers and on records of numbers.
    pub fn is_arithmetic(self) -> bool {
        matches!(self, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div)
    }

    /// `==` and `!=`: defined on any type without a function inside it.
    pub fn is_equality(self) -> bool {
        matches!(self, BinOp::Eq | BinOp::Ne)
    }

    /// The operator as written, for messages.
    pub fn symbol(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::FloorDiv => "//",
            BinOp::Mod => "%",
            BinOp::Lt => "<",
            BinOp::Lte => "<=",
            BinOp::Gt => ">",
            BinOp::Gte => ">=",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
        }
    }
}

/// A top-level binding the interactive contract names: the span of its value,
/// and the node of its use in the synthetic tail the contract adds to the root
/// chain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ContractBinding {
    pub span: Span,
    pub use_id: ExprId,
}

/// A program whose root chain binds `init`, `update` and `draw` once each is
/// interactive (ADR 0015). Lowering ends its chain with the record
/// `{draw: draw, init: init, update: update}`, plus one field per decoder the
/// host's vocabulary names, so inference and monomorphization see them like any
/// other uses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interactive {
    pub init: ContractBinding,
    pub update: ContractBinding,
    pub draw: ContractBinding,
    pub decoders: Vec<Decoder>,
}

/// A host's decoder function (ADR 0020), defined in its prelude.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decoder {
    pub function: String,
    pub symbol: Symbol,
    pub binding: ContractBinding,
}

#[derive(Clone, Debug)]
pub struct Param {
    pub symbol: Symbol,
    pub name: String,
    pub span: Span,
}

/// What a `match` arm binds from a tag's payload, mirroring how the tag was
/// constructed: no payload, the whole payload, or the positional fields of a
/// multi-argument payload record.
#[derive(Clone, Debug)]
pub enum PatternPayload {
    None,
    Whole(Param),
    /// `(label, binder)` pairs, labelled `"0"`, `"1"`, ... in argument order.
    Fields(Vec<(String, Param)>),
}

impl PatternPayload {
    pub fn binders(&self) -> impl Iterator<Item = &Param> {
        let (whole, fields) = match self {
            PatternPayload::None => (None, &[][..]),
            PatternPayload::Whole(p) => (Some(p), &[][..]),
            PatternPayload::Fields(fs) => (None, &fs[..]),
        };
        whole.into_iter().chain(fields.iter().map(|(_, p)| p))
    }
}

#[derive(Clone, Debug)]
pub struct Pattern {
    pub tag: String,
    pub span: Span,
    pub payload: PatternPayload,
}

#[derive(Clone, Debug)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
}

pub struct Expr {
    pub id: ExprId,
    pub span: Span,
    pub kind: ExprKind,
}

/// A long block is a long chain of `Let`s, so the derived `Drop`, `Clone` and
/// `Debug` would each recurse once per statement and overflow the stack; the
/// impls below walk the chain in a loop instead.
impl Drop for Expr {
    fn drop(&mut self) {
        let mut next = self.take_rest();
        while let Some(mut link) = next {
            next = link.take_rest();
        }
    }
}

impl Expr {
    fn take_rest(&mut self) -> Option<Box<Expr>> {
        match &mut self.kind {
            ExprKind::Let { rest, .. } => rest.take(),
            _ => None,
        }
    }

    fn rest(&self) -> Option<&Expr> {
        match &self.kind {
            ExprKind::Let { rest, .. } => rest.as_deref(),
            _ => None,
        }
    }

    fn clone_without_rest(&self) -> Expr {
        let kind = match &self.kind {
            ExprKind::Let {
                symbol,
                name,
                value,
                ..
            } => ExprKind::Let {
                symbol: *symbol,
                name: name.clone(),
                value: value.clone(),
                rest: None,
            },
            kind => kind.clone(),
        };
        Expr {
            id: self.id,
            span: self.span,
            kind,
        }
    }
}

impl Clone for Expr {
    fn clone(&self) -> Expr {
        let mut links = vec![self.clone_without_rest()];
        let mut cursor = self.rest();
        while let Some(link) = cursor {
            links.push(link.clone_without_rest());
            cursor = link.rest();
        }
        let mut result = links.pop().expect("the chain has a head");
        while let Some(mut link) = links.pop() {
            if let ExprKind::Let { rest, .. } = &mut link.kind {
                *rest = Some(Box::new(result));
            }
            result = link;
        }
        result
    }
}

/// A `Let` chain prints as a flat list of its links.
impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !matches!(self.kind, ExprKind::Let { .. }) {
            return f
                .debug_struct("Expr")
                .field("id", &self.id)
                .field("span", &self.span)
                .field("kind", &self.kind)
                .finish();
        }
        let mut list = f.debug_list();
        let mut cursor = Some(self);
        while let Some(link) = cursor {
            list.entry(&LinkDebug(link));
            cursor = link.rest();
        }
        list.finish()
    }
}

struct LinkDebug<'a>(&'a Expr);

impl fmt::Debug for LinkDebug<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Expr { id, span, kind } = self.0;
        let mut s = f.debug_struct("Expr");
        s.field("id", id).field("span", span);
        match kind {
            ExprKind::Let {
                symbol,
                name,
                value,
                ..
            } => s
                .field("symbol", symbol)
                .field("name", name)
                .field("value", value),
            kind => s.field("kind", kind),
        };
        s.finish()
    }
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    /// An empty program, or an empty function body.
    Unit,
    /// A whole-number literal: `Int`, or `Float` where the context needs one.
    Int(i64),
    /// A literal with a decimal point or exponent.
    Float(f64),
    Str(String),
    Bool(bool),
    /// A use of a name, resolved to its binding.
    Var {
        symbol: Symbol,
        name: String,
    },
    /// A function the compiler provides, used by its bare name.
    Builtin(Builtin),
    /// `trap("message")`: stops the program with `message`; has any type.
    Trap(String),
    /// `foreign "module" "name" (params) -> ret`: the host function `name`
    /// of import module `module`. It is only ever the value of a `Let`, whose
    /// scheme is the fixed `(params) -> ret`; the binding is a capture-free
    /// function that has no body to lower.
    Foreign {
        module: String,
        name: String,
        params: Vec<Boundary>,
        ret: Boundary,
    },
    /// `program(params) do body done`.
    Func {
        params: Vec<Param>,
        body: Box<Expr>,
    },
    /// `callee(args)`. The grammar restricts the callee to an identifier, but
    /// the node is general so multiple argument groups (`f(x)(y)`) nest.
    App {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    /// `if cond then then_branch else else_branch done`.
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },
    /// `lhs and rhs`; `rhs` runs only when `lhs` is true.
    And {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    /// `lhs or rhs`; `rhs` runs only when `lhs` is false.
    Or {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    /// `not operand`.
    Not(Box<Expr>),
    /// `name = value rest` — a let binding. `rest` is the expression the name is
    /// in scope for; absent when the declaration is the trailing form `name =
    /// value`, whose value is then the whole expression's value.
    Let {
        symbol: Symbol,
        name: String,
        value: Box<Expr>,
        rest: Option<Box<Expr>>,
    },
    Bin {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    /// `{label: value, ...}` — a record literal (a closed row).
    Record {
        fields: Vec<(String, Expr)>,
    },
    /// `{...base, label: value, ...}` — `base` extended with the fields, which
    /// shadow any field of `base` with the same label (the new one wins, even at
    /// a different type).
    Spread {
        base: Box<Expr>,
        fields: Vec<(String, Expr)>,
    },
    /// `record` with each of `labels` taken out — what `{x, ...rest} = record`
    /// binds to `rest`.
    Restrict {
        record: Box<Expr>,
        labels: Vec<String>,
    },
    /// `record.label` — field access.
    Field {
        record: Box<Expr>,
        label: String,
    },
    /// `Tag`, `Tag(arg)` or `Tag(a, b, ...)`. One argument is the payload as
    /// is; several become an [`ExprKind::Record`] labelled `"0"`, `"1"`, ...,
    /// so variant payloads share the record row machinery.
    Tag {
        name: String,
        payload: Option<Box<Expr>>,
        /// The declared group the tag belongs to; `None` for a tag the host or
        /// the list sugar leaves open.
        group: Option<Arc<Group>>,
    },
    /// `match scrutinee do arms else else_branch done`.
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
        else_branch: Option<Box<Expr>>,
    },
}
