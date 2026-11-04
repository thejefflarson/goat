//! The high-level intermediate representation: an owned, name-resolved tree.
//!
//! Unlike the parser's borrowed `Ast<'a>`, the HIR owns its data and carries a
//! resolved [`Symbol`] on every binding and use, so later phases (inference,
//! codegen) never touch the source string or re-run name resolution. Spans are
//! byte offsets into the source, kept only for diagnostics.

/// A resolved name. Every binding occurrence (declaration, function parameter)
/// gets a fresh `Symbol`; every use carries the `Symbol` of the binding it
/// resolved to. This is the scope-aware alpha-renaming the old `Renamer` never
/// did correctly.
pub type Symbol = u32;

/// A stable identifier for an expression node, used to key the inferred type of
/// each node after checking.
pub type ExprId = u32;

/// A half-open byte range `[start, end)` into the source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Span {
        Span { start, end }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Lt,
    Lte,
    Gt,
    Gte,
}

impl BinOp {
    /// Whether this operator yields a `Bool` (the comparisons) rather than a
    /// `Number` (the arithmetic).
    pub fn is_comparison(self) -> bool {
        matches!(self, BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte)
    }
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

#[derive(Clone, Debug)]
pub struct Expr {
    pub id: ExprId,
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    /// An empty program, or an empty function body.
    Unit,
    Number(f64),
    Str(String),
    Bool(bool),
    /// A use of a name, resolved to its binding.
    Var {
        symbol: Symbol,
        name: String,
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
    },
    /// `match scrutinee do arms else else_branch done`.
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
        else_branch: Option<Box<Expr>>,
    },
}
