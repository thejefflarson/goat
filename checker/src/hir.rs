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
    /// `record.label` — field access.
    Field {
        record: Box<Expr>,
        label: String,
    },
}
