//! SPIKE (throwaway): a resilient, lossless parser for a slice of goat's grammar,
//! in the rust-analyzer style: a hand-written lexer, a hand-written recursive-
//! descent parser that never fails, and a `rowan` green tree. The slice is the
//! binding chain, binary operators, calls/field access, and `match ... do arm*
//! else? done`. Not wired into the real compiler.

pub mod ast;
mod lexer;
mod parser;

pub use lexer::lex;
pub use parser::{Diagnostic, Parse, parse};

use rowan::Language;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum SyntaxKind {
    // tokens
    Whitespace,
    Comment,
    Ident,
    Number,
    Str,
    Unknown,
    Eq,
    Semi,
    Comma,
    Dot,
    LParen,
    RParen,
    Plus,
    Minus,
    Star,
    Slash,
    FloorDiv,
    Percent,
    EqEq,
    NotEq,
    Lte,
    Lt,
    Gte,
    Gt,
    MatchKw,
    DoKw,
    DoneKw,
    ThenKw,
    ElseKw,
    NotKw,
    AndKw,
    OrKw,
    TrueKw,
    FalseKw,
    // nodes
    Root,
    Let,
    Expr,
    Operation,
    Negation,
    Call,
    Access,
    Paren,
    MatchExpr,
    Arm,
    Pattern,
    Name,
    Literal,
    Error,
}

impl SyntaxKind {
    pub fn is_trivia(self) -> bool {
        matches!(self, SyntaxKind::Whitespace | SyntaxKind::Comment)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Goat {}

impl Language for Goat {
    type Kind = SyntaxKind;
    fn kind_from_raw(raw: rowan::SyntaxKind) -> SyntaxKind {
        assert!(raw.0 <= SyntaxKind::Error as u16);
        // SAFETY: `SyntaxKind` is `repr(u16)` with contiguous discriminants and
        // `raw` is in range, checked above.
        unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    }
    fn kind_to_raw(kind: SyntaxKind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind as u16)
    }
}

pub type SyntaxNode = rowan::SyntaxNode<Goat>;
pub type SyntaxToken = rowan::SyntaxToken<Goat>;

/// The chain of node kinds enclosing `offset`, innermost first, skipping
/// `Error` wrappers. This is what an editor asks for to decide what to offer
/// at the cursor (e.g. inside `MatchExpr` after `do` → arm patterns / `done`).
pub fn enclosing_kinds(root: &SyntaxNode, offset: usize) -> Vec<SyntaxKind> {
    let at = rowan::TextSize::try_from(offset).expect("offset fits u32");
    let token = match root.token_at_offset(at) {
        rowan::TokenAtOffset::None => return vec![],
        rowan::TokenAtOffset::Single(t) => t,
        // At a boundary prefer the token to the left: the one being typed.
        rowan::TokenAtOffset::Between(left, _) => left,
    };
    token
        .parent_ancestors()
        .map(|n| n.kind())
        .filter(|k| *k != SyntaxKind::Error)
        .collect()
}
