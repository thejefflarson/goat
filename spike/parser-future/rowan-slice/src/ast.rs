//! A typed view over the CST: what `lower.rs` would consume instead of
//! `pest::Pair<Rule>`. Every accessor returns `Option` because a recovered
//! tree may be missing any child; lowering skips what is absent (the parser
//! already reported it).

use crate::{SyntaxKind, SyntaxNode, SyntaxToken};

macro_rules! node {
    ($name:ident, $kind:ident) => {
        #[derive(Debug, Clone)]
        pub struct $name(pub SyntaxNode);
        impl $name {
            pub fn cast(node: SyntaxNode) -> Option<Self> {
                (node.kind() == SyntaxKind::$kind).then(|| Self(node))
            }
        }
    };
}

node!(Let, Let);
node!(MatchExpr, MatchExpr);
node!(Arm, Arm);
node!(Expr, Expr);

fn children<T>(node: &SyntaxNode, cast: fn(SyntaxNode) -> Option<T>) -> impl Iterator<Item = T> {
    node.children().filter_map(cast)
}

fn token(node: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxToken> {
    node.children_with_tokens()
        .filter_map(|e| e.into_token())
        .find(|t| t.kind() == kind)
}

impl Let {
    pub fn name(&self) -> Option<String> {
        token(&self.0, SyntaxKind::Ident).map(|t| t.text().to_string())
    }
    /// The value expression: whichever non-token child follows the `=`.
    pub fn value(&self) -> Option<SyntaxNode> {
        self.0.children().next()
    }
}

impl MatchExpr {
    pub fn scrutinee(&self) -> Option<Expr> {
        children(&self.0, Expr::cast).next()
    }
    pub fn arms(&self) -> impl Iterator<Item = Arm> {
        children(&self.0, Arm::cast)
    }
    pub fn has_done(&self) -> bool {
        token(&self.0, SyntaxKind::DoneKw).is_some()
    }
}

impl Arm {
    pub fn pattern_head(&self) -> Option<String> {
        let pat = self
            .0
            .children()
            .find(|n| n.kind() == SyntaxKind::Pattern)?;
        pat.children_with_tokens()
            .filter_map(|e| e.into_token())
            .find(|t| !t.kind().is_trivia())
            .map(|t| t.text().to_string())
    }
    pub fn body(&self) -> Option<Expr> {
        children(&self.0, Expr::cast).next()
    }
}

/// Every top-level binding in source order, however broken the rest is.
pub fn lets(root: &SyntaxNode) -> Vec<Let> {
    root.descendants().filter_map(Let::cast).collect()
}
