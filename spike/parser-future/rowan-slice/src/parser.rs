use crate::lexer::lex;
use crate::{
    SyntaxKind::{self, *},
    SyntaxNode,
};
use rowan::{Checkpoint, GreenNode, GreenNodeBuilder};
use std::ops::Range;

/// Deepest nesting the parser follows before it stops recursing, so hostile
/// input cannot overflow the stack.
const MAX_DEPTH: usize = 256;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub range: Range<usize>,
    pub message: String,
}

pub struct Parse {
    green: GreenNode,
    pub diagnostics: Vec<Diagnostic>,
}

impl Parse {
    pub fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green.clone())
    }
}

/// Parse `src`. Never fails: always returns a tree that covers every byte of
/// `src`, plus the diagnostics found on the way.
pub fn parse(src: &str) -> Parse {
    let mut p = Parser::new(src);
    p.root();
    p.finish()
}

fn raw(kind: SyntaxKind) -> rowan::SyntaxKind {
    rowan::SyntaxKind(kind as u16)
}

struct Parser<'a> {
    toks: Vec<(SyntaxKind, &'a str)>,
    starts: Vec<usize>,
    src_len: usize,
    pos: usize,
    depth: usize,
    builder: GreenNodeBuilder<'static>,
    diagnostics: Vec<Diagnostic>,
}

impl<'a> Parser<'a> {
    fn new(src: &'a str) -> Self {
        let toks = lex(src);
        let mut starts = Vec::with_capacity(toks.len());
        let mut at = 0;
        for (_, text) in &toks {
            starts.push(at);
            at += text.len();
        }
        Parser {
            toks,
            starts,
            src_len: src.len(),
            pos: 0,
            depth: 0,
            builder: GreenNodeBuilder::new(),
            diagnostics: Vec::new(),
        }
    }

    fn finish(self) -> Parse {
        Parse {
            green: self.builder.finish(),
            diagnostics: self.diagnostics,
        }
    }

    // ---- token plumbing ----

    fn nth_index(&self, n: usize) -> Option<usize> {
        (self.pos..self.toks.len())
            .filter(|&i| !self.toks[i].0.is_trivia())
            .nth(n)
    }

    fn nth(&self, n: usize) -> Option<SyntaxKind> {
        self.nth_index(n).map(|i| self.toks[i].0)
    }

    fn peek(&self) -> Option<SyntaxKind> {
        self.nth(0)
    }

    fn at(&self, kind: SyntaxKind) -> bool {
        self.peek() == Some(kind)
    }

    fn eat_trivia(&mut self) {
        while let Some((kind, text)) = self.toks.get(self.pos).copied() {
            if !kind.is_trivia() {
                break;
            }
            self.builder.token(raw(kind), text);
            self.pos += 1;
        }
    }

    fn bump(&mut self) {
        self.eat_trivia();
        let (kind, text) = self.toks[self.pos];
        self.builder.token(raw(kind), text);
        self.pos += 1;
    }

    fn start(&mut self, kind: SyntaxKind) {
        self.eat_trivia();
        self.builder.start_node(raw(kind));
    }

    fn start_at(&mut self, cp: Checkpoint, kind: SyntaxKind) {
        self.builder.start_node_at(cp, raw(kind));
    }

    fn checkpoint(&mut self) -> Checkpoint {
        self.eat_trivia();
        self.builder.checkpoint()
    }

    fn finish_node(&mut self) {
        self.builder.finish_node();
    }

    fn eof(&self) -> bool {
        self.peek().is_none()
    }

    // ---- diagnostics ----

    fn here(&self) -> Range<usize> {
        match self.nth_index(0) {
            Some(i) => self.starts[i]..self.starts[i] + self.toks[i].1.len(),
            None => self.src_len..self.src_len,
        }
    }

    fn found(&self) -> String {
        match self.nth_index(0) {
            Some(i) => format!("`{}`", self.toks[i].1),
            None => "end of file".to_string(),
        }
    }

    fn error(&mut self, expected: &str) {
        let message = format!("expected {expected}, found {}", self.found());
        self.diagnostics.push(Diagnostic {
            range: self.here(),
            message,
        });
    }

    /// Report `expected` and wrap the offending token in an `Error` node so
    /// the parser always makes progress.
    fn error_bump(&mut self, expected: &str) {
        self.error(expected);
        if !self.eof() {
            self.start(Error);
            self.bump();
            self.finish_node();
        }
    }

    fn expect(&mut self, kind: SyntaxKind, what: &str) {
        if self.at(kind) {
            self.bump();
        } else {
            self.error(what);
        }
    }

    // ---- lookahead sets ----

    fn at_operand_start(&self) -> bool {
        matches!(
            self.peek(),
            Some(Ident | Number | Str | TrueKw | FalseKw | LParen | MatchKw | Minus | NotKw)
        )
    }

    fn at_decl_start(&self) -> bool {
        self.at(Ident) && self.nth(1) == Some(Eq)
    }

    fn at_arm_start(&self) -> bool {
        matches!(self.peek(), Some(Ident | Number | Str | TrueKw | FalseKw))
            && !self.at_decl_start()
    }

    fn at_infix(&self) -> bool {
        matches!(
            self.peek(),
            Some(
                Plus | Minus
                    | Star
                    | Slash
                    | FloorDiv
                    | Percent
                    | EqEq
                    | NotEq
                    | Lte
                    | Lt
                    | Gte
                    | Gt
                    | AndKw
                    | OrKw
            )
        )
    }

    /// Tokens that end or resume a construct: never swallowed as garbage inside
    /// an expression, so an enclosing rule can resynchronize on them.
    fn at_sync(&self) -> bool {
        matches!(
            self.peek(),
            None | Some(Semi | RParen | Comma | DoKw | DoneKw | ThenKw | ElseKw)
        )
    }

    // ---- grammar ----

    fn root(&mut self) {
        self.builder.start_node(raw(Root));
        while !self.eof() {
            if self.at_operand_start() {
                self.expr();
            } else {
                self.error_bump("an expression");
            }
        }
        self.eat_trivia();
        self.finish_node();
    }

    /// `expr = part (';' part)* ';'?` — always produces an `Expr` node, empty
    /// (with a diagnostic) when no expression starts here.
    fn expr(&mut self) {
        self.start(Expr);
        if !self.at_operand_start() {
            self.error("an expression");
        } else {
            loop {
                self.part();
                if self.at(Semi) {
                    self.bump();
                    if !self.at_operand_start() {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
        self.finish_node();
    }

    /// `part = declaration+ statement? | statement`
    fn part(&mut self) {
        while self.at_decl_start() {
            self.declaration();
        }
        if self.at_operand_start() {
            self.statement();
        }
    }

    /// `name '=' value ';'?`
    fn declaration(&mut self) {
        self.start(Let);
        self.bump();
        self.bump();
        if self.at_operand_start() {
            self.statement();
        } else {
            self.error("a value after `=`");
        }
        if self.at(Semi) {
            self.bump();
        }
        self.finish_node();
    }

    /// A flat run `operand (infix operand)*`; precedence is resolved later, as
    /// `lower.rs` does today, which keeps recovery free of precedence.
    fn statement(&mut self) {
        let cp = self.checkpoint();
        self.operand();
        if self.at_infix() {
            self.start_at(cp, Operation);
            while self.at_infix() {
                self.bump();
                self.operand();
            }
            self.finish_node();
        }
    }

    fn operand(&mut self) {
        if self.depth >= MAX_DEPTH {
            // Give up on the rest of the file: resuming at this depth would
            // re-enter the same nesting from every enclosing level.
            self.error("a shallower expression");
            self.start(Error);
            while !self.eof() {
                self.bump();
            }
            self.finish_node();
            return;
        }
        self.depth += 1;
        if matches!(self.peek(), Some(NotKw | Minus)) {
            self.start(Negation);
            self.bump();
            self.operand();
            self.finish_node();
        } else {
            self.term();
        }
        self.depth -= 1;
    }

    fn term(&mut self) {
        let cp = self.checkpoint();
        self.primary();
        loop {
            match self.peek() {
                Some(LParen) => {
                    self.start_at(cp, Call);
                    self.bump();
                    self.arguments();
                    self.expect(RParen, "`)` to close the call");
                    self.finish_node();
                }
                Some(Dot) => {
                    self.start_at(cp, Access);
                    self.bump();
                    if self.at(Ident) {
                        self.bump();
                    } else {
                        self.error("a field name after `.`");
                    }
                    self.finish_node();
                }
                _ => break,
            }
        }
    }

    fn arguments(&mut self) {
        if self.at(RParen) {
            return;
        }
        loop {
            self.expr();
            if self.at(Comma) {
                self.bump();
                if self.at(RParen) {
                    break;
                }
            } else {
                break;
            }
        }
    }

    fn primary(&mut self) {
        match self.peek() {
            Some(Number | Str | TrueKw | FalseKw) => {
                self.start(Literal);
                self.bump();
                self.finish_node();
            }
            Some(Ident) => {
                self.start(Name);
                self.bump();
                self.finish_node();
            }
            Some(LParen) => {
                self.start(Paren);
                self.bump();
                self.expr();
                self.expect(RParen, "`)`");
                self.finish_node();
            }
            Some(MatchKw) => self.match_expr(),
            _ if self.at_sync() => self.error("an expression"),
            _ => self.error_bump("an expression"),
        }
    }

    /// `match expr do arm* (else expr)? done`
    fn match_expr(&mut self) {
        self.start(MatchExpr);
        self.bump();
        self.expr();
        self.expect(DoKw, "`do` after the matched value");
        loop {
            match self.peek() {
                None | Some(DoneKw | ElseKw | RParen) => break,
                // A binding at statement level means the author left the
                // match open; close it here instead of eating the program.
                _ if self.at_decl_start() => break,
                _ if self.at_arm_start() => self.arm(),
                _ => self.error_bump("a match arm"),
            }
        }
        if self.at(ElseKw) {
            self.bump();
            self.expr();
        }
        self.expect(DoneKw, "`done` to close `match`");
        self.finish_node();
    }

    /// `pattern then expr`
    fn arm(&mut self) {
        self.start(Arm);
        self.pattern();
        self.expect(ThenKw, "`then` after the pattern");
        self.expr();
        self.finish_node();
    }

    /// `Name`, `Name(a, b)`, or a scalar literal
    fn pattern(&mut self) {
        self.start(Pattern);
        self.bump();
        if self.at(LParen) {
            self.bump();
            while self.at(Ident) {
                self.bump();
                if self.at(Comma) {
                    self.bump();
                }
            }
            self.expect(RParen, "`)` to close the pattern");
        }
        self.finish_node();
    }
}
