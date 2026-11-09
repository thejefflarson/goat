//! Cursor queries over a recovered [`Cst`] (ADR 0022 §4): what encloses an
//! offset, and what the cursor is about to type. They read only the tree and its
//! tokens, so they answer on broken input; the checker adds the types.
//!
//! Spans in a recovered tree can end short of the cursor: a `MISSING` node sits
//! right after the last token placed, so `a = ` ends before the space the cursor
//! is in. A node that ends in a `MISSING` piece is *open*, and it still encloses
//! a cursor that only trivia separates from its end.

use crate::cst::{Child, Cst, Match, Node};
use crate::lexer::{self, Token, TokenKind};
use std::ops::Range;

/// What the cursor is positioned to type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Role {
    /// An expression: a binding's value, an argument, a statement.
    Operand,
    /// A member after `.`, of the operand that precedes the dot.
    Field { base: Range<usize> },
    /// The head of a `match` arm, a tag. `covered` holds the tags the other
    /// arms already match.
    ArmPattern {
        scrutinee: Option<Range<usize>>,
        covered: Vec<String>,
    },
    /// A name being introduced, or a place where nothing completes: a
    /// comment, a string, a number.
    Nothing,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokenContext {
    /// The part of the word before the cursor; empty when none has been typed.
    pub prefix: Range<usize>,
    /// The last token before the prefix, trivia aside.
    pub previous: Option<Token>,
    pub role: Role,
    /// The keywords the grammar requires at the cursor, innermost first: the
    /// `then` a half-written `if` waits for.
    pub expected: Vec<&'static str>,
}

impl Cst {
    /// The nodes that enclose `offset`, from the root to the innermost. When
    /// the cursor sits where a required piece is missing, that `MISSING` node
    /// comes last.
    pub fn enclosing_path(&self, offset: usize) -> Vec<Node<'_>> {
        path_at(self, &self.root().tokens(), offset)
    }

    /// The word being typed at `offset`, the token before it, and the role the
    /// cursor's position gives it.
    pub fn token_context(&self, offset: usize) -> TokenContext {
        let tokens = self.root().tokens();
        let source = self.source();

        let word = tokens.iter().find(|t| {
            t.start < offset
                && offset <= t.end
                && matches!(
                    t.kind,
                    TokenKind::Name | TokenKind::Keyword | TokenKind::Literal | TokenKind::Tag
                )
        });
        let prefix = word.map_or(offset..offset, |t| t.start..offset);
        let previous = tokens
            .iter()
            .rev()
            .find(|t| !t.is_trivia() && t.end <= prefix.start)
            .copied();
        let opaque = tokens.iter().any(|t| {
            t.start < offset
                && match t.kind {
                    TokenKind::Comment | TokenKind::Number => offset <= t.end,
                    TokenKind::String => offset < t.end,
                    _ => false,
                }
        }) || previous.is_some_and(|t| t.kind == TokenKind::Unknown);

        let path = path_at(self, &tokens, offset);
        let missing = missing_here(&path, &tokens, prefix.start);
        let keywords = lexer::keywords();
        let expected: Vec<&'static str> = missing
            .iter()
            .filter_map(|m| m.expected())
            .filter(|e| keywords.contains(e))
            .collect();

        let previous_text = previous.map(|t| &source[t.start..t.end]);
        let role = if opaque {
            Role::Nothing
        } else if previous_text == Some(".") {
            field(&path)
        } else if let Some(arm) = arm_pattern(&path, previous, source, prefix.start, offset) {
            arm
        } else if binder_position(&path, &tokens, source, previous_text, prefix.start)
            || missing
                .first()
                .and_then(|m| m.expected())
                .is_some_and(|e| keywords.contains(&e))
        {
            Role::Nothing
        } else {
            Role::Operand
        };
        TokenContext {
            prefix,
            previous,
            role,
            expected,
        }
    }
}

fn path_at<'a>(cst: &'a Cst, tokens: &[Token], offset: usize) -> Vec<Node<'a>> {
    let mut path = vec![cst.root()];
    loop {
        let node = *path.last().expect("the root is first");
        let inside = node
            .children()
            .rfind(|c| !c.is("MISSING") && encloses(*c, tokens, offset));
        match inside {
            Some(child) => path.push(child),
            None => {
                path.extend(
                    node.children().find(|c| {
                        c.is("MISSING") && trivia_between(tokens, c.span().start, offset)
                    }),
                );
                return path;
            }
        }
    }
}

fn encloses(node: Node, tokens: &[Token], offset: usize) -> bool {
    let span = node.span();
    span.start <= offset
        && (offset <= span.end || (node.is_open() && trivia_between(tokens, span.end, offset)))
}

/// Whether nothing but trivia lies between `from` and `to`.
fn trivia_between(tokens: &[Token], from: usize, to: usize) -> bool {
    from <= to
        && !tokens
            .iter()
            .any(|t| !t.is_trivia() && t.start >= from && t.end <= to)
}

impl Node<'_> {
    /// Whether the node's last piece is a `MISSING` node, directly or through
    /// its last child: a construct the user has yet to finish.
    pub fn is_open(&self) -> bool {
        let last = self
            .elements()
            .filter(|e| !matches!(e, Child::Token(t) if t.is_trivia()))
            .last();
        match last {
            Some(Child::Node(n)) => n.is("MISSING") || n.is_open(),
            _ => false,
        }
    }
}

/// The `MISSING` nodes right before the cursor, innermost enclosing node first.
fn missing_here<'a>(path: &[Node<'a>], tokens: &[Token], offset: usize) -> Vec<Node<'a>> {
    path.iter()
        .rev()
        .flat_map(|n| n.children_of("MISSING"))
        .filter(|m| trivia_between(tokens, m.span().start, offset))
        .collect()
}

impl Node<'_> {
    /// The span without the trivia around it.
    pub fn trimmed_span(&self) -> Range<usize> {
        let tokens = self.tokens();
        let mut real = tokens.iter().filter(|t| !t.is_trivia());
        match (real.next(), real.next_back()) {
            (Some(first), Some(last)) => first.start..last.end,
            (Some(only), None) => only.start..only.end,
            _ => self.span(),
        }
    }
}

fn is_postfix(node: &Node) -> bool {
    matches!(node.kind(), "access" | "call")
}

/// After a `.`: the operand chain the access hangs off.
fn field(path: &[Node]) -> Role {
    let Some(at) = path.iter().rposition(|n| n.is("access")) else {
        return Role::Nothing;
    };
    let Some(parent) = at.checked_sub(1).map(|p| path[p]) else {
        return Role::Nothing;
    };
    let siblings: Vec<Node> = parent.children().collect();
    let Some(place) = siblings
        .iter()
        .position(|n| n.is("access") && n.span() == path[at].span())
    else {
        return Role::Nothing;
    };
    let mut head = place;
    while head > 0 && is_postfix(&siblings[head - 1]) {
        head -= 1;
    }
    if head == 0 {
        return Role::Nothing;
    }
    let (first, last) = (
        siblings[head - 1].trimmed_span(),
        siblings[place - 1].trimmed_span(),
    );
    Role::Field {
        base: first.start..last.end,
    }
}

/// Whether the token ends an operand, so that an operand cannot continue it.
fn ends_operand(token: Option<Token>, source: &str) -> bool {
    token.is_some_and(|t| {
        let text = &source[t.start..t.end];
        match t.kind {
            TokenKind::Name
            | TokenKind::Number
            | TokenKind::String
            | TokenKind::Literal
            | TokenKind::Tag => true,
            TokenKind::Punct => matches!(text, ")" | "]" | "}"),
            TokenKind::Keyword => text == "done",
            _ => false,
        }
    })
}

/// The tag a pattern matches, when it names one.
fn pattern_tag(pattern: Node) -> Option<String> {
    match pattern.kind() {
        "pattern" => pattern.child("name").map(|n| n.text().to_string()),
        "list_pattern" => Some(
            if pattern.child("name").is_some() || pattern.text().contains("...") {
                "Link".into()
            } else {
                "Empty".into()
            },
        ),
        _ => None,
    }
}

/// The head of a `match` arm: the cursor is past the `do`, before any `done`,
/// and either typing a pattern or where one would start.
fn arm_pattern(
    path: &[Node],
    previous: Option<Token>,
    source: &str,
    at: usize,
    cursor: usize,
) -> Option<Role> {
    let at_match = path.iter().rposition(|n| n.is("match_expr"))?;
    let node = path[at_match];
    let word = |t: &Token| &source[t.start..t.end];
    let own: Vec<Token> = node
        .elements()
        .filter_map(|e| match e {
            Child::Token(t) if !t.is_trivia() => Some(t),
            _ => None,
        })
        .collect();
    let do_token = own
        .iter()
        .find(|t| t.kind == TokenKind::Keyword && word(t) == "do" && t.end <= at)?;
    if !node.is_open() && cursor >= own.last()?.end {
        return None;
    }
    let view = Match::cast(node)?;
    let ends = ends_operand(previous, source);
    let after = &path[at_match + 1..];
    let typing = match after.first() {
        Some(arm) if arm.is("arm") => {
            let inside = &after[1..];
            let in_head = inside.first().is_some_and(|n| {
                matches!(n.kind(), "pattern" | "list_pattern" | "literal_pattern")
            });
            if in_head {
                let opening = matches!(previous.map(|t| word(&t)), Some("(" | ","));
                if opening || inside.iter().any(|n| n.is("labels")) {
                    return None;
                }
            } else if arm.is_open() || !ends {
                return None;
            }
            in_head.then(|| arm.span())
        }
        Some(other) if !other.is("MISSING") => return None,
        _ => {
            let first = previous.is_some_and(|t| t.start == do_token.start);
            if !(first || ends && view.arms().next().is_some()) {
                return None;
            }
            None
        }
    };
    let covered = view
        .arms()
        .filter(|arm| Some(arm.node().span()) != typing)
        .filter_map(|arm| arm.pattern().and_then(pattern_tag))
        .collect();
    Some(Role::ArmPattern {
        scrutinee: view.scrutinee().map(|s| s.node().trimmed_span()),
        covered,
    })
}

const NAMING: [&str; 9] = [
    "params",
    "labels",
    "list_pattern",
    "record_pattern",
    "tag_decl",
    "tag_case",
    "group_name",
    "field_type",
    "rest_binding",
];

/// The bracket the cursor sits in, and the token before it. Recovery can leave
/// a trailing `,` outside the node it belongs to, so this reads the tokens.
fn open_bracket<'s>(
    tokens: &[Token],
    source: &'s str,
    at: usize,
) -> Option<(&'s str, Option<&'s str>)> {
    let text = |t: &Token| &source[t.start..t.end];
    let mut depth = 0;
    let mut significant = tokens
        .iter()
        .filter(|t| !t.is_trivia() && t.end <= at)
        .rev();
    while let Some(token) = significant.next() {
        match text(token) {
            ")" | "]" | "}" => depth += 1,
            "(" | "[" | "{" if depth > 0 => depth -= 1,
            opener @ ("(" | "[" | "{") => return Some((opener, significant.next().map(text))),
            _ => {}
        }
    }
    None
}

/// Whether the cursor names something new: a parameter, a pattern's binding, a
/// tag, a record field, a loop variable.
fn binder_position(
    path: &[Node],
    tokens: &[Token],
    source: &str,
    previous: Option<&str>,
    at: usize,
) -> bool {
    let mut nested = path.iter().rev().take_while(|n| !n.is("expr"));
    if nested.any(|n| NAMING.contains(&n.kind())) {
        return true;
    }
    let opening = matches!(previous, Some("(" | ","));
    match open_bracket(tokens, source, at) {
        Some(("(", Some("program" | "function" | "fn"))) if opening => return true,
        Some(("{", _)) if matches!(previous, Some("{" | ",")) => return true,
        _ => {}
    }
    let mut innermost = path.iter().rev().filter(|n| !n.is("MISSING"));
    let (last, parent) = (innermost.next(), innermost.next());
    match (last.map(|n| n.kind()), parent.map(|n| n.kind())) {
        (Some("name"), Some("field")) => true,
        (Some("pattern"), _) => opening,
        _ => matches!(
            previous,
            Some("tag" | "for" | "program" | "function" | "fn")
        ),
    }
}
