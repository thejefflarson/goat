//! Writes what `parser::interp::parse` says of every source `lex_dump` writes
//! (and of token-level breakages of some of them), for the differential test of
//! the Coq parser (`proofs/GoatPegExtract.v` extracts `parse_fuel`, and
//! `differential/parse_driver.ml` compares it with this):
//!
//!     P <TAB> TOKENS <TAB> TREE
//!
//! TOKENS are the parser's tokens (trivia dropped) separated by spaces: `I` and
//! the text for a name, `N` for a number, `S` for a string, `Y` and the text for
//! every other token; a text writes its space, tab, line break and `%` as `%` and
//! two hex digits. TREE is `ERR` when `parse` fails, else the parse tree in
//! parentheses: a node is its rule's name and its children, a leaf is its token
//! as above. A source with a code point no token takes, or one `parse` refuses
//! for nesting, is not written.
//!
//! Input is `lex_dump`'s output on standard input (only its `L` lines are read):
//!
//!     lex_dump < sources.txt | parse_dump > parse.tsv

use goat_parser::cst::{Child, Node};
use goat_parser::interp::parse;
use goat_parser::lexer::{Token, TokenKind, lex};
use std::io::{BufRead, Write};

/// Every this-many-th source that parses also gets its tokens broken.
const BREAK_EVERY: usize = 17;
const BREAKS_PER_SOURCE: usize = 8;

/// A keyword such as `start at` holds whitespace, so a token's text escapes the
/// characters that separate tokens and lines, and `%`.
fn escaped(text: &str) -> String {
    let mut out = String::new();
    for c in text.chars() {
        match c {
            '%' | ' ' | '\t' | '\n' | '\r' => out.push_str(&format!("%{:02X}", c as u32)),
            _ => out.push(c),
        }
    }
    out
}

fn token_text(source: &str, token: &Token) -> String {
    let text = escaped(&source[token.start..token.end]);
    match token.kind {
        TokenKind::Name => format!("I{text}"),
        TokenKind::Number => "N".into(),
        TokenKind::String => "S".into(),
        _ => format!("Y{text}"),
    }
}

fn tree(source: &str, node: Node<'_>, out: &mut String) {
    out.push('(');
    out.push_str(node.kind());
    for child in node.elements() {
        match child {
            Child::Node(inner) => {
                out.push(' ');
                tree(source, inner, out);
            }
            Child::Token(token) if !token.is_trivia() => {
                out.push(' ');
                out.push_str(&token_text(source, &token));
            }
            Child::Token(_) => {}
        }
    }
    out.push(')');
}

/// The line for a source; `None` when it is not one the comparison covers.
fn line(source: &str) -> Option<(String, bool)> {
    let tokens = lex(source);
    if tokens.iter().any(|t| t.kind == TokenKind::Unknown) {
        return None;
    }
    let spelled: Vec<String> = tokens
        .iter()
        .filter(|t| !t.is_trivia())
        .map(|t| token_text(source, t))
        .collect();
    match parse(source) {
        Ok(cst) => {
            let mut out = String::new();
            tree(source, cst.root(), &mut out);
            Some((format!("P\t{}\t{out}", spelled.join(" ")), true))
        }
        Err(e) if e.too_deep => None,
        Err(_) => Some((format!("P\t{}\tERR", spelled.join(" ")), false)),
    }
}

/// The source with the token at `index` dropped, doubled, or swapped with the next.
fn broken(source: &str, index: usize, how: usize) -> Option<String> {
    let tokens: Vec<Token> = lex(source).into_iter().filter(|t| !t.is_trivia()).collect();
    let this = tokens.get(index)?;
    let (head, tail) = (&source[..this.start], &source[this.end..]);
    let text = &source[this.start..this.end];
    Some(match how {
        0 => format!("{head}{tail}"),
        1 => format!("{head}{text} {text}{tail}"),
        _ => {
            let next = tokens.get(index + 1)?;
            let (a, b) = (text, &source[next.start..next.end]);
            format!("{head}{b} {a}{}", &source[next.end..])
        }
    })
}

fn main() {
    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    let mut parsed = 0usize;
    for input in std::io::stdin().lock().lines() {
        let input = input.expect("standard input");
        let mut fields = input.split('\t');
        if fields.next() != Some("L") {
            continue;
        }
        let source: String = fields
            .next()
            .expect("code points")
            .split_whitespace()
            .filter_map(|n| char::from_u32(n.parse().expect("a code point")))
            .collect();
        let Some((text, ok)) = line(&source) else {
            continue;
        };
        writeln!(out, "{text}").unwrap();
        if !ok {
            continue;
        }
        parsed += 1;
        if parsed % BREAK_EVERY != 0 || source.len() > 4000 {
            continue;
        }
        let count = lex(&source).iter().filter(|t| !t.is_trivia()).count();
        let stride = (count / BREAKS_PER_SOURCE).max(1);
        for index in (0..count).step_by(stride) {
            for how in 0..3 {
                if let Some((text, _)) = broken(&source, index, how).as_deref().and_then(line) {
                    writeln!(out, "{text}").unwrap();
                }
            }
        }
    }
}
