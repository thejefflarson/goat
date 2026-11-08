//! The token stream editors highlight from. It is the grammar's own lexical
//! rules (`lex` in `grammar.pest`), so a highlighter cannot drift from the
//! language, and it never fails: half-typed code still yields tokens.

use crate::parser::{GoatParser, Rule};
use pest::Parser;
use std::collections::HashSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Comment,
    Keyword,
    /// `true` and `false`.
    Literal,
    Number,
    String,
    /// A name that a `tag` declaration introduces (ADR 0016); only
    /// [`highlight`] produces it, since [`tokenize`] sees no declarations.
    Tag,
    Operator,
    Name,
    /// Brackets, `=`, `:`, `;`, `|`, `,` and `.`.
    Punct,
}

/// A byte range `[start, end)` of the source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub start: usize,
    pub end: usize,
}

/// Every token of `source` in order, whitespace aside. Unrecognized characters
/// produce no token.
pub fn tokenize(source: &str) -> Vec<Token> {
    let Ok(pairs) = GoatParser::parse(Rule::lex, source) else {
        return Vec::new();
    };
    let mut tokens: Vec<Token> = pairs
        .flatten()
        .filter_map(|pair| {
            let kind = match pair.as_rule() {
                Rule::lex_comment => TokenKind::Comment,
                Rule::lex_keyword => TokenKind::Keyword,
                Rule::lex_literal => TokenKind::Literal,
                Rule::lex_number => TokenKind::Number,
                Rule::lex_string => TokenKind::String,
                Rule::lex_operator => TokenKind::Operator,
                Rule::lex_punct => TokenKind::Punct,
                Rule::lex_name | Rule::lex_word => TokenKind::Name,
                _ => return None,
            };
            let span = pair.as_span();
            Some(Token {
                kind,
                start: span.start(),
                end: span.end(),
            })
        })
        .collect();
    place_contextual_keywords(source, &mut tokens);
    tokens
}

/// [`tokenize`], with each name that `source` or `known_tags` declares as a tag
/// marked [`TokenKind::Tag`]. `known_tags` is what the host provides: the
/// prelude's tags and the vocabulary's.
pub fn highlight(source: &str, known_tags: &HashSet<String>) -> Vec<Token> {
    let mut tokens = tokenize(source);
    let mut tags: HashSet<&str> = known_tags.iter().map(String::as_str).collect();
    tags.extend(declared_tags(source, &tokens));
    for token in &mut tokens {
        if token.kind == TokenKind::Name && tags.contains(&source[token.start..token.end]) {
            token.kind = TokenKind::Tag;
        }
    }
    tokens
}

/// The cases of every `tag` declaration among `tokens` (of `source`): the
/// `Circle` and `Dot` of `tag Shape = Circle(Number) | Dot`, but not `Shape`,
/// which names the group.
pub fn declared_tags<'a>(source: &'a str, tokens: &[Token]) -> Vec<&'a str> {
    let text = |t: &Token| &source[t.start..t.end];
    let is = |t: Option<&Token>, kind, s: &str| t.is_some_and(|t| t.kind == kind && text(t) == s);
    let mut tags = Vec::new();
    let mut i = 0;
    while i < tokens.len() {
        if !is(tokens.get(i), TokenKind::Keyword, "tag") {
            i += 1;
            continue;
        }
        i += 1;
        if is(tokens.get(i + 1), TokenKind::Punct, "=") {
            i += 2;
        }
        while let Some(case) = tokens.get(i).filter(|t| t.kind == TokenKind::Name) {
            tags.push(text(case));
            i += 1;
            if is(tokens.get(i), TokenKind::Punct, "(") {
                i = after_matching_paren(source, tokens, i);
            }
            if !is(tokens.get(i), TokenKind::Punct, "|") {
                break;
            }
            i += 1;
        }
    }
    tags
}

/// The index just past the `)` that closes the `(` at `open`.
fn after_matching_paren(source: &str, tokens: &[Token], open: usize) -> usize {
    let mut depth = 0usize;
    for (i, t) in tokens.iter().enumerate().skip(open) {
        if t.kind == TokenKind::Punct {
            match &source[t.start..t.end] {
                "(" => depth += 1,
                ")" => {
                    depth -= 1;
                    if depth == 0 {
                        return i + 1;
                    }
                }
                _ => {}
            }
        }
    }
    tokens.len()
}

/// `from`, `in`, `to` and `foreign` are keywords only where the grammar says so
/// (`for_kw ~ name ~ from_kw ~ expr ~ to_kw`, `x = foreign "m" "n" (…) -> …`);
/// elsewhere they are ordinary names, so `line.to` and `{from: 1}` stay names.
fn place_contextual_keywords(source: &str, tokens: &mut [Token]) {
    let text = |t: &Token| &source[t.start..t.end];
    // Bracket depth of the open `for … from` header whose `to` is still due.
    let mut awaiting_to: Option<usize> = None;
    let mut depth = 0usize;
    for i in 0..tokens.len() {
        let token = tokens[i];
        match (token.kind, text(&token)) {
            (TokenKind::Punct, "(" | "{" | "[") => depth += 1,
            (TokenKind::Punct, ")" | "}" | "]") => depth = depth.saturating_sub(1),
            (TokenKind::Keyword, "do") => awaiting_to = None,
            (TokenKind::Name, word @ ("from" | "in" | "to" | "foreign")) => {
                let kind_at = |j: Option<usize>| j.and_then(|j| tokens.get(j)).map(|t| t.kind);
                let before = |back: usize| i.checked_sub(back);
                let is_keyword = match word {
                    "from" | "in" => {
                        kind_at(before(1)) == Some(TokenKind::Name)
                            && before(2).is_some_and(|j| {
                                tokens[j].kind == TokenKind::Keyword && text(&tokens[j]) == "for"
                            })
                    }
                    "to" => awaiting_to == Some(depth),
                    _ => {
                        before(1).is_some_and(|j| {
                            tokens[j].kind == TokenKind::Punct && text(&tokens[j]) == "="
                        }) && matches!(
                            kind_at(Some(i + 1)),
                            Some(
                                TokenKind::String
                                    | TokenKind::Number
                                    | TokenKind::Literal
                                    | TokenKind::Name
                            )
                        )
                    }
                };
                if is_keyword {
                    tokens[i].kind = TokenKind::Keyword;
                    if word == "from" {
                        awaiting_to = Some(depth);
                    }
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `(kind, text)` for each token of `source`.
    fn lex(source: &str) -> Vec<(TokenKind, &str)> {
        tokenize(source)
            .into_iter()
            .map(|t| (t.kind, &source[t.start..t.end]))
            .collect()
    }

    fn kinds_of(source: &str, wanted: TokenKind) -> Vec<&str> {
        highlight(source, &HashSet::new())
            .into_iter()
            .filter(|t| t.kind == wanted)
            .map(|t| &source[t.start..t.end])
            .collect()
    }

    #[test]
    fn classifies_the_lexical_categories() {
        use TokenKind::*;
        assert_eq!(
            lex("x = 1.5 + \"hi\" # note\nif true then not y done"),
            [
                (Name, "x"),
                (Punct, "="),
                (Number, "1.5"),
                (Operator, "+"),
                (String, "\"hi\""),
                (Comment, "# note"),
                (Keyword, "if"),
                (Literal, "true"),
                (Keyword, "then"),
                (Keyword, "not"),
                (Name, "y"),
                (Keyword, "done"),
            ]
        );
    }

    #[test]
    fn a_keyword_prefix_is_a_name() {
        use TokenKind::*;
        assert_eq!(
            lex("doner double ifx truthy"),
            [
                (Name, "doner"),
                (Name, "double"),
                (Name, "ifx"),
                (Name, "truthy")
            ]
        );
    }

    #[test]
    fn a_hash_inside_a_string_is_not_a_comment() {
        assert_eq!(lex("\"a # b\""), [(TokenKind::String, "\"a # b\"")],);
    }

    #[test]
    fn offsets_are_bytes() {
        let tokens = tokenize("\"é\" 1");
        assert_eq!((tokens[0].start, tokens[0].end), (0, 4));
        assert_eq!((tokens[1].start, tokens[1].end), (5, 6));
    }

    #[test]
    fn half_typed_code_still_tokenizes() {
        use TokenKind::*;
        let tokens = lex("if x then @ \"oops");
        assert!(tokens.contains(&(Keyword, "if")));
        assert!(tokens.contains(&(Keyword, "then")));
        assert!(tokens.contains(&(Name, "oops")));
    }

    #[test]
    fn empty_and_odd_input_do_not_fail() {
        assert!(tokenize("").is_empty());
        assert!(tokenize("\u{0}\u{feff}€").is_empty());
    }

    #[test]
    fn for_headers_make_from_to_in_keywords() {
        use TokenKind::*;
        let count = lex("for i from 1 to 3 do i done");
        assert!(count.contains(&(Keyword, "from")) && count.contains(&(Keyword, "to")));
        let each = lex("for x in xs do x done");
        assert!(each.contains(&(Keyword, "in")));
    }

    #[test]
    fn from_to_in_are_names_elsewhere() {
        use TokenKind::*;
        for source in ["line.from", "{to: 1}", "in = 2", "f(from, to)"] {
            for (kind, text) in lex(source) {
                if matches!(text, "from" | "to" | "in") {
                    assert_eq!(kind, Name, "{source}");
                }
            }
        }
        let nested = lex("for i from 1 to f({to: 2}.to) do i done");
        let to: Vec<_> = nested.iter().filter(|(_, t)| *t == "to").collect();
        assert_eq!(
            to.iter().map(|(k, _)| *k).collect::<Vec<_>>(),
            [Keyword, Name, Name]
        );
    }

    #[test]
    fn foreign_is_a_keyword_only_in_a_foreign_declaration() {
        use TokenKind::*;
        let decl = lex("f = foreign \"m\" \"n\" (Number) -> Unit");
        assert!(decl.contains(&(Keyword, "foreign")));
        assert!(!lex("x = foreign + 1").contains(&(Keyword, "foreign")));
        assert!(!lex("foreign(1)").contains(&(Keyword, "foreign")));
    }

    #[test]
    fn declared_tags_are_the_cases_not_the_group() {
        let source = "tag Empty\ntag Shape = Circle(Number) | Dot | Square\nCircle(1)";
        assert_eq!(
            kinds_of(source, TokenKind::Tag),
            ["Empty", "Circle", "Dot", "Square", "Circle"]
        );
        assert!(kinds_of(source, TokenKind::Name).contains(&"Shape"));
    }

    #[test]
    fn capitalization_alone_does_not_make_a_tag() {
        assert!(kinds_of("Circle(1)", TokenKind::Tag).is_empty());
    }

    #[test]
    fn known_tags_mark_host_provided_names() {
        let known: HashSet<String> = ["KeyDown".to_string()].into();
        let source = "match e do KeyDown(k) then 1 else 2 done";
        let tags: Vec<_> = highlight(source, &known)
            .into_iter()
            .filter(|t| t.kind == TokenKind::Tag)
            .map(|t| &source[t.start..t.end])
            .collect();
        assert_eq!(tags, ["KeyDown"]);
    }

    #[test]
    fn an_unterminated_tag_declaration_does_not_panic() {
        for source in ["tag", "tag A(", "tag A = ", "tag A(B | ", "tag A((("] {
            let _ = highlight(source, &HashSet::new());
        }
    }
}
