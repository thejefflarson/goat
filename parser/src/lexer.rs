//! The token stream editors highlight from, and the one the parser will read:
//! a hand-written scanner shared by the highlighter and the grammar
//! interpreter, so a highlighter cannot drift from the language. It never
//! fails: half-typed code still yields tokens.

use std::collections::HashSet;
use unicode_ident::{is_xid_continue, is_xid_start};

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
    /// Spaces, tabs and line breaks; only [`lex`] produces it.
    Whitespace,
    /// A run of characters no rule recognizes, including a `"` that opens no
    /// complete string; only [`lex`] produces it.
    Unknown,
}

/// A byte range `[start, end)` of the source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub start: usize,
    pub end: usize,
}

/// Every byte of `source` as a token, in order and without gaps, so the source
/// reconstructs from the spans. `from`, `to`, `in` and `foreign` come back as
/// [`TokenKind::Name`]; [`tokenize`] places them.
pub fn lex(source: &str) -> Vec<Token> {
    let mut tokens: Vec<Token> = Vec::new();
    let mut start = 0;
    while start < source.len() {
        let (kind, len) = next_token(&source[start..]);
        let end = start + len;
        match tokens.last_mut() {
            Some(last) if kind == TokenKind::Unknown && last.kind == TokenKind::Unknown => {
                last.end = end;
            }
            _ => tokens.push(Token { kind, start, end }),
        }
        start = end;
    }
    tokens
}

/// Every token of `source` in order, whitespace aside. Unrecognized characters
/// produce no token.
pub fn tokenize(source: &str) -> Vec<Token> {
    let mut tokens: Vec<Token> = lex(source)
        .into_iter()
        .filter(|t| !matches!(t.kind, TokenKind::Whitespace | TokenKind::Unknown))
        .collect();
    place_contextual_keywords(source, &mut tokens);
    tokens
}

/// The words that open a function literal; the grammar's `function` rule lists
/// the same three.
pub const FUNCTION_KEYWORDS: [&str; 3] = ["program", "function", "fn"];

const KEYWORDS: &[&str] = &[
    "if", "match", "then", "else", "done", "do", "start at", "repeat", "times", "for", "and", "or",
    "not", "return", "tag",
];

const LITERALS: &[&str] = &["true", "false"];

// A longer operator precedes any it begins with: the first that fits wins.
const OPERATORS: &[&str] = &[
    "==", "!=", "<=", "<", ">=", ">", "->", "//", "/", "%", "+", "*", "-", "::",
];

const PUNCTUATION: &[&str] = &[
    "(", ")", "{", "}", "[", "]", "=", ":", ";", "|", ",", "...", ".",
];

/// A name is runs of one `XID_START` and up to this many `XID_CONTINUE`
/// characters (the grammar's `unicode` rule), so a longer word continues only
/// into another `XID_START`.
const NAME_RUN: usize = 255;

/// The first rule that matches the start of `rest`, tried in the order the
/// grammar's lexical rules are.
fn next_token(rest: &str) -> (TokenKind, usize) {
    whitespace(rest)
        .map(|n| (TokenKind::Whitespace, n))
        .or_else(|| comment(rest).map(|n| (TokenKind::Comment, n)))
        .or_else(|| string(rest).map(|n| (TokenKind::String, n)))
        .or_else(|| number(rest).map(|n| (TokenKind::Number, n)))
        .or_else(|| word(rest, LITERALS).map(|n| (TokenKind::Literal, n)))
        .or_else(|| {
            word(rest, &FUNCTION_KEYWORDS)
                .or_else(|| word(rest, KEYWORDS))
                .map(|n| (TokenKind::Keyword, n))
        })
        .or_else(|| name(rest).map(|n| (TokenKind::Name, n)))
        .or_else(|| prefix(rest, OPERATORS).map(|n| (TokenKind::Operator, n)))
        .or_else(|| prefix(rest, PUNCTUATION).map(|n| (TokenKind::Punct, n)))
        .unwrap_or_else(|| {
            let first = rest.chars().next().map_or(0, char::len_utf8);
            (TokenKind::Unknown, first)
        })
}

fn whitespace(rest: &str) -> Option<usize> {
    let len = rest.len() - rest.trim_start_matches([' ', '\t', '\n', '\r']).len();
    (len > 0).then_some(len)
}

/// `#` to the end of the line, not including the line break.
fn comment(rest: &str) -> Option<usize> {
    rest.starts_with('#')
        .then(|| rest.find(['\n', '\r']).unwrap_or(rest.len()))
}

/// A `"…"` literal; a backslash escapes the next character, quote included.
fn string(rest: &str) -> Option<usize> {
    let mut chars = rest.strip_prefix('"')?.char_indices();
    while let Some((i, c)) = chars.next() {
        match c {
            '"' => return Some(i + 2),
            '\\' => {
                chars.next()?;
            }
            _ => {}
        }
    }
    None
}

/// Digits with an optional fraction and exponent, or a bare fraction (`.5`).
/// There is no sign: `5 -1` is a subtraction.
fn number(rest: &str) -> Option<usize> {
    let bytes = rest.as_bytes();
    let digits = |from: usize| {
        bytes
            .get(from..)
            .map_or(0, |b| b.iter().take_while(|c| c.is_ascii_digit()).count())
    };
    let whole = digits(0);
    let mut end = if whole > 0 {
        match bytes.get(whole) {
            Some(b'.') => whole + 1 + digits(whole + 1),
            _ => whole,
        }
    } else if bytes.first() == Some(&b'.') && digits(1) > 0 {
        1 + digits(1)
    } else {
        return None;
    };
    if matches!(bytes.get(end), Some(b'e' | b'E')) {
        let sign = usize::from(matches!(bytes.get(end + 1), Some(b'+' | b'-')));
        let exponent = digits(end + 1 + sign);
        if exponent > 0 {
            end += 1 + sign + exponent;
        }
    }
    Some(end)
}

fn name(rest: &str) -> Option<usize> {
    let mut end = 0;
    while let Some(c) = rest[end..].chars().next().filter(|&c| is_xid_start(c)) {
        end += c.len_utf8();
        end += rest[end..]
            .chars()
            .take(NAME_RUN - 1)
            .take_while(|&c| is_xid_continue(c))
            .map(char::len_utf8)
            .sum::<usize>();
    }
    (end > 0).then_some(end)
}

/// One of `words` at the start of `rest`, not followed by an identifier
/// character: `done` is a keyword, `doner` a name.
fn word(rest: &str, words: &[&str]) -> Option<usize> {
    words.iter().find_map(|w| {
        let after = rest.strip_prefix(w)?;
        (!after.chars().next().is_some_and(is_xid_continue)).then_some(w.len())
    })
}

/// The first of `candidates` that `rest` starts with.
fn prefix(rest: &str, candidates: &[&str]) -> Option<usize> {
    candidates
        .iter()
        .find(|c| rest.starts_with(**c))
        .map(|c| c.len())
}

/// [`tokenize`], with each name that `source` or `known_tags` declares as a tag
/// marked [`TokenKind::Tag`], and `self` marked [`TokenKind::Keyword`].
/// `known_tags` is what the host provides: the prelude's tags and the
/// vocabulary's. `self` stays a [`TokenKind::Name`] to the parser, which reads
/// [`lex`]; the checker reserves it (ADR 0034), so an editor can show it as the
/// keyword it acts as.
pub fn highlight(source: &str, known_tags: &HashSet<String>) -> Vec<Token> {
    let mut tokens = tokenize(source);
    let mut tags: HashSet<&str> = known_tags.iter().map(String::as_str).collect();
    tags.extend(declared_tags(source, &tokens));
    for token in &mut tokens {
        if token.kind != TokenKind::Name {
            continue;
        }
        let word = &source[token.start..token.end];
        if tags.contains(word) {
            token.kind = TokenKind::Tag;
        } else if word == "self" {
            token.kind = TokenKind::Keyword;
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

/// The words an editor may offer as keywords: the reserved words some
/// construct uses (`return` and `start at` are reserved but unused, so they are
/// left out), then the contextual ones (`from`, `to`, `in`, `foreign`).
pub fn keywords() -> Vec<&'static str> {
    FUNCTION_KEYWORDS
        .into_iter()
        .chain(KEYWORDS.iter().copied())
        .filter(|w| !matches!(*w, "return" | "start at"))
        .chain(LITERALS.iter().copied())
        .chain(["from", "to", "in", "foreign"])
        .collect()
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
    fn lexed(source: &str) -> Vec<(TokenKind, &str)> {
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
            lexed("x = 1.5 + \"hi\" # note\nif true then not y done"),
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
            lexed("doner double ifx truthy"),
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
        assert_eq!(lexed("\"a # b\""), [(TokenKind::String, "\"a # b\"")],);
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
        let tokens = lexed("if x then @ \"oops");
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
        let count = lexed("for i from 1 to 3 do i done");
        assert!(count.contains(&(Keyword, "from")) && count.contains(&(Keyword, "to")));
        let each = lexed("for x in xs do x done");
        assert!(each.contains(&(Keyword, "in")));
    }

    #[test]
    fn from_to_in_are_names_elsewhere() {
        use TokenKind::*;
        for source in ["line.from", "{to: 1}", "in = 2", "f(from, to)"] {
            for (kind, text) in lexed(source) {
                if matches!(text, "from" | "to" | "in") {
                    assert_eq!(kind, Name, "{source}");
                }
            }
        }
        let nested = lexed("for i from 1 to f({to: 2}.to) do i done");
        let to: Vec<_> = nested.iter().filter(|(_, t)| *t == "to").collect();
        assert_eq!(
            to.iter().map(|(k, _)| *k).collect::<Vec<_>>(),
            [Keyword, Name, Name]
        );
    }

    #[test]
    fn self_is_a_name_to_the_parser_and_a_keyword_to_the_highlighter() {
        let source = "program(self) do self.x done selfish";
        let kinds_of_self = |tokens: Vec<Token>| {
            tokens
                .iter()
                .filter(|t| &source[t.start..t.end] == "self")
                .map(|t| t.kind)
                .collect::<Vec<_>>()
        };
        assert_eq!(
            kinds_of_self(tokenize(source)),
            [TokenKind::Name, TokenKind::Name]
        );
        assert_eq!(
            kinds_of_self(highlight(source, &HashSet::new())),
            [TokenKind::Keyword, TokenKind::Keyword]
        );
        let selfish = highlight(source, &HashSet::new())
            .into_iter()
            .find(|t| &source[t.start..t.end] == "selfish")
            .unwrap();
        assert_eq!(selfish.kind, TokenKind::Name);
    }

    #[test]
    fn foreign_is_a_keyword_only_in_a_foreign_declaration() {
        use TokenKind::*;
        let decl = lexed("f = foreign \"m\" \"n\" (Number) -> Unit");
        assert!(decl.contains(&(Keyword, "foreign")));
        assert!(!lexed("x = foreign + 1").contains(&(Keyword, "foreign")));
        assert!(!lexed("foreign(1)").contains(&(Keyword, "foreign")));
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
    fn keywords_are_the_reserved_words_in_use_and_the_contextual_ones() {
        assert_eq!(
            keywords(),
            [
                "program", "function", "fn", "if", "match", "then", "else", "done", "do", "repeat",
                "times", "for", "and", "or", "not", "tag", "true", "false", "from", "to", "in",
                "foreign",
            ]
        );
    }

    #[test]
    fn the_grammar_lists_exactly_the_function_keywords() {
        let rule = include_str!("../../grammar/goat.peg")
            .lines()
            .find(|l| l.starts_with("function <- "))
            .expect("the grammar has a function rule");
        let alternation = &rule["function <- (".len()..rule.find(')').unwrap()];
        let listed: Vec<_> = alternation
            .split(" / ")
            .map(|w| w.trim_matches('\''))
            .collect();
        assert_eq!(listed, FUNCTION_KEYWORDS);
    }

    #[test]
    fn an_unterminated_tag_declaration_does_not_panic() {
        for source in ["tag", "tag A(", "tag A = ", "tag A(B | ", "tag A((("] {
            let _ = highlight(source, &HashSet::new());
        }
    }

    #[test]
    fn strings_take_escapes_and_stop_at_the_closing_quote() {
        use TokenKind::*;
        assert_eq!(lex(r#""a\"b" c"#)[0], tok(String, 0, 6));
        assert_eq!(lex(r#""a\\" "b""#)[0], tok(String, 0, 5));
        assert_eq!(lex("\"a\nb\"")[0].kind, String);
        assert_eq!(lex("\"\"")[0], tok(String, 0, 2));
    }

    #[test]
    fn an_unterminated_string_is_unknown_and_lexing_resumes() {
        use TokenKind::*;
        for source in ["\"abc", "\"abc\\", "\"abc\\\""] {
            assert_eq!(lex(source)[0], tok(Unknown, 0, 1), "{source}");
        }
        assert_eq!(
            lex("\"ab"),
            [tok(Unknown, 0, 1), tok(Name, 1, 3)],
            "the quote alone is skipped and the rest lexes as usual"
        );
    }

    #[test]
    fn numbers_take_a_fraction_and_an_exponent_but_no_sign() {
        use TokenKind::*;
        for number in ["7", "1.5", "1.", ".5", "1e5", "2.5E-3", "1.e+2", ".5e3"] {
            assert_eq!(lex(number), [tok(Number, 0, number.len())], "{number}");
        }
        assert_eq!(
            lex("5 -1"),
            [
                tok(Number, 0, 1),
                tok(Whitespace, 1, 2),
                tok(Operator, 2, 3),
                tok(Number, 3, 4)
            ]
        );
        assert_eq!(
            lex("1e"),
            [tok(Number, 0, 1), tok(Name, 1, 2)],
            "an exponent needs digits"
        );
        assert_eq!(lex("1..2"), [tok(Number, 0, 2), tok(Number, 2, 4)]);
        assert_eq!(lex("."), [tok(Punct, 0, 1)]);
    }

    #[test]
    fn a_comment_ends_at_either_kind_of_line_break() {
        use TokenKind::*;
        assert_eq!(lex("#a\rb")[0], tok(Comment, 0, 2));
        assert_eq!(lex("#a\r\nb")[0], tok(Comment, 0, 2));
        assert_eq!(lex("#a\nb")[0], tok(Comment, 0, 2));
        assert_eq!(lex("# to the end"), [tok(Comment, 0, 12)]);
    }

    #[test]
    fn operators_and_punctuation_take_the_longest_form() {
        use TokenKind::*;
        let cases = [
            ("==", Operator),
            ("!=", Operator),
            ("<=", Operator),
            (">=", Operator),
            ("->", Operator),
            ("//", Operator),
            ("::", Operator),
            (":", Punct),
            ("...", Punct),
            ("=", Punct),
        ];
        for (text, kind) in cases {
            assert_eq!(lex(text), [tok(kind, 0, text.len())], "{text}");
        }
        assert_eq!(lex("!"), [tok(Unknown, 0, 1)]);
        assert_eq!(lex(":::"), [tok(Operator, 0, 2), tok(Punct, 2, 3)]);
        assert_eq!(lex("a::b").len(), 3);
        let spaced = lex("a: :b");
        assert_eq!((spaced[1], spaced[3]), (tok(Punct, 1, 2), tok(Punct, 3, 4)));
    }

    #[test]
    fn start_at_is_one_keyword_only_with_a_single_space() {
        use TokenKind::*;
        assert_eq!(lex("start at"), [tok(Keyword, 0, 8)]);
        assert_eq!(lex("start  at")[0].kind, Name);
        assert_eq!(lex("start atx")[0].kind, Name);
    }

    #[test]
    fn names_may_be_unicode_and_stop_at_the_first_non_identifier_character() {
        use TokenKind::*;
        assert_eq!(lex("héllo_2"), [tok(Name, 0, 8)]);
        assert_eq!(lex("a-b").len(), 3);
        assert_eq!(lex("_x"), [tok(Unknown, 0, 1), tok(Name, 1, 2)]);
        let long = "a".repeat(300);
        assert_eq!(lex(&long), [tok(Name, 0, 300)]);
        let digit_after_a_full_run = format!("{}1", "a".repeat(NAME_RUN));
        assert_eq!(
            lex(&digit_after_a_full_run),
            [tok(Name, 0, NAME_RUN), tok(Number, NAME_RUN, NAME_RUN + 1)]
        );
    }

    #[test]
    fn unknown_characters_merge_into_one_token() {
        use TokenKind::*;
        assert_eq!(lex("a@€!b").len(), 3);
        assert_eq!(lex("@€"), [tok(Unknown, 0, 4)]);
    }

    #[test]
    fn lex_covers_every_byte_exactly_once() {
        for source in corpus() {
            let mut next = 0;
            for t in lex(&source) {
                assert_eq!(t.start, next, "gap before {t:?}");
                assert!(t.end > t.start, "empty token {t:?}");
                assert!(source.is_char_boundary(t.end));
                next = t.end;
            }
            assert_eq!(next, source.len());
        }
    }

    fn tok(kind: TokenKind, start: usize, end: usize) -> Token {
        Token { kind, start, end }
    }

    fn read_goat_files(dir: &str) -> Vec<String> {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(dir);
        let mut files: Vec<_> = std::fs::read_dir(dir)
            .expect("corpus directory")
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().is_some_and(|x| x == "goat"))
            .collect();
        files.sort();
        files
            .iter()
            .map(|p| std::fs::read_to_string(p).expect("readable"))
            .collect()
    }

    /// The example programs, the prelude, and the Rust test sources that quote
    /// goat (whole files and line by line), which also stress odd characters.
    fn corpus() -> Vec<String> {
        let mut sources = read_goat_files("../examples");
        sources.extend(read_goat_files("../prelude"));
        for rust in [
            include_str!("interp.rs"),
            include_str!("../../checker/src/lib.rs"),
            include_str!("lexer.rs"),
        ] {
            sources.push(rust.to_string());
            sources.extend(rust.lines().map(String::from));
        }
        sources
    }
}
