use crate::SyntaxKind::{self, *};

/// Lex `src` into tokens that tile it exactly (trivia and unknown bytes kept),
/// so the tree can reproduce the source byte-for-byte.
pub fn lex(src: &str) -> Vec<(SyntaxKind, &str)> {
    let mut out = Vec::new();
    let mut rest = src;
    while let Some(c) = rest.chars().next() {
        let (kind, len) = if c.is_whitespace() {
            (Whitespace, take_while(rest, char::is_whitespace))
        } else if c == '#' {
            (Comment, take_while(rest, |c| c != '\n'))
        } else if c.is_ascii_digit() {
            (Number, take_while(rest, |c| c.is_ascii_digit() || c == '.'))
        } else if unicode_ident::is_xid_start(c) {
            let len = take_while(rest, unicode_ident::is_xid_continue);
            (keyword(&rest[..len]).unwrap_or(Ident), len)
        } else if c == '"' {
            (Str, string_len(rest))
        } else {
            operator(rest)
        };
        out.push((kind, &rest[..len]));
        rest = &rest[len..];
    }
    out
}

fn take_while(s: &str, f: impl Fn(char) -> bool) -> usize {
    s.char_indices()
        .find(|&(_, c)| !f(c))
        .map_or(s.len(), |(i, _)| i)
}

/// An unterminated string runs to the end of the line, so one stray quote
/// cannot swallow the rest of the file.
fn string_len(s: &str) -> usize {
    let mut chars = s.char_indices().skip(1);
    while let Some((i, c)) = chars.next() {
        match c {
            '\\' => {
                chars.next();
            }
            '"' => return i + 1,
            '\n' => return i,
            _ => {}
        }
    }
    s.len()
}

fn keyword(word: &str) -> Option<SyntaxKind> {
    Some(match word {
        "match" => MatchKw,
        "do" => DoKw,
        "done" => DoneKw,
        "then" => ThenKw,
        "else" => ElseKw,
        "not" => NotKw,
        "and" => AndKw,
        "or" => OrKw,
        "true" => TrueKw,
        "false" => FalseKw,
        _ => return None,
    })
}

fn operator(s: &str) -> (SyntaxKind, usize) {
    const TWO: [(&str, SyntaxKind); 5] = [
        ("//", FloorDiv),
        ("==", EqEq),
        ("!=", NotEq),
        ("<=", Lte),
        (">=", Gte),
    ];
    if let Some((_, k)) = TWO.iter().find(|(p, _)| s.starts_with(p)) {
        return (*k, 2);
    }
    let c = s.chars().next().expect("non-empty");
    let kind = match c {
        '=' => Eq,
        ';' => Semi,
        ',' => Comma,
        '.' => Dot,
        '(' => LParen,
        ')' => RParen,
        '+' => Plus,
        '-' => Minus,
        '*' => Star,
        '/' => Slash,
        '%' => Percent,
        '<' => Lt,
        '>' => Gt,
        _ => Unknown,
    };
    (kind, c.len_utf8())
}
