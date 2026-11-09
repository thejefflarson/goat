//! The words an editor can offer: keywords from the grammar, and the names the
//! turtle host puts in scope, read from the prelude's own source.

use goat_checker::hir::Builtin;
use goat_parser::lexer::{self, Token, TokenKind};
use std::collections::BTreeSet;

pub const KEYWORD: u8 = 0;
pub const FUNCTION: u8 = 1;
pub const TAG: u8 = 2;

pub struct Word {
    pub kind: u8,
    pub name: String,
    /// What follows the name in a completion list: a signature, or empty.
    pub detail: String,
}

/// Keywords, then the compiler's builtins, then the host prelude's functions,
/// then its tags (events, shapes and keys included), each group in a stable order.
pub fn words(host: &goat::HostInterface) -> Vec<Word> {
    let word = |kind, name: &str, detail: &str| Word {
        kind,
        name: name.into(),
        detail: detail.into(),
    };
    let prelude = host.prelude();
    let tokens = lexer::tokenize(prelude);
    let mut words: Vec<Word> = lexer::keywords()
        .into_iter()
        .map(|k| word(KEYWORD, k, ""))
        .collect();
    words.extend(Builtin::ALL.map(|b| {
        let detail = match b {
            Builtin::Print => "(value)",
            Builtin::Trap => "(\"message\")",
        };
        word(FUNCTION, b.name(), detail)
    }));
    words.extend(
        top_level_bindings(prelude, &tokens)
            .into_iter()
            .map(|(name, detail)| word(FUNCTION, name, &detail)),
    );
    let vocab = host.vocab();
    let tags: BTreeSet<&str> = lexer::declared_tags(prelude, &tokens)
        .into_iter()
        .chain(vocab.tag_names())
        .chain(vocab.key_tag_names())
        .collect();
    words.extend(tags.into_iter().map(|t| word(TAG, t, "")));
    words
}

/// Each name `source` binds at the start of a line (where the prelude keeps
/// its definitions, indented lines being inside one), with a signature: the
/// parameters of a `program`, or the type of a `foreign` function.
fn top_level_bindings<'a>(source: &'a str, tokens: &[Token]) -> Vec<(&'a str, String)> {
    let text = |t: &Token| &source[t.start..t.end];
    let is = |t: Option<&Token>, kind, s: &str| t.is_some_and(|t| t.kind == kind && text(t) == s);
    let mut found = Vec::new();
    for (i, token) in tokens.iter().enumerate() {
        let at_line_start = token.start == 0 || source.as_bytes()[token.start - 1] == b'\n';
        if token.kind != TokenKind::Name
            || !at_line_start
            || !is(tokens.get(i + 1), TokenKind::Punct, "=")
        {
            continue;
        }
        let value = tokens.get(i + 2);
        let detail = if is(value, TokenKind::Keyword, "program") {
            let params: Vec<&str> = tokens[i + 3..]
                .iter()
                .skip(1)
                .take_while(|t| !is(Some(t), TokenKind::Punct, ")"))
                .filter(|t| t.kind == TokenKind::Name)
                .map(text)
                .collect();
            format!("({})", params.join(", "))
        } else if is(value, TokenKind::Keyword, "foreign") {
            // `foreign "module" "name"`, then the type.
            tokens.get(i + 5).map_or(String::new(), |ty| {
                let line = &source[ty.start..];
                line[..line.find('\n').unwrap_or(line.len())].trim().into()
            })
        } else {
            String::new()
        };
        found.push((text(token), detail));
    }
    found
}

/// One entry per word: `kind: u8`, then the name and the detail, each as a
/// little-endian `u32` byte length followed by UTF-8.
pub fn encode(words: &[Word]) -> Vec<u8> {
    let mut out = Vec::new();
    for word in words {
        out.push(word.kind);
        for text in [&word.name, &word.detail] {
            out.extend_from_slice(&(text.len() as u32).to_le_bytes());
            out.extend_from_slice(text.as_bytes());
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn turtle() -> Vec<Word> {
        words(&goat::HostInterface::turtle())
    }

    fn named(words: &[Word], kind: u8) -> Vec<&str> {
        words
            .iter()
            .filter(|w| w.kind == kind)
            .map(|w| w.name.as_str())
            .collect()
    }

    fn detail<'a>(words: &'a [Word], name: &str) -> &'a str {
        &words.iter().find(|w| w.name == name).unwrap().detail
    }

    #[test]
    fn keywords_are_the_grammars() {
        assert_eq!(named(&turtle(), KEYWORD), lexer::keywords());
    }

    #[test]
    fn the_turtle_commands_come_from_the_prelude_with_their_types() {
        let words = turtle();
        let functions = named(&words, FUNCTION);
        for name in [
            "forward", "back", "left", "right", "pen_up", "pen_down", "color",
        ] {
            assert!(functions.contains(&name), "{name}");
        }
        assert_eq!(detail(&words, "forward"), "(Number) -> Unit");
        assert_eq!(detail(&words, "pen_up"), "() -> Unit");
        assert_eq!(detail(&words, "color"), "(String) -> Unit");
    }

    #[test]
    fn standard_library_functions_list_their_parameters() {
        let words = turtle();
        assert_eq!(detail(&words, "item"), "(xs, n)");
        assert_eq!(detail(&words, "nothing"), "()");
        assert_eq!(detail(&words, "sqrt"), "(Number) -> Number");
    }

    #[test]
    fn builtins_the_prelude_does_not_define_are_offered() {
        let functions = named(&turtle(), FUNCTION).join(" ");
        assert!(functions.contains("print") && functions.contains("trap"));
    }

    #[test]
    fn names_bound_inside_a_definition_are_not_offered() {
        let words = turtle();
        let functions = named(&words, FUNCTION);
        assert!(!functions.contains(&"shown") && !functions.contains(&"whole"));
    }

    #[test]
    fn tags_cover_the_preludes_events_shapes_and_keys() {
        let words = turtle();
        let tags = named(&words, TAG);
        for tag in [
            "Empty", "Link", "Tick", "KeyDown", "Polyline", "Line", "Up", "Other",
        ] {
            assert!(tags.contains(&tag), "{tag}");
        }
        assert!(!tags.contains(&"Shape"));
    }

    #[test]
    fn encoding_round_trips_the_words() {
        let encoded = encode(&[Word {
            kind: FUNCTION,
            name: "é".into(),
            detail: "(x)".into(),
        }]);
        assert_eq!(
            encoded,
            [
                &[FUNCTION, 2, 0, 0, 0][..],
                "é".as_bytes(),
                &[3, 0, 0, 0],
                b"(x)"
            ]
            .concat()
        );
    }
}
