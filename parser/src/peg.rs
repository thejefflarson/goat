//! The grammar as data: `grammar/goat.peg` read into a tree of PEG combinators
//! that [`crate::interp`] walks, recovery annotations included. The reader
//! accepts only a well-formed grammar and panics on a malformed one, which is a
//! bug in the file, not in a user's program.

use crate::lexer::TokenKind;
use std::collections::HashMap;
use std::sync::OnceLock;

const SOURCE: &str = include_str!("../../grammar/goat.peg");

pub type RuleId = u16;

/// What one token must be for a terminal to match it.
#[derive(Debug, PartialEq, Eq)]
pub enum Terminal {
    /// A token with exactly this text. A word is a keyword only where the
    /// grammar asks for it, so `from`, `to`, `in` and `foreign` stay names
    /// everywhere else.
    Text(String),
    Kind(TokenKind),
    EndOfInput,
}

#[derive(Debug)]
pub enum Expr {
    Seq(Vec<Expr>),
    Choice(Vec<Expr>),
    Star(Box<Expr>),
    Plus(Box<Expr>),
    Opt(Box<Expr>),
    /// `a@expect`: required, and recovered from when absent.
    Expect(Box<Expr>),
    Terminal(Terminal),
    Rule(RuleId),
}

#[derive(Debug)]
pub struct Rule {
    pub name: String,
    /// A silent rule makes no node: its pieces join the enclosing one.
    pub silent: bool,
    /// `@sync`: tokens where panic-mode skipping inside this rule stops.
    pub sync: Vec<String>,
    /// `@anchor`: tokens recovery inside this rule must not consume.
    pub anchors: Vec<String>,
    /// `@nest`: one level of the nesting the parser bounds.
    pub nest: bool,
    pub body: Expr,
}

#[derive(Debug)]
pub struct Grammar {
    pub rules: Vec<Rule>,
    pub root: RuleId,
    ids: HashMap<String, RuleId>,
}

impl Grammar {
    /// The grammar embedded in the binary, read once.
    pub fn goat() -> &'static Grammar {
        static GOAT: OnceLock<Grammar> = OnceLock::new();
        GOAT.get_or_init(|| Grammar::read(SOURCE).expect("grammar/goat.peg is well formed"))
    }

    pub fn read(text: &str) -> Result<Grammar, String> {
        Reader::new(text)?.grammar()
    }

    pub fn id(&self, name: &str) -> Option<RuleId> {
        self.ids.get(name).copied()
    }

    pub fn rule(&self, id: RuleId) -> &Rule {
        &self.rules[usize::from(id)]
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum Lex {
    Ident(String),
    Quoted(String),
    Arrow,
    Slash,
    Star,
    Plus,
    Question,
    Open,
    Close,
    At,
}

fn lex(text: &str) -> Result<Vec<Lex>, String> {
    let mut out = Vec::new();
    let mut chars = text.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        match c {
            c if c.is_whitespace() => {}
            '#' => while chars.next_if(|&(_, c)| c != '\n').is_some() {},
            '<' if chars.next_if(|&(_, c)| c == '-').is_some() => out.push(Lex::Arrow),
            '/' => out.push(Lex::Slash),
            '*' => out.push(Lex::Star),
            '+' => out.push(Lex::Plus),
            '?' => out.push(Lex::Question),
            '@' => out.push(Lex::At),
            '(' => out.push(Lex::Open),
            ')' => out.push(Lex::Close),
            '\'' => {
                let rest = &text[i + 1..];
                let len = rest.find('\'').ok_or("unterminated quote")?;
                out.push(Lex::Quoted(rest[..len].to_string()));
                for _ in 0..=len {
                    chars.next();
                }
            }
            c if c.is_ascii_alphabetic() || c == '_' => {
                let mut end = i + 1;
                while let Some(&(j, c)) = chars.peek() {
                    if !(c.is_ascii_alphanumeric() || c == '_') {
                        break;
                    }
                    end = j + 1;
                    chars.next();
                }
                out.push(Lex::Ident(text[i..end].to_string()));
            }
            c => return Err(format!("unexpected `{c}` in grammar")),
        }
    }
    Ok(out)
}

/// A rule body before its references to other rules are resolved to ids.
enum Draft {
    Seq(Vec<Draft>),
    Choice(Vec<Draft>),
    Star(Box<Draft>),
    Plus(Box<Draft>),
    Opt(Box<Draft>),
    Expect(Box<Draft>),
    Terminal(Terminal),
    Name(String),
}

#[derive(Default)]
struct Annotations {
    sync: Vec<String>,
    anchors: Vec<String>,
    nest: bool,
}

struct Reader {
    lexed: Vec<Lex>,
    at: usize,
}

impl Reader {
    fn new(text: &str) -> Result<Reader, String> {
        Ok(Reader {
            lexed: lex(text)?,
            at: 0,
        })
    }

    fn grammar(mut self) -> Result<Grammar, String> {
        let mut drafts = Vec::new();
        while self.at < self.lexed.len() {
            let annotations = self.annotations()?;
            let Some(Lex::Ident(name)) = self.next() else {
                return Err("a rule starts with its name".into());
            };
            if self.next() != Some(Lex::Arrow) {
                return Err(format!("expected `<-` after `{name}`"));
            }
            drafts.push((name, annotations, self.choice()?));
        }
        let ids: HashMap<String, RuleId> = drafts
            .iter()
            .enumerate()
            .map(|(i, (name, ..))| (name.clone(), i as RuleId))
            .collect();
        if ids.len() != drafts.len() {
            return Err("a rule is defined twice".into());
        }
        let rules = drafts
            .into_iter()
            .map(|(name, annotations, draft)| {
                Ok(Rule {
                    silent: name.starts_with('_'),
                    sync: annotations.sync,
                    anchors: annotations.anchors,
                    nest: annotations.nest,
                    body: resolve(draft, &ids)?,
                    name,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let root = *ids.get("goat").ok_or("no `goat` rule")?;
        Ok(Grammar { rules, root, ids })
    }

    fn annotations(&mut self) -> Result<Annotations, String> {
        let mut found = Annotations::default();
        while self.peek() == Some(&Lex::At) {
            self.at += 1;
            let Some(Lex::Ident(name)) = self.next() else {
                return Err("an annotation has a name".into());
            };
            let mut tokens = Vec::new();
            if self.peek() == Some(&Lex::Open) {
                self.at += 1;
                while let Some(Lex::Quoted(text)) = self.peek().cloned() {
                    tokens.push(text);
                    self.at += 1;
                }
                if self.next() != Some(Lex::Close) {
                    return Err(format!("`@{name}` lists quoted tokens in parentheses"));
                }
            }
            match (name.as_str(), tokens.is_empty()) {
                ("sync", false) => found.sync = tokens,
                ("anchor", false) => found.anchors = tokens,
                ("nest", true) => found.nest = true,
                _ => return Err(format!("a misused annotation `@{name}`")),
            }
        }
        Ok(found)
    }

    fn peek(&self) -> Option<&Lex> {
        self.lexed.get(self.at)
    }

    fn next(&mut self) -> Option<Lex> {
        let lexed = self.lexed.get(self.at).cloned();
        self.at += 1;
        lexed
    }

    /// Whether a new rule begins here, which ends the one being read.
    fn at_rule_start(&self) -> bool {
        matches!(self.peek(), Some(Lex::Ident(_)))
            && self.lexed.get(self.at + 1) == Some(&Lex::Arrow)
    }

    fn choice(&mut self) -> Result<Draft, String> {
        let mut alternatives = vec![self.sequence()?];
        while self.peek() == Some(&Lex::Slash) {
            self.at += 1;
            alternatives.push(self.sequence()?);
        }
        Ok(one_or(alternatives, Draft::Choice))
    }

    fn sequence(&mut self) -> Result<Draft, String> {
        let mut items = Vec::new();
        while !self.at_rule_start()
            && !matches!(self.peek(), None | Some(Lex::Slash | Lex::Close | Lex::At))
        {
            items.push(self.suffixed()?);
        }
        if items.is_empty() {
            return Err("an empty sequence".into());
        }
        Ok(one_or(items, Draft::Seq))
    }

    fn suffixed(&mut self) -> Result<Draft, String> {
        let mut atom = self.atom()?;
        loop {
            atom = match self.peek() {
                Some(Lex::Star) => Draft::Star(Box::new(atom)),
                Some(Lex::Plus) => Draft::Plus(Box::new(atom)),
                Some(Lex::Question) => Draft::Opt(Box::new(atom)),
                Some(Lex::At)
                    if self.lexed.get(self.at + 1) == Some(&Lex::Ident("expect".into())) =>
                {
                    self.at += 1;
                    Draft::Expect(Box::new(atom))
                }
                _ => return Ok(atom),
            };
            self.at += 1;
        }
    }

    fn atom(&mut self) -> Result<Draft, String> {
        match self.next() {
            Some(Lex::Open) => {
                let inner = self.choice()?;
                if self.next() != Some(Lex::Close) {
                    return Err("an unclosed `(`".into());
                }
                Ok(inner)
            }
            Some(Lex::Quoted(text)) => Ok(Draft::Terminal(Terminal::Text(text))),
            Some(Lex::Ident(name)) => Ok(match name.as_str() {
                "NAME" => Draft::Terminal(Terminal::Kind(TokenKind::Name)),
                "NUMBER" => Draft::Terminal(Terminal::Kind(TokenKind::Number)),
                "STRING" => Draft::Terminal(Terminal::Kind(TokenKind::String)),
                "EOI" => Draft::Terminal(Terminal::EndOfInput),
                _ => Draft::Name(name),
            }),
            other => Err(format!("unexpected {other:?} in a rule body")),
        }
    }
}

fn one_or(mut items: Vec<Draft>, many: fn(Vec<Draft>) -> Draft) -> Draft {
    if items.len() == 1 {
        items.remove(0)
    } else {
        many(items)
    }
}

fn resolve(draft: Draft, ids: &HashMap<String, RuleId>) -> Result<Expr, String> {
    let all = |items: Vec<Draft>| -> Result<Vec<Expr>, String> {
        items.into_iter().map(|d| resolve(d, ids)).collect()
    };
    Ok(match draft {
        Draft::Seq(items) => Expr::Seq(all(items)?),
        Draft::Choice(items) => Expr::Choice(all(items)?),
        Draft::Star(d) => Expr::Star(Box::new(resolve(*d, ids)?)),
        Draft::Plus(d) => Expr::Plus(Box::new(resolve(*d, ids)?)),
        Draft::Opt(d) => Expr::Opt(Box::new(resolve(*d, ids)?)),
        Draft::Expect(d) => Expr::Expect(Box::new(resolve(*d, ids)?)),
        Draft::Terminal(t) => Expr::Terminal(t),
        Draft::Name(name) => Expr::Rule(*ids.get(&name).ok_or(format!("no rule named `{name}`"))?),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_the_embedded_grammar() {
        let grammar = Grammar::goat();
        assert_eq!(grammar.rule(grammar.root).name, "goat");
        assert!(grammar.rule(grammar.id("_part").unwrap()).silent);
        assert!(!grammar.rule(grammar.id("expr").unwrap()).silent);
    }

    #[test]
    fn reads_sequence_choice_and_repetition() {
        let grammar = Grammar::read("goat <- a 'x' / b+\na <- 'y'?\nb <- ( NAME )*").unwrap();
        let Expr::Choice(alternatives) = &grammar.rule(grammar.root).body else {
            panic!("a choice");
        };
        assert!(matches!(&alternatives[0], Expr::Seq(items) if items.len() == 2));
        assert!(matches!(&alternatives[1], Expr::Plus(_)));
        assert!(matches!(grammar.rule(1).body, Expr::Opt(_)));
        assert!(matches!(grammar.rule(2).body, Expr::Star(_)));
    }

    #[test]
    fn reads_the_recovery_annotations() {
        let grammar = Grammar::read(
            "@sync(';' 'x')\n@anchor('done')\n@nest\ngoat <- a@expect 'y'@expect b\na <- 'z'\nb <- 'w'",
        )
        .unwrap();
        let root = grammar.rule(grammar.root);
        assert_eq!(root.sync, [";", "x"]);
        assert_eq!(root.anchors, ["done"]);
        assert!(root.nest);
        let Expr::Seq(items) = &root.body else {
            panic!("a sequence");
        };
        assert!(matches!(&items[0], Expr::Expect(inner) if matches!(**inner, Expr::Rule(1))));
        assert!(matches!(&items[1], Expr::Expect(inner) if matches!(**inner, Expr::Terminal(_))));
        assert!(matches!(&items[2], Expr::Rule(2)));
        assert!(!grammar.rule(1).nest && grammar.rule(1).sync.is_empty());
    }

    #[test]
    fn rejects_a_malformed_grammar() {
        for (text, why) in [
            ("goat <- missing", "no rule named"),
            ("goat <- 'x'\ngoat <- 'y'", "defined twice"),
            ("goat <- ( 'x'", "unclosed"),
            ("goat <- 'x", "unterminated"),
            ("other <- 'x'", "no `goat` rule"),
            ("goat <-", "empty sequence"),
            ("@sync\ngoat <- 'x'", "misused annotation"),
            ("@bogus('x')\ngoat <- 'x'", "misused annotation"),
            ("@anchor('x' goat <- 'x'", "lists quoted tokens"),
        ] {
            let error = Grammar::read(text).expect_err(text);
            assert!(error.contains(why), "{text}: {error}");
        }
    }
}
