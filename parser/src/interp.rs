//! The PEG interpreter: walks the grammar as data over the lexer's tokens and
//! records a [`Cst`]. It parses valid input only; on anything else it reports
//! where the parse got farthest and builds no tree.

use crate::cst::{Cst, Event};
use crate::lexer::{self, Token, TokenKind};
use crate::peg::{Expr, Grammar, Terminal};
use std::fmt;

/// Rule nesting deeper than this fails the parse, so a pathological program
/// cannot overflow the stack.
const MAX_DEPTH: usize = 1024;

/// The byte offset of the farthest token the grammar could not place.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub offset: usize,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unexpected input at byte {}", self.offset)
    }
}

impl std::error::Error for ParseError {}

pub fn parse(source: &str) -> Result<Cst, ParseError> {
    let grammar = Grammar::goat();
    let tokens = lexer::lex(source);
    if let Some(unknown) = tokens.iter().find(|t| t.kind == TokenKind::Unknown) {
        return Err(ParseError {
            offset: unknown.start,
        });
    }
    let significant: Vec<usize> = (0..tokens.len())
        .filter(|&i| !tokens[i].is_trivia())
        .collect();
    let placed: Vec<Token> = significant.iter().map(|&i| tokens[i]).collect();

    let mut run = Run {
        grammar,
        source,
        tokens: &placed,
        position: 0,
        events: Vec::new(),
        farthest: 0,
        depth: 0,
    };
    if !run.rule(grammar.root) {
        let offset = placed.get(run.farthest).map_or(source.len(), |t| t.start);
        return Err(ParseError { offset });
    }
    let events: Vec<Event> = run
        .events
        .into_iter()
        .map(|event| match event {
            Event::Token(i) => Event::Token(significant[i]),
            other => other,
        })
        .collect();
    Ok(Cst::build(source, grammar, tokens, &events))
}

struct Run<'a> {
    grammar: &'static Grammar,
    source: &'a str,
    tokens: &'a [Token],
    position: usize,
    events: Vec<Event>,
    farthest: usize,
    depth: usize,
}

impl Run<'_> {
    fn rule(&mut self, id: u16) -> bool {
        if self.depth == MAX_DEPTH {
            return false;
        }
        let rule = self.grammar.rule(id);
        let mark = (self.position, self.events.len());
        if !rule.silent {
            self.events.push(Event::Open(id));
        }
        self.depth += 1;
        let matched = self.expr(&rule.body);
        self.depth -= 1;
        if !matched {
            (self.position, _) = mark;
            self.events.truncate(mark.1);
            return false;
        }
        if !rule.silent {
            self.events.push(Event::Close);
        }
        true
    }

    fn expr(&mut self, expr: &Expr) -> bool {
        match expr {
            Expr::Rule(id) => self.rule(*id),
            Expr::Terminal(terminal) => self.terminal(terminal),
            Expr::Seq(items) => {
                let mark = self.mark();
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        self.events.push(Event::Skip);
                    }
                    if !self.expr(item) {
                        self.reset(mark);
                        return false;
                    }
                }
                true
            }
            Expr::Choice(alternatives) => {
                let mark = self.mark();
                for alternative in alternatives {
                    if self.expr(alternative) {
                        return true;
                    }
                    self.reset(mark);
                }
                false
            }
            Expr::Opt(inner) => {
                let mark = self.mark();
                if !self.expr(inner) {
                    self.reset(mark);
                }
                true
            }
            Expr::Star(inner) => {
                self.repeat(inner);
                true
            }
            Expr::Plus(inner) => self.repeat(inner) > 0,
        }
    }

    /// Match `inner` as many times as it will, returning how many.
    fn repeat(&mut self, inner: &Expr) -> usize {
        let mut count = 0;
        loop {
            let mark = self.mark();
            if count > 0 {
                self.events.push(Event::Skip);
            }
            if !self.expr(inner) {
                self.reset(mark);
                return count;
            }
            count += 1;
            if self.position == mark.0 {
                return count;
            }
        }
    }

    fn terminal(&mut self, terminal: &Terminal) -> bool {
        let token = self.tokens.get(self.position);
        let matched = match (terminal, token) {
            (Terminal::EndOfInput, token) => token.is_none(),
            (_, None) => false,
            (Terminal::Kind(kind), Some(t)) => t.kind == *kind,
            (Terminal::Text(text), Some(t)) => &self.source[t.start..t.end] == text,
        };
        if matched && token.is_some() {
            self.events.push(Event::Token(self.position));
            self.position += 1;
        } else if !matched {
            self.farthest = self.farthest.max(self.position);
        }
        matched
    }

    fn mark(&self) -> (usize, usize) {
        (self.position, self.events.len())
    }

    fn reset(&mut self, (position, events): (usize, usize)) {
        self.position = position;
        self.events.truncate(events);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cst::{Access, Conditional, Function, Goat, Match, Node};

    fn goat(source: &str) -> Cst {
        parse(source).unwrap_or_else(|e| panic!("{source:?}: {e}"))
    }

    fn find<'a>(node: Node<'a>, kind: &str) -> Option<Node<'a>> {
        if node.is(kind) {
            return Some(node);
        }
        node.children().find_map(|child| find(child, kind))
    }

    fn all<'a>(node: Node<'a>, kinds: &[&str], found: &mut Vec<&'a str>) {
        for child in node.children() {
            if kinds.contains(&child.kind()) {
                found.push(child.kind());
            }
            all(child, kinds, found);
        }
    }

    #[test]
    fn the_tree_gives_back_the_source_byte_for_byte() {
        for source in [
            "",
            "  # only a comment\n",
            "x = 1 # one\n\n  y = x + 2 ;\r\n y  ",
            "tag A # c\ntag B = C(Number) | D\nmatch f(1) do A then 1 else 2 done # end\n",
        ] {
            let cst = goat(source);
            let text: String = cst
                .root()
                .tokens()
                .iter()
                .map(|t| &source[t.start..t.end])
                .collect();
            assert_eq!(text, source);
            assert_eq!(cst.root().span(), 0..source.len());
        }
    }

    #[test]
    fn trivia_stays_between_tokens_and_off_the_edges_of_a_node() {
        let source = "x = 1 # c\n  + 2";
        let cst = goat(source);
        let declaration = find(cst.root(), "declaration").unwrap();
        assert_eq!(declaration.text(), source);
        let value = declaration.child("value").unwrap();
        assert_eq!(value.text(), "1 # c\n  + 2");
        assert!(value.tokens().iter().any(|t| t.is_trivia()));
        assert!(!value.tokens().first().unwrap().is_trivia());
    }

    #[test]
    fn typed_views_return_what_is_there_and_none_for_what_is_not() {
        let cst = goat(
            "tag Shape = Circle(Number) | Dot\n\
             f = program(a, b) do a done\n\
             if f(1, 2) then 3 done;\n\
             match p.x do 0 then 1 else 2 done",
        );
        let goat = Goat::cast(cst.root()).unwrap();
        let tag = goat.tag_decls().next().unwrap();
        assert_eq!(tag.group().unwrap().text(), "Shape");
        let cases: Vec<_> = tag.cases().map(|c| c.name().unwrap().text()).collect();
        assert_eq!(cases, ["Circle", "Dot"]);

        let block = goat.body().unwrap();
        let binding = block.declarations().next().unwrap();
        assert_eq!(binding.name().unwrap().text(), "f");
        let function = find(binding.value().unwrap(), "function")
            .and_then(Function::cast)
            .unwrap();
        assert_eq!(function.params().count(), 2);
        assert!(function.body().is_some());

        let conditional = find(block.node(), "conditional")
            .and_then(Conditional::cast)
            .unwrap();
        assert!(conditional.condition().is_some() && conditional.then_branch().is_some());
        assert!(conditional.else_branch().is_none());

        let matched = find(block.node(), "match_expr")
            .and_then(Match::cast)
            .unwrap();
        assert_eq!(matched.arms().count(), 1);
        assert!(matched.scrutinee().is_some() && matched.otherwise().is_some());
        let access = find(matched.node(), "access")
            .and_then(Access::cast)
            .unwrap();
        assert_eq!(access.field().unwrap().text(), "x");

        assert!(Goat::cast(goat_of("").root()).unwrap().body().is_none());
    }

    fn goat_of(source: &str) -> Cst {
        goat(source)
    }

    #[test]
    fn from_to_in_and_foreign_are_names_except_where_the_grammar_says() {
        for source in [
            "from = 1 to = 2 in = 3 foreign = 4 from + to + in + foreign",
            "line.from + {to: 1}.to",
            "for from from from to to do from done",
            "sqrt = foreign \"math\" \"sqrt\" (Number) -> Number",
            "sqrt = foreign \"math\"",
        ] {
            goat(source);
        }
        let keywords = |source: &str| {
            let cst = goat(source);
            let mut found = Vec::new();
            all(
                cst.root(),
                &["foreign_kw", "from_kw", "to_kw", "in_kw"],
                &mut found,
            );
            found.into_iter().map(String::from).collect::<Vec<_>>()
        };
        assert_eq!(
            keywords("for i from 1 to 2 do i done"),
            ["from_kw", "to_kw"]
        );
        assert_eq!(keywords("for i in xs do i done"), ["in_kw"]);
        assert!(keywords("from + to + in").is_empty());
    }

    #[test]
    fn choice_is_ordered_and_backtracks() {
        for source in [
            "{a, b} = p a",
            "{a: 1, b: 2}",
            "[a, ...r] = xs r",
            "[a, b]",
            "x = 1 x",
            "x",
            "doner",
        ] {
            goat(source);
        }
    }

    #[test]
    fn invalid_input_reports_where_the_parse_got_farthest() {
        for (source, offset) in [
            ("x = ", 4),
            ("(1", 2),
            ("1 +", 3),
            ("match x do", 10),
            ("if a then b", 11),
            ("x ? y", 2),
            ("tag", 3),
            ("1 )", 2),
        ] {
            assert_eq!(
                parse(source).unwrap_err(),
                ParseError { offset },
                "{source:?}"
            );
        }
    }

    #[test]
    fn nesting_past_the_limit_fails_instead_of_overflowing_the_stack() {
        let nested = |n: usize| format!("{}1{}", "(".repeat(n), ")".repeat(n));
        let on_small_stack = |source: String| {
            std::thread::Builder::new()
                .stack_size(2 << 20)
                .spawn(move || parse(&source).is_ok())
                .unwrap()
                .join()
                .unwrap()
        };
        assert!(on_small_stack(nested(50)));
        assert!(!on_small_stack(nested(100_000)));
    }
}
