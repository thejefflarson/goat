//! The PEG interpreter: walks the grammar as data over the lexer's tokens and
//! records a [`Cst`]. [`parse`] accepts valid input only and reports where the
//! parse got farthest otherwise. [`parse_recovering`] never fails: it follows
//! the grammar's recovery annotations to a tree with `ERROR` and `MISSING`
//! nodes and a list of spanned diagnostics, and on valid input builds the same
//! tree as [`parse`].

use crate::cst::{Cst, Event, Kind};
use crate::lexer::{self, Token, TokenKind};
use crate::peg::{Expr, Grammar, Terminal};
use std::fmt;
use std::ops::Range;

/// Expression levels, the bound lowering applies to the same program: deeper
/// nesting fails the parse, so a pathological program cannot overflow the stack.
const MAX_NESTING: usize = 256;

const TOO_DEEP: &str = "expression nested too deeply";

/// The byte offset of the farthest token the grammar could not place.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub offset: usize,
    /// The parse failed on nesting past the limit, not on a syntax error.
    pub too_deep: bool,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unexpected input at byte {}", self.offset)
    }
}

impl std::error::Error for ParseError {}

/// A syntax problem the parser recovered from. A zero-width span marks
/// something missing at that offset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub span: Range<usize>,
    pub message: String,
}

#[derive(Clone, Debug)]
pub struct Recovered {
    pub cst: Cst,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn parse(source: &str) -> Result<Cst, ParseError> {
    let grammar = Grammar::goat();
    let tokens = lexer::lex(source);
    if let Some(unknown) = tokens.iter().find(|t| t.kind == TokenKind::Unknown) {
        return Err(ParseError {
            offset: unknown.start,
            too_deep: false,
        });
    }
    let (significant, placed) = significant(&tokens);
    let mut run = Run::new(grammar, source, &placed, false);
    if !run.rule(grammar.root) {
        let too_deep = run.too_deep.is_some();
        let at = run.too_deep.unwrap_or(run.farthest);
        let offset = placed.get(at).map_or(source.len(), |t| t.start);
        return Err(ParseError { offset, too_deep });
    }
    let events = place(run.events, &significant);
    Ok(Cst::build(source, grammar, tokens, &events))
}

/// Parse any input. Every byte lands in the tree, and every problem is a
/// diagnostic.
pub fn parse_recovering(source: &str) -> Recovered {
    let grammar = Grammar::goat();
    let tokens = lexer::lex(source);
    let (significant, placed) = significant(&tokens);
    let mut run = Run::new(grammar, source, &placed, true);
    run.root();
    let events = place(run.events, &significant);
    let cst = Cst::build(source, grammar, tokens, &events);
    let mut diagnostics = run.diagnostics;
    // A MISSING diagnostic says where the tree put its node, after any trivia
    // already placed, so a span and its node never disagree.
    let mut offsets = cst.missing_offsets().into_iter();
    for diagnostic in diagnostics.iter_mut().filter(|d| d.span.is_empty()) {
        let at = offsets.next().expect("a MISSING node for each diagnostic");
        diagnostic.span = at..at;
    }
    if let Some(at) = run.too_deep {
        diagnostics.push(Diagnostic {
            span: placed[at].start..placed[at].end,
            message: TOO_DEEP.into(),
        });
    }
    diagnostics.sort_by_key(|d| d.span.start);
    Recovered { cst, diagnostics }
}

/// The indices of the tokens the grammar sees, and those tokens.
fn significant(tokens: &[Token]) -> (Vec<usize>, Vec<Token>) {
    let significant: Vec<usize> = (0..tokens.len())
        .filter(|&i| !tokens[i].is_trivia())
        .collect();
    let placed = significant.iter().map(|&i| tokens[i]).collect();
    (significant, placed)
}

/// Re-index the events from significant tokens to the full token list.
fn place(events: Vec<Event>, significant: &[usize]) -> Vec<Event> {
    events
        .into_iter()
        .map(|event| match event {
            Event::Token(i) => Event::Token(significant[i]),
            other => other,
        })
        .collect()
}

#[derive(Clone, Copy)]
struct Mark {
    position: usize,
    events: usize,
    diagnostics: usize,
}

/// What an `@expect` stands in for.
enum Expected {
    Text(&'static str),
    Named(&'static str),
}

struct Run<'a> {
    grammar: &'static Grammar,
    source: &'a str,
    tokens: &'a [Token],
    position: usize,
    events: Vec<Event>,
    farthest: usize,
    nesting: usize,
    recover: bool,
    diagnostics: Vec<Diagnostic>,
    /// The `@anchor` tokens of every rule being run, outermost first.
    anchors: Vec<&'static str>,
    /// How many of `anchors` belong to rules enclosing the innermost node
    /// rule: those are walls for its recovery, and its own are not.
    walls: usize,
    sync: &'static [String],
    /// The token at which nesting first hit the cap.
    too_deep: Option<usize>,
}

impl<'a> Run<'a> {
    fn new(grammar: &'static Grammar, source: &'a str, tokens: &'a [Token], recover: bool) -> Self {
        Run {
            grammar,
            source,
            tokens,
            position: 0,
            events: Vec::new(),
            farthest: 0,
            nesting: 0,
            recover,
            diagnostics: Vec::new(),
            anchors: Vec::new(),
            walls: 0,
            sync: &[],
            too_deep: None,
        }
    }

    /// The root rule, whose last item is the end of input. Whatever the rest
    /// leaves before the end is junk: skip it through a sync token and read on.
    /// Each pass consumes at least one token, so the loop ends.
    fn root(&mut self) {
        let grammar = self.grammar;
        let rule = grammar.rule(grammar.root);
        let Expr::Seq(items) = &rule.body else {
            panic!("the root rule is a sequence ending at the end of input");
        };
        self.events.push(Event::Open(Kind::Rule(grammar.root)));
        self.sync = &rule.sync;
        loop {
            for (i, item) in items[..items.len() - 1].iter().enumerate() {
                if i > 0 {
                    self.events.push(Event::Skip);
                }
                self.expr(item);
            }
            if self.position == self.tokens.len() {
                break;
            }
            let mut end = self.position;
            loop {
                let stops = self.is_sync(end);
                end += 1;
                if stops || end == self.tokens.len() {
                    break;
                }
            }
            self.junk(end, "unexpected input");
        }
        self.events.push(Event::Skip);
        self.events.push(Event::Close);
    }

    fn rule(&mut self, id: u16) -> bool {
        let grammar = self.grammar;
        let rule = grammar.rule(id);
        if rule.nest && self.nesting == MAX_NESTING {
            let last = self.tokens.len().saturating_sub(1);
            self.too_deep.get_or_insert(self.position.min(last));
            return false;
        }
        let mark = self.mark();
        let (walls, sync) = (self.walls, self.sync);
        let anchors = self.anchors.len();
        if !rule.silent {
            self.events.push(Event::Open(Kind::Rule(id)));
            self.walls = anchors;
            self.sync = &rule.sync;
        }
        self.anchors.extend(rule.anchors.iter().map(String::as_str));
        self.nesting += usize::from(rule.nest);
        let matched = self.expr(&rule.body);
        self.nesting -= usize::from(rule.nest);
        self.anchors.truncate(anchors);
        (self.walls, self.sync) = (walls, sync);
        if !matched {
            self.reset(mark);
            return false;
        }
        if !rule.silent {
            self.events.push(Event::Close);
        }
        true
    }

    fn expr(&mut self, expr: &'static Expr) -> bool {
        match expr {
            Expr::Rule(id) => self.rule(*id),
            Expr::Terminal(terminal) => self.terminal(terminal),
            Expr::Seq(items) => self.sequence(items),
            Expr::Choice(alternatives) => self.choice(alternatives),
            Expr::Opt(inner) => {
                self.optional(inner);
                true
            }
            Expr::Star(inner) => {
                self.repeat(inner);
                true
            }
            Expr::Plus(inner) => self.repeat(inner) > 0,
            Expr::Expect(inner) => self.expect(inner),
        }
    }

    fn sequence(&mut self, items: &'static [Expr]) -> bool {
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

    fn choice(&mut self, alternatives: &'static [Expr]) -> bool {
        let mark = self.mark();
        for alternative in alternatives {
            if self.expr(alternative) {
                return true;
            }
            self.reset(mark);
        }
        false
    }

    fn optional(&mut self, inner: &'static Expr) {
        let mark = self.mark();
        if !self.expr(inner) {
            self.reset(mark);
        }
    }

    /// Match `inner` as many times as it will, returning how many.
    fn repeat(&mut self, inner: &'static Expr) -> usize {
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
            if self.position == mark.position {
                return count;
            }
        }
    }

    /// A required piece. When it is absent and recovery is on, the tokens up to
    /// the keyword it spells, if that keyword lies ahead within reach, become an
    /// `ERROR` node and the keyword matches; otherwise a `MISSING` node stands
    /// in for it and the tokens stay for an enclosing rule. The keyword is out of reach past a token an enclosing rule
    /// anchors or this rule syncs on.
    fn expect(&mut self, inner: &'static Expr) -> bool {
        let mark = self.mark();
        if self.expr(inner) {
            return true;
        }
        self.reset(mark);
        if !self.recover {
            return false;
        }
        let expected = self.expected(inner);
        if let Expected::Text(text) = expected {
            let mut end = self.position;
            while end < self.tokens.len() && self.text(end) != text && !self.is_wall(end) {
                end += 1;
            }
            if end < self.tokens.len() && self.text(end) == text {
                self.junk(end, &format!("unexpected input, expected `{text}`"));
                if self.expr(inner) {
                    return true;
                }
            }
        }
        let (label, message) = match expected {
            Expected::Text(text) => (text, format!("expected `{text}`")),
            Expected::Named(name) => (name, format!("expected {name}")),
        };
        self.diagnostics.push(Diagnostic {
            span: 0..0,
            message,
        });
        self.events.push(Event::Missing(label));
        true
    }

    fn expected(&self, expr: &'static Expr) -> Expected {
        match expr {
            Expr::Terminal(Terminal::Text(text)) => Expected::Text(text),
            Expr::Terminal(Terminal::Kind(kind)) => Expected::Named(match kind {
                TokenKind::Number => "number",
                TokenKind::String => "string",
                _ => "name",
            }),
            Expr::Terminal(Terminal::EndOfInput) => Expected::Named("the end"),
            Expr::Rule(id) => {
                let rule = self.grammar.rule(*id);
                match &rule.body {
                    Expr::Terminal(Terminal::Text(text)) => Expected::Text(text),
                    _ => Expected::Named(rule.name.trim_start_matches('_')),
                }
            }
            Expr::Choice(items) => self.expected(items.last().expect("a choice has alternatives")),
            Expr::Seq(items) => self.expected(&items[0]),
            Expr::Star(inner) | Expr::Plus(inner) | Expr::Opt(inner) | Expr::Expect(inner) => {
                self.expected(inner)
            }
        }
    }

    /// Move the tokens before `end` into an `ERROR` node. Nothing moves when
    /// `end` is the cursor.
    fn junk(&mut self, end: usize, message: &str) {
        if end == self.position {
            return;
        }
        self.diagnostics.push(Diagnostic {
            span: self.tokens[self.position].start..self.tokens[end - 1].end,
            message: message.into(),
        });
        self.events.push(Event::Open(Kind::Error));
        self.events.extend((self.position..end).map(Event::Token));
        self.events.push(Event::Close);
        self.position = end;
    }

    fn text(&self, at: usize) -> &str {
        &self.source[self.tokens[at].start..self.tokens[at].end]
    }

    fn is_sync(&self, at: usize) -> bool {
        self.sync.iter().any(|s| s == self.text(at))
    }

    fn is_wall(&self, at: usize) -> bool {
        self.is_sync(at) || self.anchors[..self.walls].contains(&self.text(at))
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

    fn mark(&self) -> Mark {
        Mark {
            position: self.position,
            events: self.events.len(),
            diagnostics: self.diagnostics.len(),
        }
    }

    fn reset(&mut self, mark: Mark) {
        self.position = mark.position;
        self.events.truncate(mark.events);
        self.diagnostics.truncate(mark.diagnostics);
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
                ParseError {
                    offset,
                    too_deep: false
                },
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

    #[test]
    fn a_parse_that_fails_on_nesting_says_so_and_where() {
        let nested = format!("{}1{}", "(".repeat(300), ")".repeat(300));
        let error = parse(&nested).unwrap_err();
        assert!(error.too_deep);
        assert_eq!(error.offset, MAX_NESTING - 1);
        assert!(!parse("(1").unwrap_err().too_deep);
    }
}
