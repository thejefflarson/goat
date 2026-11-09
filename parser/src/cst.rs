//! The concrete syntax tree: a flat arena that keeps every token and all trivia
//! (whitespace and comments), so the source reconstructs byte for byte (ADR
//! 0022 §4). Nodes and tokens are addressed by index, so the tree is plainly
//! `Clone`, `Send` and wasm32-clean. Typed views at the bottom wrap a node and
//! return `Option` for every child, since a recovered tree may lack any of them.
//!
//! A recovered tree also holds two kinds of node no rule names: `ERROR`, which
//! keeps the tokens the grammar could not place, and `MISSING`, a zero-width
//! node where a required piece should have been.

use crate::lexer::{Token, TokenKind};
use crate::peg::{Grammar, RuleId};

/// What a node stands for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Rule(RuleId),
    Error,
    /// What was expected, as the grammar spells it.
    Missing(&'static str),
}

/// What the interpreter did, in order; [`Cst::build`] turns it into the arena.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Event {
    Open(Kind),
    /// A zero-width [`Kind::Missing`] node right after the last token placed.
    Missing(&'static str),
    /// The token at this index of the full, trivia-included token list.
    Token(usize),
    /// The trivia up to the next token belongs to the open node, as pest's
    /// implicit whitespace skipping places it between the pieces of a
    /// sequence: a node that ends in an empty option or repetition keeps the
    /// trivia after its last token.
    Skip,
    Close,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Element {
    Token(u32),
    Node(u32),
}

#[derive(Clone, Debug)]
struct NodeData {
    kind: Kind,
    start: usize,
    end: usize,
    first_child: u32,
    child_count: u32,
}

#[derive(Clone, Debug)]
pub struct Cst {
    source: String,
    grammar: &'static Grammar,
    tokens: Vec<Token>,
    nodes: Vec<NodeData>,
    children: Vec<Element>,
}

impl Cst {
    /// Build the tree for `events`. Trivia lands in whichever node is open when
    /// the next token or a [`Event::Skip`] does, and never at a node's start, so
    /// a node's span begins at its first token. The root alone covers the whole
    /// source, trivia at both ends included.
    pub(crate) fn build(
        source: &str,
        grammar: &'static Grammar,
        tokens: Vec<Token>,
        events: &[Event],
    ) -> Cst {
        let mut cst = Cst {
            source: source.to_string(),
            grammar,
            tokens,
            nodes: Vec::new(),
            children: Vec::new(),
        };
        let mut open: Vec<(Kind, Vec<Element>)> = Vec::new();
        let mut emitted = 0;
        for (at, event) in events.iter().enumerate() {
            let next_token = || {
                events[at..].iter().find_map(|e| match e {
                    Event::Token(i) => Some(*i),
                    _ => None,
                })
            };
            let upto = match event {
                Event::Token(i) => Some(*i),
                Event::Open(_) if !open.is_empty() => next_token(),
                Event::Skip => Some(next_token().unwrap_or(cst.tokens.len())),
                _ => None,
            };
            if let (Some(upto), Some((_, siblings))) = (upto, open.last_mut()) {
                while emitted < upto {
                    siblings.push(Element::Token(emitted as u32));
                    emitted += 1;
                }
            }
            match *event {
                Event::Skip => {}
                Event::Open(kind) => open.push((kind, Vec::new())),
                Event::Missing(expected) => {
                    let at = emitted.checked_sub(1).map_or(0, |i| cst.tokens[i].end);
                    let id = cst.push_node(Kind::Missing(expected), &[], at);
                    open.last_mut()
                        .expect("a node holds it")
                        .1
                        .push(Element::Node(id));
                }
                Event::Token(i) => {
                    open.last_mut()
                        .expect("a token sits inside a node")
                        .1
                        .push(Element::Token(i as u32));
                    emitted = i + 1;
                }
                Event::Close => {
                    let (kind, mut elements) = open.pop().expect("a close matches an open");
                    if open.is_empty() {
                        elements
                            .extend((emitted..cst.tokens.len()).map(|i| Element::Token(i as u32)));
                    }
                    let id = cst.push_node(kind, &elements, 0);
                    if let Some((_, siblings)) = open.last_mut() {
                        siblings.push(Element::Node(id));
                    }
                }
            }
        }
        let root = cst.nodes.last_mut().expect("the root rule closes");
        (root.start, root.end) = (0, cst.source.len());
        cst
    }

    /// `at` places a node with no elements.
    fn push_node(&mut self, kind: Kind, elements: &[Element], at: usize) -> u32 {
        let start = elements.first().map_or(at, |e| self.element_start(*e));
        let end = elements.last().map_or(at, |e| self.element_end(*e));
        let first_child = self.children.len() as u32;
        self.children.extend_from_slice(elements);
        self.nodes.push(NodeData {
            kind,
            start,
            end,
            first_child,
            child_count: elements.len() as u32,
        });
        (self.nodes.len() - 1) as u32
    }

    fn element_start(&self, element: Element) -> usize {
        match element {
            Element::Token(i) => self.tokens[i as usize].start,
            Element::Node(i) => self.nodes[i as usize].start,
        }
    }

    fn element_end(&self, element: Element) -> usize {
        match element {
            Element::Token(i) => self.tokens[i as usize].end,
            Element::Node(i) => self.nodes[i as usize].end,
        }
    }

    /// Where each `MISSING` node sits, in the order the interpreter inserted them.
    pub(crate) fn missing_offsets(&self) -> Vec<usize> {
        self.nodes
            .iter()
            .filter(|n| matches!(n.kind, Kind::Missing(_)))
            .map(|n| n.start)
            .collect()
    }

    pub fn source(&self) -> &str {
        &self.source
    }

    /// The `goat` node, which is the last one built.
    pub fn root(&self) -> Node<'_> {
        Node {
            cst: self,
            id: (self.nodes.len() - 1) as u32,
        }
    }
}

/// One node of a [`Cst`]: a cheap, copyable cursor.
#[derive(Clone, Copy)]
pub struct Node<'a> {
    cst: &'a Cst,
    id: u32,
}

/// What a node holds: another node, or a token, trivia included.
#[derive(Clone, Copy)]
pub enum Child<'a> {
    Node(Node<'a>),
    Token(Token),
}

impl<'a> Node<'a> {
    fn data(&self) -> &'a NodeData {
        &self.cst.nodes[self.id as usize]
    }

    /// The rule's name, or `ERROR` or `MISSING` in a recovered tree.
    pub fn kind(&self) -> &'a str {
        match self.data().kind {
            Kind::Rule(id) => &self.cst.grammar.rule(id).name,
            Kind::Error => "ERROR",
            Kind::Missing(_) => "MISSING",
        }
    }

    /// What a `MISSING` node stands in for: a keyword's text or a rule's name.
    pub fn expected(&self) -> Option<&'static str> {
        match self.data().kind {
            Kind::Missing(expected) => Some(expected),
            _ => None,
        }
    }

    pub fn is(&self, kind: &str) -> bool {
        self.kind() == kind
    }

    pub fn span(&self) -> std::ops::Range<usize> {
        self.data().start..self.data().end
    }

    pub fn text(&self) -> &'a str {
        &self.cst.source[self.span()]
    }

    pub fn elements(&self) -> impl Iterator<Item = Child<'a>> + use<'a> {
        let cst = self.cst;
        let data = self.data();
        let range = data.first_child as usize..(data.first_child + data.child_count) as usize;
        cst.children[range]
            .iter()
            .map(move |element| match *element {
                Element::Node(id) => Child::Node(Node { cst, id }),
                Element::Token(i) => Child::Token(cst.tokens[i as usize]),
            })
    }

    pub fn children(&self) -> impl Iterator<Item = Node<'a>> + use<'a> {
        self.elements().filter_map(|child| match child {
            Child::Node(node) => Some(node),
            Child::Token(_) => None,
        })
    }

    pub fn child(&self, kind: &str) -> Option<Node<'a>> {
        self.children().find(|node| node.is(kind))
    }

    pub fn children_of<'k>(&self, kind: &'k str) -> impl Iterator<Item = Node<'a>> + use<'a, 'k> {
        self.children().filter(move |node| node.is(kind))
    }

    /// Every token under this node in source order, trivia included.
    pub fn tokens(&self) -> Vec<Token> {
        let mut out = Vec::new();
        self.collect_tokens(&mut out);
        out
    }

    fn collect_tokens(&self, out: &mut Vec<Token>) {
        for child in self.elements() {
            match child {
                Child::Node(node) => node.collect_tokens(out),
                Child::Token(token) => out.push(token),
            }
        }
    }
}

impl Token {
    pub fn is_trivia(&self) -> bool {
        matches!(self.kind, TokenKind::Whitespace | TokenKind::Comment)
    }
}

macro_rules! views {
    ($($view:ident = $kind:literal),* $(,)?) => {$(
        #[derive(Clone, Copy)]
        pub struct $view<'a>(Node<'a>);

        impl<'a> $view<'a> {
            pub fn cast(node: Node<'a>) -> Option<Self> {
                node.is($kind).then_some(Self(node))
            }

            pub fn node(&self) -> Node<'a> {
                self.0
            }
        }
    )*};
}

views! {
    Goat = "goat",
    TagDecl = "tag_decl",
    TagCase = "tag_case",
    Block = "expr",
    Declaration = "declaration",
    Match = "match_expr",
    Arm = "arm",
    Conditional = "conditional",
    Function = "function",
    Access = "access",
    Name = "name",
}

impl<'a> Goat<'a> {
    pub fn tag_decls(&self) -> impl Iterator<Item = TagDecl<'a>> + use<'a> {
        self.0.children_of("tag_decl").map(TagDecl)
    }

    pub fn body(&self) -> Option<Block<'a>> {
        self.0.child("expr").map(Block)
    }
}

impl<'a> TagDecl<'a> {
    /// The group's name in `tag Shape = Circle | Dot`, absent in `tag Circle`.
    pub fn group(&self) -> Option<Name<'a>> {
        self.0.child("group_name")?.child("name").map(Name)
    }

    pub fn cases(&self) -> impl Iterator<Item = TagCase<'a>> + use<'a> {
        self.0.children_of("tag_case").map(TagCase)
    }
}

impl<'a> TagCase<'a> {
    pub fn name(&self) -> Option<Name<'a>> {
        self.0.child("name").map(Name)
    }
}

impl<'a> Block<'a> {
    /// The bindings of the block, in order.
    pub fn declarations(&self) -> impl Iterator<Item = Declaration<'a>> + use<'a> {
        self.0.children_of("declaration").map(Declaration)
    }
}

impl<'a> Declaration<'a> {
    pub fn name(&self) -> Option<Name<'a>> {
        self.0.child("name").map(Name)
    }

    /// The bound value: an operator run, or a `foreign` declaration.
    pub fn value(&self) -> Option<Node<'a>> {
        self.0
            .child("value")
            .or_else(|| self.0.child("foreign_decl"))
    }
}

impl<'a> Match<'a> {
    pub fn scrutinee(&self) -> Option<Block<'a>> {
        self.0.child("expr").map(Block)
    }

    pub fn arms(&self) -> impl Iterator<Item = Arm<'a>> + use<'a> {
        self.0.children_of("arm").map(Arm)
    }

    pub fn otherwise(&self) -> Option<Block<'a>> {
        self.0.children_of("expr").nth(1).map(Block)
    }
}

impl<'a> Arm<'a> {
    pub fn pattern(&self) -> Option<Node<'a>> {
        self.0
            .children()
            .find(|n| matches!(n.kind(), "pattern" | "list_pattern" | "literal_pattern"))
    }

    pub fn body(&self) -> Option<Block<'a>> {
        self.0.child("expr").map(Block)
    }
}

impl<'a> Conditional<'a> {
    pub fn condition(&self) -> Option<Block<'a>> {
        self.0.children_of("expr").next().map(Block)
    }

    pub fn then_branch(&self) -> Option<Block<'a>> {
        self.0.children_of("expr").nth(1).map(Block)
    }

    pub fn else_branch(&self) -> Option<Block<'a>> {
        self.0.children_of("expr").nth(2).map(Block)
    }
}

impl<'a> Function<'a> {
    pub fn params(&self) -> impl Iterator<Item = Node<'a>> + use<'a> {
        self.0
            .child("params")
            .into_iter()
            .flat_map(|params| params.children())
    }

    pub fn body(&self) -> Option<Block<'a>> {
        self.0.child("expr").map(Block)
    }
}

impl<'a> Access<'a> {
    pub fn field(&self) -> Option<Name<'a>> {
        self.0.child("name").map(Name)
    }
}

impl<'a> Name<'a> {
    pub fn text(&self) -> &'a str {
        self.0.text()
    }
}
