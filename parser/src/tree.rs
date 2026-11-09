//! The parse tree lowering reads, with the `Pair`/`Pairs` surface pest's tree
//! has. Either parser builds it: [`parse_pest`] from pest, [`parse_cst`] from
//! the grammar interpreter's CST. Lowering reads only this, so the dual-run
//! tests can hold the two parsers to the same tree and the same HIR. The module
//! is scaffolding: it goes when lowering reads the CST's typed views directly.

use crate::cst::Node;
use crate::parser::{GoatParser, Rule};
use crate::{Parser, interp};
use std::fmt::{self, Write as _};

#[derive(Clone, Debug, PartialEq, Eq)]
struct Entry {
    rule: Rule,
    start: usize,
    end: usize,
    children: Vec<u32>,
}

/// Every node in pre-order; the first is the `goat` node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tree {
    source: String,
    nodes: Vec<Entry>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SyntaxError(String);

impl fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for SyntaxError {}

pub fn parse_pest(source: &str) -> Result<Tree, SyntaxError> {
    let mut pairs =
        GoatParser::parse(Rule::goat, source).map_err(|e| SyntaxError(e.to_string()))?;
    let mut tree = Tree::empty(source);
    tree.add_pest(pairs.next().expect("goat always produces one pair"));
    Ok(tree)
}

pub fn parse_cst(source: &str) -> Result<Tree, SyntaxError> {
    let cst = interp::parse(source).map_err(|e| SyntaxError(e.to_string()))?;
    let mut tree = Tree::empty(source);
    tree.add_cst(cst.root());
    Ok(tree)
}

impl Tree {
    fn empty(source: &str) -> Tree {
        Tree {
            source: source.to_string(),
            nodes: Vec::new(),
        }
    }

    fn add_pest(&mut self, pair: pest::iterators::Pair<Rule>) -> u32 {
        let span = pair.as_span();
        let id = self.push(pair.as_rule(), span.start(), span.end());
        for inner in pair.into_inner().filter(|p| p.as_rule() != Rule::EOI) {
            let child = self.add_pest(inner);
            self.nodes[id as usize].children.push(child);
        }
        id
    }

    fn add_cst(&mut self, node: Node) -> u32 {
        let rule = rule_named(node.kind()).expect("every node rule has a pest counterpart");
        let span = node.span();
        let id = self.push(rule, span.start, span.end);
        for inner in node.children() {
            let child = self.add_cst(inner);
            self.nodes[id as usize].children.push(child);
        }
        id
    }

    fn push(&mut self, rule: Rule, start: usize, end: usize) -> u32 {
        self.nodes.push(Entry {
            rule,
            start,
            end,
            children: Vec::new(),
        });
        (self.nodes.len() - 1) as u32
    }

    pub fn root(&self) -> Pair<'_> {
        Pair { tree: self, id: 0 }
    }

    /// An indented outline with spans, for a readable diff of two trees.
    pub fn outline(&self) -> String {
        let mut out = String::new();
        self.outline_into(0, 0, &mut out);
        out
    }

    fn outline_into(&self, id: u32, depth: usize, out: &mut String) {
        let entry = &self.nodes[id as usize];
        let text = &self.source[entry.start..entry.end];
        let _ = writeln!(
            out,
            "{:indent$}{:?} {}..{} {:?}",
            "",
            entry.rule,
            entry.start,
            entry.end,
            text.chars().take(24).collect::<String>(),
            indent = depth * 2
        );
        for &child in &entry.children {
            self.outline_into(child, depth + 1, out);
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct PairSpan {
    start: usize,
    end: usize,
}

impl PairSpan {
    pub fn start(&self) -> usize {
        self.start
    }

    pub fn end(&self) -> usize {
        self.end
    }
}

#[derive(Clone)]
pub struct Pair<'i> {
    tree: &'i Tree,
    id: u32,
}

impl<'i> Pair<'i> {
    fn entry(&self) -> &'i Entry {
        &self.tree.nodes[self.id as usize]
    }

    pub fn as_rule(&self) -> Rule {
        self.entry().rule
    }

    pub fn as_span(&self) -> PairSpan {
        PairSpan {
            start: self.entry().start,
            end: self.entry().end,
        }
    }

    pub fn as_str(&self) -> &'i str {
        &self.tree.source[self.entry().start..self.entry().end]
    }

    pub fn into_inner(self) -> Pairs<'i> {
        Pairs {
            tree: self.tree,
            ids: self.entry().children.iter(),
        }
    }
}

#[derive(Clone)]
pub struct Pairs<'i> {
    tree: &'i Tree,
    ids: std::slice::Iter<'i, u32>,
}

impl<'i> Iterator for Pairs<'i> {
    type Item = Pair<'i>;

    fn next(&mut self) -> Option<Pair<'i>> {
        self.ids.next().map(|&id| Pair {
            tree: self.tree,
            id,
        })
    }
}

impl DoubleEndedIterator for Pairs<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.ids.next_back().map(|&id| Pair {
            tree: self.tree,
            id,
        })
    }
}

macro_rules! rules {
    ($($name:ident),* $(,)?) => {
        /// The pest rule a grammar rule of the same name stands for.
        pub fn rule_named(name: &str) -> Option<Rule> {
            match name {
                $(stringify!($name) => Some(Rule::$name),)*
                _ => None,
            }
        }
    };
}

rules! {
    goat, tag_decl, tag_kw, group_name, tag_case, expr, sequel, value, and_op, or_op, not_op,
    plus, minus, multiply, floor_divide, divide, remainder, equal, not_equal, lte, lt, gte, gt,
    negation, access, call, arguments, number, string, boolean, true_lit, false_lit, name, record,
    spread, field, local, declaration, foreign_kw, foreign_decl, foreign_name, fn_type, list_type,
    record_type, field_type, type_name, destructure, record_pattern, list_pattern, rest_binding,
    function, params, conditional, list, match_expr, arm, pattern, labels, literal_pattern,
    repeat_loop, count_loop, each_loop, for_kw, from_kw, to_kw, in_kw,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::peg::Grammar;

    #[test]
    fn every_node_rule_has_a_pest_counterpart() {
        let grammar = Grammar::goat();
        for rule in grammar.rules.iter().filter(|r| !r.silent) {
            assert!(rule_named(&rule.name).is_some(), "{}", rule.name);
        }
    }

    #[test]
    fn the_cst_tree_is_pests_tree() {
        let source = "tag Shape = Circle(Number) | Dot\n# c\nx = 1 + f(2).y;\nmatch x do 0 then 1 else 2 done";
        let cst = parse_cst(source).unwrap();
        let pest = parse_pest(source).unwrap();
        assert_eq!(cst.outline(), pest.outline());
        assert_eq!(cst, pest);
    }
}
