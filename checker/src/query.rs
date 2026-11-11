//! Editor queries over a program that may be half typed (ADR 0022 §4): which
//! names are in scope at a cursor, what type an expression has, and the
//! completions those give. The parser recovers a tree from any buffer; this
//! module *heals* a copy of that tree's source into a program the strict
//! parser accepts, runs lowering and inference on it, and reads the answers
//! back at the original offsets. Nothing here reports an error: a buffer the
//! checker cannot make sense of yields fewer answers, not a diagnostic.
//!
//! Healing sets aside what the parser could not place (`ERROR` nodes), the
//! half-typed word at the cursor (`.fo`, an arm head `Ci`), and fills each
//! `MISSING` piece with text that checks: a keyword, a bracket, or
//! `trap("")`, an expression of any type.

use crate::captures::for_each_node;
use crate::hir::{Builtin, Expr, ExprKind, FileId};
use crate::infer::{Typed, infer_partial};
use crate::lower::{RECEIVER_NAME, lower_with_vocab};
use crate::ty::{Row, Ty};
use crate::vocab::Vocab;
use goat_parser::cst::{Child, Cst, Goat, Match, Node, TagCase};
use goat_parser::interp::parse_recovering;
use goat_parser::lexer;
use goat_parser::query::Role;
use std::collections::{HashMap, HashSet};
use std::ops::Range;

/// The tags the list sugar builds, which every program may use.
const LIST_TAGS: [&str; 2] = ["Empty", "Link"];

/// The keywords that can begin an expression, besides the function-literal ones.
const OPERAND_KEYWORDS: [&str; 7] = ["if", "match", "repeat", "for", "true", "false", "not"];

fn operand_keywords() -> impl Iterator<Item = &'static str> {
    OPERAND_KEYWORDS.into_iter().chain(lexer::FUNCTION_KEYWORDS)
}

/// Where a name in scope comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Origin {
    Program,
    Prelude,
    Builtin,
}

/// A name in scope, with what is known about its value.
#[derive(Clone, Debug, PartialEq)]
pub struct Binding {
    pub name: String,
    pub origin: Origin,
    pub ty: Option<Ty>,
    /// The parameter names, when the value is a `program` or a builtin.
    pub params: Option<Vec<String>>,
}

#[derive(Clone, Debug)]
struct Known {
    ty: Option<Ty>,
    params: Option<Vec<String>>,
}

struct Program {
    root: Expr,
    typed: Typed,
}

/// A buffer made checkable: its text, and where the fills went.
#[derive(Default)]
struct Healed {
    source: String,
    /// `(offset in the buffer, bytes filled in there)`, by offset.
    fills: Vec<(usize, usize)>,
}

impl Healed {
    /// `offset` of the buffer in the healed text. A fill at `offset` sits
    /// before a span that starts there and after one that ends there.
    fn map(&self, offset: usize, ends: bool) -> usize {
        let shift: usize = self
            .fills
            .iter()
            .filter(|(at, _)| *at < offset || (*at == offset && !ends))
            .map(|(_, len)| len)
            .sum();
        offset + shift
    }
}

pub struct Analysis {
    cst: Cst,
    healed: Healed,
    program: Option<Program>,
    /// What each binder of the program is, by name and healed start offset.
    binders: HashMap<(String, usize), Known>,
    prelude: Vec<Binding>,
    tags: Vec<TagInfo>,
}

impl Analysis {
    /// Analyze `cst`, the recovered tree of a buffer, against a host's
    /// `prelude` and `vocab`. `cursor` picks the half-typed word to set aside.
    pub fn new(prelude: &str, vocab: &Vocab, cst: Cst, cursor: usize) -> Analysis {
        let mut healed = heal(&cst, cursor);
        let lowered = lower_with_vocab(prelude, vocab, &healed.source).or_else(|_| {
            healed = Healed::default();
            lower_with_vocab(prelude, vocab, "")
        });
        let program = lowered.ok().map(|lowered| {
            let (typed, _) = infer_partial(&lowered.root, lowered.interactive.as_ref(), vocab);
            Program {
                root: lowered.root,
                typed,
            }
        });
        let (binders, prelude_names) = program.as_ref().map(read_binders).unwrap_or_default();
        Analysis {
            tags: tags(prelude, vocab, &cst),
            cst,
            healed,
            program,
            binders,
            prelude: prelude_names,
        }
    }

    pub fn cst(&self) -> &Cst {
        &self.cst
    }

    /// The type of the expression `node` covers, when the checker settled one.
    pub fn type_of(&self, node: Node) -> Option<Ty> {
        self.type_of_span(node.trimmed_span())
    }

    /// [`Analysis::type_of`] for the expression at `span`.
    pub fn type_of_span(&self, span: Range<usize>) -> Option<Ty> {
        let program = self.program.as_ref()?;
        let (start, end) = (
            self.healed.map(span.start, false),
            self.healed.map(span.end, true),
        );
        let slack = |to: usize| {
            self.healed
                .source
                .get(end..to)
                .is_some_and(|s| s.trim().is_empty())
        };
        let mut found = None;
        for_each_node(&program.root, &mut |e| {
            let at = e.span;
            if found.is_none()
                && at.file == FileId::User
                && at.start == start
                && at.end >= end
                && slack(at.end)
            {
                found = Some(e.id);
            }
        });
        program.typed.node_types.get(&found?).cloned()
    }

    /// The names visible at `offset`: the program's own, innermost and latest
    /// first, then the prelude's and the builtins.
    pub fn scope_at(&self, offset: usize) -> Vec<Binding> {
        let mut own: Vec<Binding> = Vec::new();
        for (name, start) in visible_names(&self.cst, offset).into_iter().rev() {
            if own.iter().any(|b| b.name == name) {
                continue;
            }
            let known = self
                .binders
                .get(&(name.clone(), self.healed.map(start, false)));
            own.push(Binding {
                name,
                origin: Origin::Program,
                ty: known.and_then(|k| k.ty.clone()),
                params: known.and_then(|k| k.params.clone()),
            });
        }
        let shadowed = |name: &str| own.iter().any(|b| b.name == name);
        let prelude = self.prelude.iter().filter(|b| !shadowed(&b.name)).cloned();
        let builtins = Builtin::ALL
            .iter()
            .filter(|b| !shadowed(b.name()))
            .map(|b| Binding {
                name: b.name().into(),
                origin: Origin::Builtin,
                ty: None,
                params: Some(vec![
                    match b {
                        Builtin::Print => "value",
                        Builtin::Trap => "message",
                    }
                    .into(),
                ]),
            });
        let rest: Vec<Binding> = prelude.chain(builtins).collect();
        own.extend(rest);
        own
    }

    /// Every tag a program may use, the program's own first.
    pub fn tags(&self) -> &[TagInfo] {
        &self.tags
    }
}

fn known(typed: &Typed, symbol: &u32, value: &Expr) -> Known {
    let params = match &value.kind {
        ExprKind::Func { params, .. } => Some(params.iter().map(|p| p.name.clone()).collect()),
        _ => None,
    };
    Known {
        ty: typed.schemes.get(symbol).map(|s| s.ty.clone()),
        params,
    }
}

/// The program's binders with their types, keyed by name and start offset, and
/// the names the prelude defines.
fn read_binders(program: &Program) -> (HashMap<(String, usize), Known>, Vec<Binding>) {
    let typed = &program.typed;
    let mut binders = HashMap::new();
    for_each_node(&program.root, &mut |e| {
        if e.span.file != FileId::User {
            return;
        }
        match &e.kind {
            ExprKind::Let {
                symbol,
                name,
                value,
                ..
            } if name != RECEIVER_NAME => {
                binders.insert((name.clone(), e.span.start), known(typed, symbol, value));
            }
            ExprKind::Func { params, .. } => {
                let args = match typed.node_types.get(&e.id) {
                    Some(Ty::Func(args, _)) => args.as_slice(),
                    _ => &[],
                };
                for (p, ty) in params
                    .iter()
                    .zip(args.iter().map(Some).chain(std::iter::repeat(None)))
                {
                    let known = Known {
                        ty: ty.cloned(),
                        params: None,
                    };
                    binders.insert((p.name.clone(), p.span.start), known);
                }
            }
            ExprKind::Match { arms, .. } => {
                for p in arms.iter().flat_map(|arm| arm.pattern.payload.binders()) {
                    let known = Known {
                        ty: typed.binder_types.get(&p.symbol).cloned(),
                        params: None,
                    };
                    binders.insert((p.name.clone(), p.span.start), known);
                }
            }
            _ => {}
        }
    });
    let mut prelude = Vec::new();
    let mut next = Some(&program.root);
    while let Some(Expr {
        span,
        kind:
            ExprKind::Let {
                symbol,
                name,
                value,
                rest,
            },
        ..
    }) = next
    {
        if span.file != FileId::Prelude {
            break;
        }
        if name != "_" {
            let known = known(typed, symbol, value);
            prelude.push(Binding {
                name: name.clone(),
                origin: Origin::Prelude,
                ty: known.ty,
                params: known.params,
            });
        }
        next = rest.as_deref();
    }
    (binders, prelude)
}

/// A tag a program may use.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TagInfo {
    pub name: String,
    /// The payload as declared, empty for a bare tag.
    pub payload: String,
    /// The closed group the tag belongs to, when its declaration names one.
    pub group: Option<usize>,
}

/// The tags `cst` declares, numbering each group from `next_group`.
fn declared_tags(cst: &Cst, next_group: &mut usize) -> Vec<TagInfo> {
    let source = cst.source();
    let mut found = Vec::new();
    let decls = Goat::cast(cst.root())
        .into_iter()
        .flat_map(|goat| goat.tag_decls());
    for decl in decls {
        let cases: Vec<_> = decl.cases().collect();
        let payload = |case: &TagCase| {
            let types: Vec<&str> = case
                .node()
                .children()
                .skip(1)
                .map(|ty| &source[ty.trimmed_span()])
                .collect();
            types.join(", ")
        };
        let flat = decl.group().is_none()
            && matches!(cases.as_slice(), [case] if case.node().children().count() == 1);
        let group = (!flat).then(|| {
            *next_group += 1;
            *next_group - 1
        });
        found.extend(cases.iter().filter_map(|case| {
            Some(TagInfo {
                name: case.name()?.text().to_string(),
                payload: payload(case),
                group,
            })
        }));
    }
    found
}

/// Every tag a program may use: its own declarations first, in order, then the
/// list sugar's, the prelude's and the host's by name.
fn tags(prelude: &str, vocab: &Vocab, cst: &Cst) -> Vec<TagInfo> {
    let mut groups = 0;
    let mut tags = declared_tags(cst, &mut groups);
    let bare = |name: &str, payload: String| TagInfo {
        name: name.into(),
        payload,
        group: None,
    };
    let from_prelude = declared_tags(&parse_recovering(prelude).cst, &mut groups);
    let mut rest: Vec<TagInfo> = LIST_TAGS
        .into_iter()
        .map(|name| bare(name, String::new()))
        .chain(from_prelude)
        .chain(
            vocab
                .events
                .iter()
                .map(|e| bare(&e.name, e.payload.to_string())),
        )
        .chain(
            vocab
                .shapes
                .iter()
                .map(|s| bare(&s.name, s.payload.to_string())),
        )
        .chain(vocab.keys.tags.iter().map(|(name, payload)| TagInfo {
            group: Some(groups),
            ..bare(name, payload.to_string())
        }))
        .collect();
    rest.sort_by(|a, b| a.name.cmp(&b.name));
    tags.extend(rest);
    let mut seen = HashSet::new();
    tags.retain(|t| seen.insert(t.name.clone()));
    tags
}

/// The names a pattern or parameter list binds, each with the offset it starts at.
fn pattern_names(node: Node) -> Vec<(String, usize)> {
    let mut names = Vec::new();
    let mut pending = vec![node];
    while let Some(n) = pending.pop() {
        if n.is("name") {
            names.push((n.text().to_string(), n.span().start));
        } else {
            let at = pending.len();
            pending.extend(n.children());
            pending[at..].reverse();
        }
    }
    names
}

/// Whether `node` has the direct token `word` ending at or before `offset`.
fn passed(cst: &Cst, node: Node, word: &str, offset: usize) -> bool {
    node.elements().any(|e| {
        matches!(e, Child::Token(t) if t.end <= offset && &cst.source()[t.start..t.end] == word)
    })
}

/// The names bound before `offset` that are still in scope there, outermost
/// binding first, each with the offset of its name.
fn visible_names(cst: &Cst, offset: usize) -> Vec<(String, usize)> {
    let path = cst.enclosing_path(offset);
    let mut found = Vec::new();
    for (i, node) in path.iter().enumerate() {
        let unfinished = path.get(i + 1).map(Node::span);
        let before = |child: &Node| {
            child.trimmed_span().end < offset
                && !(child.is_open() && Some(child.span()) == unfinished)
        };
        match node.kind() {
            "expr" | "local" => {
                for decl in node.children_of("declaration").filter(before) {
                    if let Some(name) = decl.child("name") {
                        found.push((name.text().to_string(), name.span().start));
                    }
                }
            }
            "destructure" => {
                if node.child("value").is_some_and(|v| before(&v)) {
                    for pattern in node
                        .children()
                        .filter(|c| matches!(c.kind(), "record_pattern" | "list_pattern"))
                    {
                        found.extend(pattern_names(pattern));
                    }
                }
            }
            "function" if passed(cst, *node, "do", offset) => {
                if let Some(params) = node.child("params") {
                    found.extend(pattern_names(params));
                }
            }
            "arm" if passed(cst, *node, "then", offset) => {
                if let Some(head) = node.children().next() {
                    // The tag's own name is not a binding.
                    let tag = usize::from(head.is("pattern"));
                    found.extend(pattern_names(head).into_iter().skip(tag));
                }
            }
            "count_loop" | "each_loop" if passed(cst, *node, "do", offset) => {
                if let Some(name) = node.child("name") {
                    found.push((name.text().to_string(), name.span().start));
                }
            }
            _ => {}
        }
    }
    found
}

/// Whether `expected`, a `MISSING` node's label, is text the grammar spells
/// rather than the name of a rule.
fn is_literal(expected: &str) -> bool {
    !expected.starts_with(|c: char| c.is_alphabetic()) || lexer::keywords().contains(&expected)
}

/// Text that stands in for a missing piece and checks.
fn fill(expected: &str) -> String {
    if is_literal(expected) {
        return format!(" {expected} ");
    }
    match expected {
        "name" => " _hole ",
        "tag_case" => " Hole ",
        "number" => " 0 ",
        "string" => " \"\" ",
        "the end" => "",
        _ => " trap(\"\") ",
    }
    .into()
}

fn heal(cst: &Cst, cursor: usize) -> Healed {
    let mut blanks: Vec<Range<usize>> = Vec::new();
    let mut fills: Vec<(usize, String)> = Vec::new();
    let mut pending = vec![cst.root()];
    while let Some(node) = pending.pop() {
        let span = node.trimmed_span();
        let touches = span.start < cursor && cursor <= span.end;
        match node.kind() {
            "ERROR" => blanks.push(node.span()),
            "access" if touches || node.child("MISSING").is_some() => blanks.push(span),
            "arm"
                if node.children().next().is_some_and(|head| {
                    let head = head.span();
                    head.start <= cursor && cursor <= head.end
                }) =>
            {
                blanks.push(span)
            }
            // An `else` keeps the scrutinee's type open to the arms about to be
            // written, instead of narrowing it to the ones so far.
            "match_expr"
                if (node.is_open() || touches)
                    && Match::cast(node).is_some_and(|m| m.otherwise().is_none()) =>
            {
                let source = cst.source();
                let done = node
                    .elements()
                    .filter_map(|e| match e {
                        Child::Token(t) if &source[t.start..t.end] == "done" => Some(t),
                        _ => None,
                    })
                    .last();
                fills.extend(done.map(|t| (t.start, " else trap(\"\") ".to_string())));
                for child in node.children() {
                    if child.expected() == Some("done") {
                        fills.push((child.span().start, " else trap(\"\") done ".into()));
                    } else {
                        pending.push(child);
                    }
                }
            }
            "MISSING" => fills.push((node.span().start, fill(node.expected().unwrap_or("")))),
            _ => {
                let at = pending.len();
                pending.extend(node.children());
                pending[at..].reverse();
            }
        }
    }
    let mut source = cst.source().to_string();
    for range in blanks {
        let blank = " ".repeat(range.len());
        source.replace_range(range, &blank);
    }
    fills.sort_by_key(|(at, _)| *at);
    for (at, text) in fills.iter().rev() {
        source.insert_str(*at, text);
    }
    Healed {
        source,
        fills: fills.iter().map(|(at, text)| (*at, text.len())).collect(),
    }
}

/// The labels of a row with their types, in order.
pub fn row_fields(row: &Row) -> Vec<(&str, &Ty)> {
    let mut out = Vec::new();
    let mut next = row;
    while let Row::Extend { label, field, rest } = next {
        out.push((label.as_str(), field.as_ref()));
        next = rest;
    }
    out
}

/// Whether a row can hold labels beyond the ones it lists.
fn row_is_open(row: &Row) -> bool {
    match row {
        Row::Empty => false,
        Row::Var(_) => true,
        Row::Extend { rest, .. } => row_is_open(rest),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ItemKind {
    Variable,
    Function,
    Keyword,
    Tag,
    Field,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Item {
    pub label: String,
    pub kind: ItemKind,
    /// What follows the label in a list: a signature or a type.
    pub detail: String,
}

/// What can be typed at a cursor, best first, from the offset where the word
/// being typed starts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Completions {
    pub from: usize,
    pub items: Vec<Item>,
}

fn item(label: &str, kind: ItemKind, detail: impl Into<String>) -> Item {
    Item {
        label: label.into(),
        kind,
        detail: detail.into(),
    }
}

fn binding_item(b: &Binding) -> Item {
    let is_function = b.params.is_some() || matches!(b.ty, Some(Ty::Func(..)));
    let kind = if is_function {
        ItemKind::Function
    } else {
        ItemKind::Variable
    };
    let detail = match (&b.params, &b.ty) {
        (Some(params), _) => format!("({})", params.join(", ")),
        (None, Some(Ty::Var(_)) | None) => String::new(),
        (None, Some(ty)) => ty.to_string(),
    };
    item(&b.name, kind, detail)
}

/// A tag's payload as the detail of a completion: nothing for a bare tag.
fn payload_detail(payload: &Ty) -> String {
    if *payload == Ty::Unit {
        String::new()
    } else {
        payload.to_string()
    }
}

/// Complete `source` at the byte `offset`, with a host's `prelude` and
/// `vocab`. `None` where nothing completes: a comment, a string, a number, a
/// name being introduced.
pub fn complete(prelude: &str, vocab: &Vocab, source: &str, offset: usize) -> Option<Completions> {
    let mut offset = offset.min(source.len());
    while !source.is_char_boundary(offset) {
        offset -= 1;
    }
    let cst = parse_recovering(source).cst;
    let context = cst.token_context(offset);
    if context.role == Role::Nothing && context.expected.is_empty() {
        return None;
    }
    let analysis = Analysis::new(prelude, vocab, cst, offset);
    let prefix = &source[context.prefix.clone()];
    let lowered = prefix.to_lowercase();

    let mut items: Vec<Item> = Vec::new();
    match &context.role {
        Role::Field { base } => {
            let ty = analysis.type_of_span(base.clone())?.unfold_head();
            let Ty::Record(row) = ty else { return None };
            items.extend(
                row_fields(&row)
                    .into_iter()
                    .map(|(label, ty)| item(label, ItemKind::Field, ty.to_string())),
            );
        }
        Role::ArmPattern { scrutinee, covered } => {
            let variant = scrutinee
                .clone()
                .and_then(|span| analysis.type_of_span(span))
                .map(|ty| ty.unfold_head());
            let (known, open) = match &variant {
                Some(Ty::Variant(row)) => (row_fields(row), row_is_open(row)),
                _ => (Vec::new(), true),
            };
            let declared = |tag: &TagInfo| {
                let payload = known
                    .iter()
                    .find(|(name, _)| *name == tag.name)
                    .map_or(tag.payload.clone(), |(_, ty)| payload_detail(ty));
                item(&tag.name, ItemKind::Tag, payload)
            };
            let group = known
                .iter()
                .find_map(|(name, _)| analysis.tags().iter().find(|t| t.name == *name)?.group);
            match group {
                Some(group) => items.extend(
                    analysis
                        .tags()
                        .iter()
                        .filter(|t| t.group == Some(group))
                        .map(declared),
                ),
                None => {
                    items.extend(
                        known
                            .iter()
                            .map(|(tag, ty)| item(tag, ItemKind::Tag, payload_detail(ty))),
                    );
                    if open {
                        items.extend(analysis.tags().iter().map(declared));
                    }
                }
            }
            items.retain(|i| !covered.contains(&i.label));
            items.extend(["else", "done"].map(|k| item(k, ItemKind::Keyword, "")));
        }
        Role::Operand => {
            items.extend(
                analysis
                    .scope_at(context.prefix.start)
                    .iter()
                    .map(binding_item),
            );
            items.extend(
                analysis
                    .tags()
                    .iter()
                    .map(|t| item(&t.name, ItemKind::Tag, t.payload.clone())),
            );
            let foreign = (context
                .previous
                .is_some_and(|t| &source[t.start..t.end] == "="))
            .then_some("foreign");
            items.extend(
                operand_keywords()
                    .chain(foreign)
                    .map(|k| item(k, ItemKind::Keyword, "")),
            );
        }
        Role::Nothing => {}
    }
    items.extend(
        context
            .expected
            .iter()
            .map(|k| item(k, ItemKind::Keyword, "")),
    );

    let mut seen = HashSet::new();
    items.retain(|i| {
        i.label != prefix
            && i.label.to_lowercase().starts_with(&lowered)
            && seen.insert(i.label.clone())
    });
    Some(Completions {
        from: context.prefix.start,
        items,
    })
}
