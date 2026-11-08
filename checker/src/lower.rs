//! Lowering: the pest parse tree → the owned, name-resolved [`hir`].
//!
//! This pass does name resolution directly (assigning a fresh [`Symbol`] to
//! each binding and resolving each use to its binder), replacing the old
//! `Renamer`. It also parses literals to values and flattens the parse tree's
//! operator list into a precedence-correct expression tree.

use crate::error::GoatError;
use crate::hir::{
    BinOp, Boundary, Builtin, ContractBinding, Expr, ExprId, ExprKind, FileId, Interactive,
    MatchArm, Param, Pattern, PatternPayload, Span, Symbol,
};
use crate::ty::{Group, Row, Ty};
use crate::vocab;
use goat_parser::parser::{GoatParser, Rule};
use pest::Parser;
use pest::iterators::{Pair, Pairs};
use std::collections::{HashMap, HashSet};
use std::iter::Peekable;
use std::sync::Arc;

/// Deepest expression tree lowering accepts; deeper input would overflow the
/// recursive passes (inference, codegen) that walk the tree.
// Kept well below the depth at which recursive inference/codegen overflows a
// small (2 MB) thread stack, so any expression the checker accepts is safe to
// walk. No real program nests this deep; pathological input gets a clean error.
const MAX_DEPTH: usize = 256;

/// Most arm bodies a program's list patterns may expand to. A pattern like
/// `[a, ...rest]` after `[a, b, c, d]` re-lowers its body at each place the
/// decision tree reaches it, so nested patterns multiply.
const MAX_LIST_LEAVES: usize = 4096;

/// The tags the list sugar `[]`/`[x, ...xs]` builds, declared even when no
/// prelude is.
const LIST_TAGS: [&str; 2] = ["Empty", "Link"];

/// The name generated bindings for the pieces of a list carry.
const LIST_NAME: &str = "list";

/// The name a `;`-sequenced value is bound to, which no source can mention.
const DISCARD_NAME: &str = "_";

/// The names a loop's generated bindings carry.
const LOOP_NAME: &str = "loop";
const LOOP_COUNTER_NAME: &str = "count";
const LOOP_START_NAME: &str = "start";
const LOOP_STOP_NAME: &str = "stop";

pub struct Lowered {
    pub root: Expr,
    pub errors: Vec<GoatError>,
    pub warnings: Vec<GoatError>,
    pub interactive: Option<Interactive>,
}

/// Parse and lower `source` on its own, with no prelude.
pub fn lower(source: &str) -> Result<Lowered, GoatError> {
    lower_with_prelude("", source)
}

/// Parse and lower `prelude` and `source` separately, then make `source` the
/// `rest` of the prelude's chain of `Let`s, so every prelude name is in scope
/// for it. Spans keep the file they came from. Parse errors abort (returned
/// as the sole error); name-resolution errors are collected so the inferer
/// can still run and report type errors in the same pass.
pub fn lower_with_prelude(prelude: &str, source: &str) -> Result<Lowered, GoatError> {
    let mut ctx = Lower::default();
    ctx.tags.extend(
        LIST_TAGS
            .into_iter()
            .chain(vocab::tag_names())
            .map(|tag| (tag.to_string(), None)),
    );
    let key = Arc::new(vocab::key_group());
    ctx.tags.extend(
        key.tags
            .iter()
            .map(|(tag, _)| (tag.clone(), Some(key.clone()))),
    );
    let mut prelude_root = ctx.lower_source(prelude, FileId::Prelude)?;

    ctx.prelude_scope = defined_names(&prelude_root);
    let user_root = ctx.lower_source(source, FileId::User)?;

    let root = if matches!(prelude_root.kind, ExprKind::Unit) {
        user_root
    } else {
        if let Err(e) = graft(&mut prelude_root, user_root) {
            ctx.errors.push(e);
        }
        prelude_root
    };
    let mut root = root;
    let interactive = ctx.make_interactive(&mut root);
    Ok(Lowered {
        root,
        errors: ctx.errors,
        warnings: ctx.warnings,
        interactive,
    })
}

const INTERACTIVE_NAMES: [&str; 3] = ["init", "update", "draw"];

/// The value span and symbol of each of `INTERACTIVE_NAMES` the root chain
/// binds exactly once; `None` when one is missing or rebound (a rebinding
/// shadows the first, ADR 0003, and the program runs once).
fn contract_bindings(root: &Expr) -> Option<[(Symbol, Span); 3]> {
    let mut found: [Vec<(Symbol, Span)>; 3] = Default::default();
    let mut next = Some(root);
    while let Some(Expr {
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
        if let Some(i) = INTERACTIVE_NAMES.iter().position(|n| n == name) {
            found[i].push((*symbol, value.span));
        }
        next = rest.as_deref();
    }
    let [init, update, draw] = found.map(|f| <[_; 1]>::try_from(f).ok().map(|[b]| b));
    Some([init?, update?, draw?])
}

/// The names bound by the chain of `Let`s that starts at `root`.
fn defined_names(root: &Expr) -> HashMap<String, Symbol> {
    let mut names = HashMap::new();
    let mut next = Some(root);
    while let Some(Expr {
        kind: ExprKind::Let {
            symbol, name, rest, ..
        },
        ..
    }) = next
    {
        names.insert(name.clone(), *symbol);
        next = rest.as_deref();
    }
    names
}

/// Make `user` the `rest` of the last `Let` in the chain at `prelude`.
fn graft(prelude: &mut Expr, user: Expr) -> Result<(), GoatError> {
    match &mut prelude.kind {
        ExprKind::Let {
            rest: Some(rest), ..
        } => graft(rest, user),
        ExprKind::Let { rest, .. } => {
            *rest = Some(Box::new(user));
            Ok(())
        }
        _ => Err(GoatError::new(
            prelude.span,
            "the prelude may only contain definitions",
        )),
    }
}

/// The names a `{x, y, ...rest}` pattern binds: `(symbol, name, span)` each.
struct RecordPattern {
    fields: Vec<(Symbol, String, Span)>,
    rest: Option<(Symbol, String, Span)>,
}

/// A `[a, b, ...rest]` pattern: the names for its leading items, and for what
/// follows them.
struct ListPattern {
    span: Span,
    items: Vec<(String, Span)>,
    rest: Option<(String, Span)>,
}

/// What runs once a list pattern has matched.
#[derive(Clone)]
enum Then<'i> {
    /// A `match` arm's body.
    Arm(Pair<'i, Rule>),
    /// The rest of a `[..] = value` chain, if there is any.
    Rest(Option<Pair<'i, Rule>>),
    /// The list-pattern parameters still to unpack, then the function body.
    Params(Vec<(Symbol, Pair<'i, Rule>)>, Option<Pair<'i, Rule>>),
}

/// The arms of one list `match`, which compile together into a decision tree
/// over `Empty` and `Link`.
struct ListMatch<'i> {
    /// Each arm's pattern, what follows it, and whether a leaf lowered it yet.
    rows: Vec<(ListPattern, Then<'i>, bool)>,
    otherwise: Option<Pair<'i, Rule>>,
    otherwise_lowered: bool,
}

impl ListMatch<'_> {
    fn is_done(&self, at: &Progress) -> bool {
        at.bound.len() == self.rows[at.row].0.items.len()
    }

    fn is_catch_all(&self, at: &Progress) -> bool {
        self.is_done(at) && self.rows[at.row].0.rest.is_some()
    }
}

/// How far one arm has matched on the way down the decision tree.
#[derive(Clone)]
struct Progress {
    row: usize,
    /// The list node each leading item was read from, in order.
    bound: Vec<Symbol>,
    /// The list that follows the leading items matched so far, which `...rest`
    /// names.
    rest_from: Symbol,
}

#[derive(Default)]
struct Lower {
    next_symbol: Symbol,
    next_expr_id: ExprId,
    scopes: Vec<HashMap<String, Symbol>>,
    /// Function bindings seen by a group pre-pass, keyed by the start of the
    /// binding's name: `Some` is its reserved symbol, `None` a repeat of an
    /// earlier name in the group, which shadows it.
    grouped: HashMap<usize, Option<Symbol>>,
    errors: Vec<GoatError>,
    warnings: Vec<GoatError>,
    depth: usize,
    file: FileId,
    /// The names the prelude defines, in scope for the user's source.
    prelude_scope: HashMap<String, Symbol>,
    list_leaves: usize,
    /// Every declared tag, built-in and written: one flat namespace for the
    /// whole program, each tag with the closed group it belongs to, if any.
    tags: HashMap<String, Option<Arc<Group>>>,
}

impl Lower {
    /// Parse and lower one source text, stamping its spans with `file`. The
    /// prelude's names are in scope when `file` is the user's.
    fn lower_source(&mut self, source: &str, file: FileId) -> Result<Expr, GoatError> {
        self.file = file;
        let mut pairs = GoatParser::parse(Rule::goat, source)
            .map_err(|e| GoatError::new(Span::in_file(0, 0, file), format!("parse error:\n{e}")))?;
        let goat = pairs.next().expect("goat rule always produces one pair");
        debug_assert!(self.grouped.is_empty());
        for decl in goat
            .clone()
            .into_inner()
            .filter(|p| p.as_rule() == Rule::tag_decl)
        {
            self.declare_tags(decl);
        }
        self.scopes.push(self.prelude_scope.clone());
        let root = self.lower_goat(goat);
        self.scopes.pop();
        Ok(root)
    }

    /// `tag Foo` opens one tag. Anything with a group name, a payload or a `|`
    /// closes its tags into a group, and each tag belongs to one group only.
    fn declare_tags(&mut self, decl: Pair<Rule>) {
        let mut group_name = None;
        let mut cases = Vec::new();
        for part in decl.into_inner() {
            match part.as_rule() {
                Rule::group_name => group_name = Some(part.as_str().to_string()),
                Rule::tag_case => cases.push(part),
                _ => {}
            }
        }
        let is_flat = group_name.is_none()
            && matches!(cases.as_slice(), [case] if case.clone().into_inner().count() == 1);
        let mut recursive = false;
        let mut tags = Vec::new();
        let mut declared: Vec<String> = Vec::new();
        for case in cases {
            let mut parts = case.into_inner();
            let name = parts.next().expect("a tag case names its tag");
            let span = self.span_of(&name);
            let payload: Vec<Ty> = parts
                .map(|ty| self.payload_ty(&ty, group_name.as_deref(), &mut recursive))
                .collect();
            let payload = match payload.len() {
                0 => Ty::Unit,
                1 => payload.into_iter().next().expect("one payload"),
                _ => Ty::Record(Row::of(
                    payload
                        .into_iter()
                        .enumerate()
                        .map(|(i, field)| (i.to_string(), field)),
                )),
            };
            let name = name.as_str().to_string();
            let taken = declared.contains(&name)
                || self
                    .tags
                    .get(&name)
                    .is_some_and(|group| group.is_some() || !is_flat);
            if taken {
                self.errors.push(GoatError::new(
                    span,
                    format!("duplicate tag `{name}`; a tag belongs to exactly one declaration"),
                ));
            }
            declared.push(name.clone());
            tags.push((name, payload));
        }
        let group = (!is_flat).then(|| Arc::new(Group { tags, recursive }));
        for name in declared {
            self.tags.entry(name).or_insert_with(|| group.clone());
        }
    }

    /// A tag payload's type: `group` stands for the group being declared.
    fn payload_ty(&mut self, ty: &Pair<Rule>, group: Option<&str>, recursive: &mut bool) -> Ty {
        let (shape, hint) = match ty.as_rule() {
            Rule::type_name if group == Some(ty.as_str()) => {
                *recursive = true;
                return Ty::Var(Group::SELF);
            }
            Rule::type_name => match Boundary::named(ty.as_str()) {
                Some(boundary) => return boundary.into(),
                None => (
                    format!("`{}`", ty.as_str()),
                    "; a payload is Number, Int, Bool, Unit, String, a record of those, or the group itself",
                ),
            },
            Rule::record_type => {
                let fields: Vec<(String, Ty)> = ty
                    .clone()
                    .into_inner()
                    .map(|field| {
                        let mut parts = field.into_inner();
                        let label = parts.next().expect("a field type has a label");
                        let ty = parts.next().expect("a field type has a type");
                        let ty = self.payload_ty(&ty, group, recursive);
                        (label.as_str().to_string(), ty)
                    })
                    .collect();
                return Ty::Record(Row::of(fields));
            }
            Rule::list_type => ("a list".to_string(), ""),
            Rule::fn_type => ("a function".to_string(), ""),
            other => unreachable!("unexpected type rule {other:?}"),
        };
        self.errors.push(GoatError::new(
            self.span_of(ty),
            format!("a tag payload can't be {shape} yet{hint}"),
        ));
        Ty::Unit
    }

    fn span_of(&self, pair: &Pair<Rule>) -> Span {
        let s = pair.as_span();
        Span::in_file(s.start(), s.end(), self.file)
    }

    fn fresh_symbol(&mut self) -> Symbol {
        let s = self.next_symbol;
        self.next_symbol += 1;
        s
    }

    fn fresh_id(&mut self) -> ExprId {
        let id = self.next_expr_id;
        self.next_expr_id += 1;
        id
    }

    /// End the root chain of an interactive program with the record its three
    /// bindings make, keeping any trailing expression as a discarded value.
    fn make_interactive(&mut self, root: &mut Expr) -> Option<Interactive> {
        let [init, update, draw] = contract_bindings(root)?;
        let end = Span::in_file(root.span.end, root.span.end, FileId::User);
        let mut uses = Vec::new();
        let mut fields = Vec::new();
        for (name, (symbol, span)) in INTERACTIVE_NAMES.iter().zip([init, update, draw]) {
            let var = self.node(
                end,
                ExprKind::Var {
                    symbol,
                    name: name.to_string(),
                },
            );
            uses.push(ContractBinding {
                span,
                use_id: var.id,
            });
            fields.push((name.to_string(), var));
        }
        let tail = self.node(end, ExprKind::Record { fields });
        self.append_to_chain(root, tail, end);
        Some(Interactive {
            init: uses[0],
            update: uses[1],
            draw: uses[2],
        })
    }

    /// Make `tail` the last thing in the chain of `Let`s at `chain`; an
    /// expression already there runs first, its value discarded.
    fn append_to_chain(&mut self, chain: &mut Expr, tail: Expr, span: Span) {
        let mut link = chain;
        while matches!(
            &link.kind,
            ExprKind::Let { rest: Some(next), .. } if matches!(next.kind, ExprKind::Let { .. })
        ) {
            let ExprKind::Let {
                rest: Some(next), ..
            } = &mut link.kind
            else {
                unreachable!("the loop condition matched a link with a successor");
            };
            link = next;
        }
        let ExprKind::Let { rest, .. } = &mut link.kind else {
            unreachable!("the chain holds the bindings found above");
        };
        *rest = Some(Box::new(match rest.take() {
            Some(old) => self.discard(span, *old, tail),
            None => tail,
        }));
    }

    fn node(&mut self, span: Span, kind: ExprKind) -> Expr {
        Expr {
            id: self.fresh_id(),
            span,
            kind,
        }
    }

    fn bind(&mut self, name: &str) -> Symbol {
        let symbol = self.fresh_symbol();
        self.bind_as(name, symbol);
        symbol
    }

    fn bind_as(&mut self, name: &str, symbol: Symbol) {
        self.scopes
            .last_mut()
            .expect("a scope is always open while binding")
            .insert(name.to_string(), symbol);
    }

    /// Resolve a use to the nearest enclosing binding, innermost scope first.
    fn resolve(&self, name: &str) -> Option<Symbol> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
    }

    fn lower_goat(&mut self, pair: Pair<Rule>) -> Expr {
        let span = self.span_of(&pair);
        self.scopes.push(HashMap::new());
        let body = pair
            .into_inner()
            .find(|p| p.as_rule() == Rule::expr)
            .map(|p| self.lower_expr(p));
        self.scopes.pop();
        body.unwrap_or_else(|| self.node(span, ExprKind::Unit))
    }

    /// Lower an `expr` pair — a flat list of operands and operators — into a
    /// precedence-correct tree. Each operand is a primary followed by zero or
    /// more postfix accesses and calls; the grammar leaves those `access` pairs as
    /// siblings, so [`Self::lower_operand`] consumes them before the next
    /// operator.
    fn lower_expr(&mut self, pair: Pair<Rule>) -> Expr {
        let scopes = self.scopes.len();
        let mut spine = Vec::new();
        let mut next = Some(pair);
        let mut tail = None;
        // The statements and bindings of a block hang off a spine of `Let`s,
        // beside the trees they build rather than under them, so the spine is
        // walked in this loop and only a statement's own nesting costs depth.
        'blocks: while let Some(pair) = next.take() {
            let end = self.span_of(&pair);
            let mut inner = pair.into_inner().peekable();
            loop {
                let added = chain_depth(&inner);
                if self.depth + added > MAX_DEPTH {
                    let span = inner.peek().map_or(end, |first| self.span_of(first));
                    self.errors
                        .push(GoatError::new(span, "expression nested too deeply"));
                    tail = Some(self.node(span, ExprKind::Unit));
                    break 'blocks;
                }
                self.depth += added;
                if let Some(declaration) = sole_declaration(&inner) {
                    let (binding, rest) = self.lower_declaration_head(declaration);
                    spine.push(binding);
                    next = rest;
                    self.depth -= added;
                    break;
                }
                let (expr, sequenced) = self.lower_expr_chain(&mut inner);
                self.depth -= added;
                if !sequenced {
                    tail = Some(expr);
                    break;
                }
                let span = expr.span.to(end);
                spine.push(Binding {
                    span,
                    symbol: None,
                    name: DISCARD_NAME.into(),
                    value: expr,
                });
                if inner.peek().is_none() {
                    tail = Some(self.node(span, ExprKind::Unit));
                    break;
                }
            }
        }
        self.scopes.truncate(scopes);
        while let Some(binding) = spine.pop() {
            tail = Some(self.bound(binding, tail));
        }
        tail.expect("a chain of statements ends in an expression")
    }

    fn bound(&mut self, binding: Binding, rest: Option<Expr>) -> Expr {
        let symbol = binding.symbol.unwrap_or_else(|| self.fresh_symbol());
        self.node(
            binding.span,
            ExprKind::Let {
                symbol,
                name: binding.name,
                value: Box::new(binding.value),
                rest: rest.map(Box::new),
            },
        )
    }

    /// Lower the statement at the front of `inner`, through the `;` that ends
    /// it. The flag is whether there was one.
    fn lower_expr_chain(&mut self, inner: &mut Peekable<Pairs<Rule>>) -> (Expr, bool) {
        let mut operands = Vec::new();
        let mut ops: Vec<(Op, Span)> = Vec::new();
        self.push_operand(inner, &mut operands, &mut ops);
        let mut sequenced = false;

        while let Some(op_pair) = inner.next() {
            if op_pair.as_rule() == Rule::sequel {
                sequenced = true;
                break;
            }
            let op = infix_op(op_pair.as_rule());
            let op_span = self.span_of(&op_pair);
            while let Some((top, _)) = ops.last() {
                if prec(*top) >= prec(op) {
                    self.reduce(&mut operands, &mut ops);
                } else {
                    break;
                }
            }
            ops.push((op, op_span));
            self.push_operand(inner, &mut operands, &mut ops);
        }

        while !ops.is_empty() {
            self.reduce(&mut operands, &mut ops);
        }
        let expr = operands.pop().expect("exactly one operand remains");
        (expr, sequenced)
    }

    /// Any `not`s are pushed as prefix operators, then the operand they apply to.
    fn push_operand(
        &mut self,
        inner: &mut Peekable<Pairs<Rule>>,
        operands: &mut Vec<Expr>,
        ops: &mut Vec<(Op, Span)>,
    ) {
        while let Some(not) = inner.next_if(|p| p.as_rule() == Rule::not_op) {
            ops.push((Op::Not, self.span_of(&not)));
        }
        operands.push(self.lower_operand(inner));
    }

    fn discard(&mut self, span: Span, value: Expr, rest: Expr) -> Expr {
        let symbol = self.fresh_symbol();
        self.node(
            span,
            ExprKind::Let {
                symbol,
                name: DISCARD_NAME.into(),
                value: Box::new(value),
                rest: Some(Box::new(rest)),
            },
        )
    }

    fn lower_operand(&mut self, inner: &mut Peekable<Pairs<Rule>>) -> Expr {
        let first = inner.next().expect("an operand begins with a primary");
        if first.as_rule() == Rule::negation {
            return self.lower_negation(first);
        }
        let expr = if first.as_rule() == Rule::name && self.is_tag(first.as_str()) {
            self.lower_tag(first, inner)
        } else {
            self.lower_primary(first)
        };
        self.lower_postfixes(expr, inner)
    }

    /// `a.b(x).c` nests as `((a.b)(x)).c`.
    fn lower_postfixes(&mut self, mut expr: Expr, inner: &mut Peekable<Pairs<Rule>>) -> Expr {
        while let Some(postfix) =
            inner.next_if(|p| matches!(p.as_rule(), Rule::access | Rule::call))
        {
            let span = expr.span.to(self.span_of(&postfix));
            expr = match postfix.as_rule() {
                Rule::access => {
                    let label = postfix
                        .into_inner()
                        .next()
                        .expect("access is `.` then an identifier")
                        .as_str()
                        .to_string();
                    self.node(
                        span,
                        ExprKind::Field {
                            record: Box::new(expr),
                            label,
                        },
                    )
                }
                _ => {
                    let args: Vec<Expr> = postfix
                        .into_inner()
                        .flat_map(|a| a.into_inner())
                        .map(|a| self.lower_expr(a))
                        .collect();
                    if matches!(expr.kind, ExprKind::Builtin(Builtin::Trap)) {
                        self.lower_trap(span, args)
                    } else {
                        self.node(
                            span,
                            ExprKind::App {
                                callee: Box::new(expr),
                                args,
                            },
                        )
                    }
                }
            };
        }
        expr
    }

    fn lower_trap(&mut self, span: Span, args: Vec<Expr>) -> Expr {
        match <[Expr; 1]>::try_from(args).map(|[arg]| arg.kind) {
            Ok(ExprKind::Str(message)) => self.node(span, ExprKind::Trap(message)),
            _ => {
                self.errors.push(GoatError::new(
                    span,
                    "`trap` takes one message, written out in quotes",
                ));
                self.node(span, ExprKind::Unit)
            }
        }
    }

    /// A literal with a `.` or an exponent is a `Float`; bare digits are an
    /// `Int`, which must fit in an `i64`.
    fn lower_number(&mut self, span: Span, text: &str) -> Expr {
        let is_float = text.contains(['.', 'e', 'E']);
        let kind = if is_float {
            text.trim_end_matches('.').parse().map(ExprKind::Float).ok()
        } else {
            text.parse().map(ExprKind::Int).ok()
        };
        let kind = kind.unwrap_or_else(|| {
            let message = if is_float {
                format!("invalid number `{text}`")
            } else {
                format!(
                    "`{text}` is too big a whole number (the most is {})",
                    i64::MAX
                )
            };
            self.errors.push(GoatError::new(span, message));
            ExprKind::Int(0)
        });
        self.node(span, kind)
    }

    /// `-x` is `0 - x`: the HIR has no negation node.
    fn lower_negation(&mut self, pair: Pair<Rule>) -> Expr {
        let span = self.span_of(&pair);
        let mut inner = pair.into_inner().peekable();
        let minus = inner.next().expect("negation begins with `-`");
        let operand = self.lower_operand(&mut inner);
        let zero = self.node(self.span_of(&minus), ExprKind::Int(0));
        self.node(
            span,
            ExprKind::Bin {
                op: BinOp::Sub,
                lhs: Box::new(zero),
                rhs: Box::new(operand),
            },
        )
    }

    /// Fold the top operator and its operands into one node.
    fn reduce(&mut self, operands: &mut Vec<Expr>, ops: &mut Vec<(Op, Span)>) {
        let (op, op_span) = ops.pop().expect("reduce called with an operator");
        let rhs = operands.pop().expect("operator has an operand");
        let node = if op == Op::Not {
            self.not(op_span.to(rhs.span), rhs)
        } else {
            let lhs = operands.pop().expect("binary operator has a left operand");
            self.binary(op, lhs, rhs)
        };
        operands.push(node);
    }

    #[inline(never)]
    fn binary(&mut self, op: Op, lhs: Expr, rhs: Expr) -> Expr {
        let span = lhs.span.to(rhs.span);
        match op {
            Op::Bin(op) => self.node(
                span,
                ExprKind::Bin {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
            ),
            Op::And => self.node(
                span,
                ExprKind::And {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
            ),
            Op::Or => self.node(
                span,
                ExprKind::Or {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
            ),
            Op::Not => unreachable!("`not` takes one operand"),
        }
    }

    fn not(&mut self, span: Span, operand: Expr) -> Expr {
        self.node(span, ExprKind::Not(Box::new(operand)))
    }

    fn branch(&mut self, span: Span, cond: Expr, then_branch: Expr, else_branch: Expr) -> Expr {
        self.node(
            span,
            ExprKind::If {
                cond: Box::new(cond),
                then_branch: Box::new(then_branch),
                else_branch: Some(Box::new(else_branch)),
            },
        )
    }

    /// Lower a single term (anything that can appear as an operand).
    fn lower_primary(&mut self, pair: Pair<Rule>) -> Expr {
        let span = self.span_of(&pair);
        match pair.as_rule() {
            Rule::expr => self.lower_expr(pair),
            Rule::number => self.lower_number(span, pair.as_str()),
            Rule::string => {
                let raw = pair.as_str();
                let decoded = self.decode_string(span, &raw[1..raw.len() - 1]);
                self.node(span, ExprKind::Str(decoded))
            }
            Rule::boolean => {
                let is_true = pair.as_str() == "true";
                self.node(span, ExprKind::Bool(is_true))
            }
            Rule::name => {
                let name = pair.as_str().to_string();
                self.var(span, name)
            }
            Rule::record => self.lower_record(pair),
            Rule::list => self.lower_list(pair),
            Rule::declaration => self.lower_declaration(pair),
            Rule::destructure => self.lower_destructure(pair),
            Rule::function => self.lower_function(pair),
            Rule::conditional => self.lower_conditional(pair),
            Rule::match_expr => self.lower_match(pair),
            Rule::repeat_loop | Rule::count_loop | Rule::each_loop => self.lower_loop(pair),
            other => unreachable!("unexpected term rule {other:?}"),
        }
    }

    fn decode_string(&mut self, span: Span, inner: &str) -> String {
        let mut out = String::with_capacity(inner.len());
        let mut chars = inner.chars();
        while let Some(c) = chars.next() {
            if c != '\\' {
                out.push(c);
                continue;
            }
            match chars.next() {
                Some('"') => out.push('"'),
                Some('\\') => out.push('\\'),
                Some('n') => out.push('\n'),
                Some('t') => out.push('\t'),
                Some(other) => self.errors.push(GoatError::new(
                    span,
                    format!("unknown escape `\\{other}` in string"),
                )),
                None => unreachable!("grammar pairs every backslash with a character"),
            }
        }
        out
    }

    /// A name is a tag when one is declared and no binding shadows it.
    fn is_tag(&self, name: &str) -> bool {
        self.resolve(name).is_none() && self.tags.contains_key(name)
    }

    fn var(&mut self, span: Span, name: String) -> Expr {
        if self.is_tag(&name) {
            return self.tag_node(span, name, Vec::new());
        }
        if self.resolve(&name).is_none()
            && let Some(builtin) = Builtin::named(&name)
        {
            return self.node(span, ExprKind::Builtin(builtin));
        }
        let symbol = self.resolve(&name).unwrap_or_else(|| {
            let hint = self.similar_tag(&name).map_or_else(String::new, |tag| {
                format!(", did you mean the tag `{tag}`?")
            });
            self.errors
                .push(GoatError::new(span, format!("unknown name `{name}`{hint}")));
            self.fresh_symbol()
        });
        self.node(span, ExprKind::Var { symbol, name })
    }

    fn lower_declaration(&mut self, pair: Pair<Rule>) -> Expr {
        let (binding, rest) = self.lower_declaration_head(pair);
        let rest = rest.map(|p| self.lower_expr(p));
        self.scopes.pop();
        self.bound(binding, rest)
    }

    /// Bind the declaration's name in a new scope, which the caller pops once
    /// the declaration's `rest` is lowered, and lower its value.
    fn lower_declaration_head<'i>(
        &mut self,
        pair: Pair<'i, Rule>,
    ) -> (Binding, Option<Pair<'i, Rule>>) {
        let span = self.span_of(&pair);
        let mut inner = pair.into_inner();
        let name_pair = inner.next().expect("declaration starts with a name");
        let name = name_pair.as_str().to_string();
        let value_pair = inner.next().expect("declaration has a value");
        let rest_pair = inner.next();

        let shadows_builtin = Builtin::named(&name).is_some();
        if self.file == FileId::User && (self.prelude_scope.contains_key(&name) || shadows_builtin)
        {
            self.warnings.push(GoatError::new(
                self.span_of(&name_pair),
                format!("`{name}` replaces the built-in `{name}`"),
            ));
        }
        self.scopes.push(HashMap::new());
        let (symbol, value) = if is_program_literal(&value_pair) {
            let start = self.span_of(&name_pair).start;
            if !self.grouped.contains_key(&start) {
                self.bind_function_group(&name_pair, rest_pair.clone());
            }
            let symbol = match self.grouped.remove(&start).flatten() {
                Some(symbol) => {
                    self.bind_as(&name, symbol);
                    symbol
                }
                None => self.bind(&name),
            };
            (symbol, self.lower_expr(value_pair))
        } else {
            let value = if value_pair.as_rule() == Rule::foreign_decl {
                self.lower_foreign(value_pair)
            } else {
                self.lower_expr(value_pair)
            };
            (self.bind(&name), value)
        };
        let binding = Binding {
            span,
            symbol: Some(symbol),
            name,
            value,
        };
        (binding, rest_pair)
    }

    fn lower_foreign(&mut self, pair: Pair<Rule>) -> Expr {
        let span = self.span_of(&pair);
        let mut inner = pair
            .into_inner()
            .filter(|p| p.as_rule() != Rule::foreign_kw);
        let module = self.foreign_name(inner.next().expect("foreign names a module"), "module");
        let name = self.foreign_name(inner.next().expect("foreign names a function"), "name");
        let signature = inner.next().expect("foreign has a signature");
        let mut types = signature.into_inner();
        let ret = types
            .next_back()
            .expect("a signature ends in a return type");
        let params = types.map(|t| self.boundary(&t, "take")).collect();
        let ret = self.boundary(&ret, "return");
        self.node(
            span,
            ExprKind::Foreign {
                module,
                name,
                params,
                ret,
            },
        )
    }

    fn foreign_name(&mut self, pair: Pair<Rule>, what: &str) -> String {
        let span = self.span_of(&pair);
        let text = pair.as_str();
        let is_string = pair
            .into_inner()
            .next()
            .is_some_and(|p| p.as_rule() == Rule::string);
        if is_string {
            return self.decode_string(span, &text[1..text.len() - 1]);
        }
        self.errors.push(GoatError::new(
            span,
            format!("the {what} of a foreign function must be a string in quotes"),
        ));
        String::new()
    }

    /// `verb` is "take" for a parameter and "return" for a result.
    fn boundary(&mut self, ty: &Pair<Rule>, verb: &str) -> Boundary {
        let (shape, hint) = match ty.as_rule() {
            Rule::type_name => match Boundary::named(ty.as_str()) {
                Some(boundary) => return boundary,
                None => (
                    format!("`{}`", ty.as_str()),
                    "; the types that cross are Number, Int, Bool, Unit and String",
                ),
            },
            Rule::record_type => ("a record".to_string(), ""),
            Rule::list_type => ("a list".to_string(), ""),
            Rule::fn_type => ("a function".to_string(), ""),
            other => unreachable!("unexpected type rule {other:?}"),
        };
        self.errors.push(GoatError::new(
            self.span_of(ty),
            format!("foreign functions can't {verb} {shape} yet{hint}"),
        ));
        Boundary::Unit
    }

    /// Bind every function name in the declaration chain starting at `first`
    /// before any body is lowered, so bodies can call each other in any order.
    fn bind_function_group(&mut self, first: &Pair<Rule>, mut rest: Option<Pair<Rule>>) {
        let mut seen = HashSet::new();
        self.reserve(first, &mut seen);
        while let Some(expr) = rest.take() {
            let mut kids = expr.into_inner();
            let (Some(decl), None) = (kids.next(), kids.next()) else {
                break;
            };
            let is_declaration = match decl.as_rule() {
                Rule::declaration => true,
                Rule::destructure => false,
                _ => break,
            };
            let mut parts = decl.into_inner();
            let head = parts
                .next()
                .expect("a chain link starts with a name or pattern");
            let value = parts.next().expect("a chain link has a value");
            rest = parts.next();
            if is_declaration && is_program_literal(&value) {
                self.reserve(&head, &mut seen);
            }
        }
    }

    fn reserve(&mut self, name_pair: &Pair<Rule>, seen: &mut HashSet<String>) {
        let name = name_pair.as_str();
        let reserved = seen.insert(name.to_string()).then(|| {
            let symbol = self.fresh_symbol();
            self.bind_as(name, symbol);
            symbol
        });
        self.grouped.insert(self.span_of(name_pair).start, reserved);
    }

    fn lower_function(&mut self, pair: Pair<Rule>) -> Expr {
        let span = self.span_of(&pair);
        self.scopes.push(HashMap::new());
        let mut params = Vec::new();
        let mut unpacked = Vec::new();
        let mut list_params = Vec::new();
        let mut body_pair = None;
        for child in pair.into_inner() {
            match child.as_rule() {
                Rule::params => {
                    for param in child.into_inner() {
                        let pspan = self.span_of(&param);
                        let name = param.as_str().to_string();
                        if param.as_rule() == Rule::list_pattern {
                            let source = self.fresh_symbol();
                            list_params.push((source, param));
                            params.push(Param {
                                symbol: source,
                                name,
                                span: pspan,
                            });
                            continue;
                        }
                        if param.as_rule() == Rule::record_pattern {
                            let source = self.fresh_symbol();
                            let pattern = self.bind_record_pattern(param, "parameter");
                            unpacked.push((source, name.clone(), pattern));
                            params.push(Param {
                                symbol: source,
                                name,
                                span: pspan,
                            });
                            continue;
                        }
                        if self.scopes.last().is_some_and(|s| s.contains_key(&name)) {
                            self.errors.push(GoatError::new(
                                pspan,
                                format!("duplicate parameter `{name}`"),
                            ));
                        }
                        let symbol = self.bind(&name);
                        params.push(Param {
                            symbol,
                            name,
                            span: pspan,
                        });
                    }
                }
                Rule::expr => body_pair = Some(child),
                other => unreachable!("unexpected function child {other:?}"),
            }
        }
        let body = if list_params.is_empty() {
            body_pair.map(|b| self.lower_expr(b))
        } else {
            Some(self.lower_list_params(&list_params, body_pair, span))
        };
        self.scopes.pop();

        let mut body = body.unwrap_or_else(|| self.node(span, ExprKind::Unit));
        for (source, name, pattern) in unpacked.into_iter().rev() {
            body = self
                .unpack(source, &name, pattern, Some(body))
                .expect("a body was given");
        }
        self.node(
            span,
            ExprKind::Func {
                params,
                body: Box::new(body),
            },
        )
    }

    /// Bind the names of a `{x, y, ...rest}` pattern in the current scope.
    /// `what` names the construct in the duplicate-name error.
    fn bind_record_pattern(&mut self, pair: Pair<Rule>, what: &str) -> RecordPattern {
        let mut pattern = RecordPattern {
            fields: Vec::new(),
            rest: None,
        };
        for item in pair.into_inner() {
            let (name_pair, is_rest) = match item.as_rule() {
                Rule::rest_binding => (
                    item.into_inner()
                        .next()
                        .expect("`...` is followed by a name"),
                    true,
                ),
                _ => (item, false),
            };
            let span = self.span_of(&name_pair);
            let name = name_pair.as_str().to_string();
            if self.scopes.last().is_some_and(|s| s.contains_key(&name)) {
                self.errors
                    .push(GoatError::new(span, format!("duplicate {what} `{name}`")));
            }
            let symbol = self.bind(&name);
            if is_rest {
                pattern.rest = Some((symbol, name, span));
            } else {
                pattern.fields.push((symbol, name, span));
            }
        }
        pattern
    }

    /// A node built from a fresh use of the pattern's source variable.
    fn read_source(
        &mut self,
        (symbol, name): (Symbol, &str),
        span: Span,
        wrap: impl FnOnce(Box<Expr>) -> ExprKind,
    ) -> Expr {
        let var = ExprKind::Var {
            symbol,
            name: name.to_string(),
        };
        let record = self.node(span, var);
        self.node(span, wrap(Box::new(record)))
    }

    /// `x = source.x  y = source.y  rest = source minus x, y` followed by
    /// `body`: a record pattern is sugar for reading its fields.
    fn unpack(
        &mut self,
        source: Symbol,
        source_name: &str,
        pattern: RecordPattern,
        body: Option<Expr>,
    ) -> Option<Expr> {
        let labels: Vec<String> = pattern.fields.iter().map(|(_, n, _)| n.clone()).collect();
        let source = (source, source_name);
        let mut bindings = Vec::new();
        for (symbol, name, span) in pattern.fields {
            let label = name.clone();
            let value = self.read_source(source, span, |record| ExprKind::Field { record, label });
            bindings.push((symbol, name, span, value));
        }
        if let Some((symbol, name, span)) = pattern.rest {
            let value =
                self.read_source(source, span, |record| ExprKind::Restrict { record, labels });
            bindings.push((symbol, name, span, value));
        }
        bindings
            .into_iter()
            .rev()
            .fold(body, |rest, (symbol, name, binding_span, value)| {
                Some(self.node(
                    binding_span,
                    ExprKind::Let {
                        symbol,
                        name,
                        value: Box::new(value),
                        rest: rest.map(Box::new),
                    },
                ))
            })
    }

    /// `{x, y} = value rest`: bind `value` once, then each name from it.
    fn lower_destructure(&mut self, pair: Pair<Rule>) -> Expr {
        let span = self.span_of(&pair);
        let mut inner = pair.into_inner();
        let pattern_pair = inner.next().expect("destructuring begins with a pattern");
        let value_pair = inner.next().expect("destructuring has a value");
        let rest_pair = inner.next();
        let source_name = pattern_pair.as_str().to_string();

        let value = self.lower_expr(value_pair);
        let source = self.fresh_symbol();
        let unpacked = if pattern_pair.as_rule() == Rule::list_pattern {
            Some(self.lower_list_binding(source, pattern_pair, Then::Rest(rest_pair)))
        } else {
            self.scopes.push(HashMap::new());
            let pattern = self.bind_record_pattern(pattern_pair, "name");
            let rest = rest_pair.map(|p| self.lower_expr(p));
            self.scopes.pop();
            self.unpack(source, &source_name, pattern, rest)
        };
        self.node(
            span,
            ExprKind::Let {
                symbol: source,
                name: source_name,
                value: Box::new(value),
                rest: unpacked.map(Box::new),
            },
        )
    }

    fn lower_record(&mut self, pair: Pair<Rule>) -> Expr {
        let span = self.span_of(&pair);
        let mut base = None;
        let mut spreads = 0;
        let mut fields = Vec::new();
        for (position, item) in pair.into_inner().enumerate() {
            if item.as_rule() == Rule::spread {
                let item_span = self.span_of(&item);
                let target = item
                    .into_inner()
                    .next()
                    .expect("`...` is followed by an expression");
                let target = self.lower_expr(target);
                spreads += 1;
                if spreads > 1 {
                    self.errors.push(GoatError::new(
                        item_span,
                        "can't merge two records of unknown shape here; spread one record and write the other's fields out",
                    ));
                } else if position != 0 {
                    self.errors.push(GoatError::new(
                        item_span,
                        "`...` must come first in a record, so the fields after it override it",
                    ));
                } else {
                    base = Some(target);
                }
                continue;
            }
            debug_assert_eq!(item.as_rule(), Rule::field);
            let mut it = item.into_inner();
            let label_pair = it.next().expect("a field begins with a label");
            let label_span = self.span_of(&label_pair);
            let label = label_pair.as_str().to_string();
            let value = self.lower_expr(it.next().expect("a field has a value"));
            if fields.iter().any(|(l, _)| *l == label) {
                self.errors.push(GoatError::new(
                    label_span,
                    format!("duplicate field `{label}` in record"),
                ));
                continue;
            }
            fields.push((label, value));
        }
        match base {
            Some(base) => self.node(
                span,
                ExprKind::Spread {
                    base: Box::new(base),
                    fields,
                },
            ),
            None => self.node(span, ExprKind::Record { fields }),
        }
    }

    /// The declared tag closest to an unknown `name`: the same word in another
    /// case, or one edit away.
    fn similar_tag(&self, name: &str) -> Option<&str> {
        let name: Vec<char> = name.to_lowercase().chars().collect();
        self.tags
            .keys()
            .filter(|tag| within_one_edit(&tag.to_lowercase().chars().collect::<Vec<_>>(), &name))
            .min()
            .map(String::as_str)
    }

    /// `Circle(5)`: the declared tag `name` and, if a call follows, its payload.
    /// `Empty()` is the same as `Empty`.
    fn lower_tag(&mut self, name: Pair<Rule>, inner: &mut Peekable<Pairs<Rule>>) -> Expr {
        let mut span = self.span_of(&name);
        let args = match inner.next_if(|p| p.as_rule() == Rule::call) {
            Some(call) => {
                span = span.to(self.span_of(&call));
                call.into_inner()
                    .flat_map(|arguments| arguments.into_inner())
                    .map(|a| self.lower_expr(a))
                    .collect()
            }
            None => Vec::new(),
        };
        self.tag_node(span, name.as_str().to_string(), args)
    }

    /// One argument is the payload as is; several become a record labelled
    /// `"0"`, `"1"`, ... in argument order.
    fn tag_node(&mut self, span: Span, name: String, mut args: Vec<Expr>) -> Expr {
        let payload = match args.len() {
            0 => None,
            1 => args.pop(),
            _ => {
                let fields = args
                    .into_iter()
                    .enumerate()
                    .map(|(i, arg)| (i.to_string(), arg))
                    .collect();
                Some(self.node(span, ExprKind::Record { fields }))
            }
        };
        let group = self.tags.get(&name).cloned().flatten();
        self.node(
            span,
            ExprKind::Tag {
                name,
                payload: payload.map(Box::new),
                group,
            },
        )
    }

    /// `[a, b]` is `Link(a, Link(b, Empty))`.
    fn lower_list(&mut self, pair: Pair<Rule>) -> Expr {
        let span = self.span_of(&pair);
        let items: Vec<Pair<Rule>> = pair.into_inner().flat_map(|a| a.into_inner()).collect();
        if self.depth + items.len() > MAX_DEPTH {
            self.errors
                .push(GoatError::new(span, "list has too many items to write out"));
            return self.node(span, ExprKind::Unit);
        }
        self.depth += items.len();
        let items: Vec<Expr> = items.into_iter().map(|a| self.lower_expr(a)).collect();
        self.depth -= items.len();
        let empty = self.tag_node(span, "Empty".into(), Vec::new());
        items.into_iter().rev().fold(empty, |tail, item| {
            self.tag_node(span, "Link".into(), vec![item, tail])
        })
    }

    fn lower_match(&mut self, pair: Pair<Rule>) -> Expr {
        let span = self.span_of(&pair);
        let mut inner = pair.into_inner();
        let scrutinee = self.lower_expr(inner.next().expect("match has a scrutinee"));
        let children: Vec<Pair<Rule>> = inner.collect();
        if children.iter().any(is_list_arm) {
            return self.lower_list_match(span, scrutinee, children);
        }
        if children.iter().any(is_literal_arm) {
            return self.lower_literal_match(span, scrutinee, children);
        }
        let mut arms = Vec::new();
        let mut else_branch = None;
        for child in children {
            match child.as_rule() {
                Rule::arm => arms.push(self.lower_arm(child)),
                Rule::expr => else_branch = Some(Box::new(self.lower_expr(child))),
                other => unreachable!("unexpected match child {other:?}"),
            }
        }
        self.node(
            span,
            ExprKind::Match {
                scrutinee: Box::new(scrutinee),
                arms,
                else_branch,
            },
        )
    }

    /// A `match` whose arms are scalar literals becomes a chain of equality
    /// tests on the scrutinee, evaluated once:
    ///
    /// ```text
    /// match e do 0 then a  1 then b  else c done
    ///   v = e  if v == 0 then a else if v == 1 then b else c done done
    /// ```
    ///
    /// Number and string domains are infinite, so they need an `else`; a bool
    /// match naming both `true` and `false` doesn't, and its last arm is the
    /// fall-through.
    fn lower_literal_match<'i>(
        &mut self,
        span: Span,
        scrutinee: Expr,
        children: Vec<Pair<'i, Rule>>,
    ) -> Expr {
        if self.depth + children.len() > MAX_DEPTH {
            self.errors.push(GoatError::new(
                span,
                "`match` has too many arms to write out",
            ));
            return self.node(span, ExprKind::Unit);
        }
        let charged = children.len();
        self.depth += charged;
        let mut rows: Vec<(Expr, Expr)> = Vec::new();
        let mut otherwise = None;
        for child in children {
            if child.as_rule() == Rule::expr {
                otherwise = Some(self.lower_expr(child));
                continue;
            }
            let mut inner = child.into_inner();
            let pattern = inner.next().expect("an arm begins with a pattern");
            let body = inner.next().expect("an arm has a body");
            let body = self.lower_expr(body);
            if pattern.as_rule() != Rule::literal_pattern {
                self.errors.push(GoatError::new(
                    self.span_of(&pattern),
                    "a `match` can't mix literal patterns with tag or list patterns",
                ));
                continue;
            }
            let literal = pattern.into_inner().next().expect("a literal pattern");
            let literal = self.lower_primary(literal);
            if rows
                .first()
                .is_some_and(|(first, _)| scalar_kind(first) != scalar_kind(&literal))
            {
                self.errors.push(GoatError::new(
                    literal.span,
                    "a `match` can't mix patterns of different types; every arm must match the same type",
                ));
                continue;
            }
            rows.push((literal, body));
        }
        self.depth -= charged;

        let covers_bool = rows
            .iter()
            .any(|(l, _)| matches!(l.kind, ExprKind::Bool(true)))
            && rows
                .iter()
                .any(|(l, _)| matches!(l.kind, ExprKind::Bool(false)));
        let mut tail = match otherwise {
            Some(expr) => expr,
            None if covers_bool => rows.pop().expect("both bool arms are present").1,
            None => {
                if !rows.is_empty() {
                    self.errors.push(GoatError::new(
                        scrutinee.span,
                        "a `match` on values needs an `else` to cover every other value",
                    ));
                }
                return self.node(span, ExprKind::Unit);
            }
        };
        if rows.is_empty() {
            return tail;
        }

        let (source, bind) = match scrutinee.kind {
            ExprKind::Var { symbol, .. } => (symbol, None),
            _ => (self.fresh_symbol(), Some(scrutinee)),
        };
        let name: String = "match".into();
        for (literal, body) in rows.into_iter().rev() {
            let subject = self.node(
                literal.span,
                ExprKind::Var {
                    symbol: source,
                    name: name.clone(),
                },
            );
            let test = self.node(
                literal.span,
                ExprKind::Bin {
                    op: BinOp::Eq,
                    lhs: Box::new(subject),
                    rhs: Box::new(literal),
                },
            );
            tail = self.branch(span, test, body, tail);
        }
        match bind {
            Some(value) => self.node(
                span,
                ExprKind::Let {
                    symbol: source,
                    name,
                    value: Box::new(value),
                    rest: Some(Box::new(tail)),
                },
            ),
            None => tail,
        }
    }

    fn lower_arm(&mut self, pair: Pair<Rule>) -> MatchArm {
        let mut inner = pair.into_inner();
        let pattern_pair = inner.next().expect("an arm begins with a pattern");
        let body_pair = inner.next().expect("an arm has a body");

        self.scopes.push(HashMap::new());
        let pattern = self.lower_pattern(pattern_pair);
        let body = self.lower_expr(body_pair);
        self.scopes.pop();
        MatchArm { pattern, body }
    }

    fn lower_pattern(&mut self, pair: Pair<Rule>) -> Pattern {
        let span = self.span_of(&pair);
        let mut inner = pair.into_inner();
        let head = inner.next().expect("a pattern begins with a tag name");
        let tag = head.as_str().to_string();
        if !self.tags.contains_key(&tag) {
            let hint = self
                .similar_tag(&tag)
                .map_or_else(String::new, |t| format!(", did you mean `{t}`?"));
            self.errors.push(GoatError::new(
                self.span_of(&head),
                format!("unknown tag `{tag}`{hint}"),
            ));
        }
        let mut binders: Vec<Param> = Vec::new();
        for label in inner.flat_map(|labels| labels.into_inner()) {
            let pspan = self.span_of(&label);
            let name = label.as_str().to_string();
            if binders.iter().any(|b| b.name == name) {
                self.errors.push(GoatError::new(
                    pspan,
                    format!("duplicate binding `{name}` in pattern"),
                ));
            }
            let symbol = self.bind(&name);
            binders.push(Param {
                symbol,
                name,
                span: pspan,
            });
        }
        let payload = match binders.len() {
            0 => PatternPayload::None,
            1 => PatternPayload::Whole(binders.remove(0)),
            _ => PatternPayload::Fields(
                binders
                    .into_iter()
                    .enumerate()
                    .map(|(i, b)| (i.to_string(), b))
                    .collect(),
            ),
        };
        Pattern { tag, span, payload }
    }

    fn list_pattern(&mut self, pair: Pair<Rule>) -> ListPattern {
        let span = self.span_of(&pair);
        let mut items: Vec<(String, Span)> = Vec::new();
        let mut rest = None;
        for item in pair.into_inner() {
            let is_rest = item.as_rule() == Rule::rest_binding;
            let name_pair = if is_rest {
                item.into_inner()
                    .next()
                    .expect("`...` is followed by a name")
            } else {
                item
            };
            let name = name_pair.as_str().to_string();
            let name_span = self.span_of(&name_pair);
            let taken = items.iter().any(|(n, _)| *n == name)
                || rest
                    .as_ref()
                    .is_some_and(|(n, _): &(String, Span)| *n == name);
            if taken {
                self.errors.push(GoatError::new(
                    name_span,
                    format!("duplicate binding `{name}` in pattern"),
                ));
            }
            if is_rest {
                rest = Some((name, name_span));
            } else {
                items.push((name, name_span));
            }
        }
        ListPattern { span, items, rest }
    }

    /// A `match` whose arms are list patterns: `[]`, `[a, b]`, `[a, ...rest]`.
    fn lower_list_match<'i>(
        &mut self,
        span: Span,
        scrutinee: Expr,
        children: Vec<Pair<'i, Rule>>,
    ) -> Expr {
        let mut rows = Vec::new();
        let mut otherwise = None;
        for child in children {
            if child.as_rule() == Rule::expr {
                otherwise = Some(child);
                continue;
            }
            let mut inner = child.into_inner();
            let pattern = inner.next().expect("an arm begins with a pattern");
            let body = inner.next().expect("an arm has a body");
            if pattern.as_rule() == Rule::list_pattern {
                let pattern = self.list_pattern(pattern);
                rows.push((pattern, Then::Arm(body), false));
            } else {
                self.errors.push(GoatError::new(
                    self.span_of(&pattern),
                    "a `match` on a list can't mix list patterns with tag patterns",
                ));
            }
        }
        if rows.is_empty() {
            return self.node(span, ExprKind::Unit);
        }
        // A `...rest` with no items before it names the scrutinee itself, so
        // the scrutinee needs a binding to read it from.
        let needs_name = rows
            .iter()
            .any(|(p, ..)| p.items.is_empty() && p.rest.is_some());
        if let ExprKind::Var { symbol, .. } = scrutinee.kind {
            return self.compile_list_match(span, scrutinee, symbol, rows, otherwise);
        }
        let source = self.fresh_symbol();
        if !needs_name {
            return self.compile_list_match(span, scrutinee, source, rows, otherwise);
        }
        let var = self.list_var(scrutinee.span, source);
        let rest = self.compile_list_match(span, var, source, rows, otherwise);
        self.node(
            span,
            ExprKind::Let {
                symbol: source,
                name: LIST_NAME.into(),
                value: Box::new(scrutinee),
                rest: Some(Box::new(rest)),
            },
        )
    }

    fn list_var(&mut self, span: Span, symbol: Symbol) -> Expr {
        let name = LIST_NAME.into();
        self.node(span, ExprKind::Var { symbol, name })
    }

    /// Compile the rows into nested matches on `Empty` and `Link`, trying
    /// them in order. `source` is the symbol `scrutinee` reads, for a
    /// `...rest` that names the whole list.
    fn compile_list_match<'i>(
        &mut self,
        span: Span,
        scrutinee: Expr,
        source: Symbol,
        rows: Vec<(ListPattern, Then<'i>, bool)>,
        otherwise: Option<Pair<'i, Rule>>,
    ) -> Expr {
        // Each item adds a nested match, and each name a binding around the body.
        let extra = rows
            .iter()
            .map(|(p, ..)| 2 * p.items.len() + 2)
            .max()
            .unwrap_or(0);
        if self.depth + extra > MAX_DEPTH {
            self.errors
                .push(GoatError::new(span, "list pattern nested too deeply"));
            return self.node(span, ExprKind::Unit);
        }
        self.depth += extra;
        let live = (0..rows.len())
            .map(|row| Progress {
                row,
                bound: Vec::new(),
                rest_from: source,
            })
            .collect();
        let mut m = ListMatch {
            rows,
            otherwise,
            otherwise_lowered: false,
        };
        let tree = self.build_list_tree(&mut m, scrutinee, live);
        self.lower_unreached_arms(&mut m);
        self.depth -= extra;
        tree.unwrap_or_else(|| self.node(span, ExprKind::Unit))
    }

    /// The match on `scrutinee` for the arms in `live`, in order. `None` when
    /// none of them can match what remains.
    fn build_list_tree<'i>(
        &mut self,
        m: &mut ListMatch<'i>,
        scrutinee: Expr,
        live: Vec<Progress>,
    ) -> Option<Expr> {
        let first = live.first()?;
        if m.is_catch_all(first) {
            return Some(self.list_leaf(m, first));
        }
        let span = m.rows[first.row].0.span;
        let mut arms = Vec::new();
        if let Some(at) = live.iter().find(|at| m.is_done(at)) {
            let body = self.list_leaf(m, at);
            let pattern = Pattern {
                tag: "Empty".into(),
                span,
                payload: PatternPayload::None,
            };
            arms.push(MatchArm { pattern, body });
        }

        let head = self.fresh_symbol();
        let tail = self.fresh_symbol();
        let deeper: Vec<Progress> = live
            .iter()
            .filter_map(|at| {
                if !m.is_done(at) {
                    let mut at = at.clone();
                    at.bound.push(head);
                    at.rest_from = tail;
                    Some(at)
                } else {
                    m.rows[at.row].0.rest.is_some().then(|| at.clone())
                }
            })
            .collect();
        let tail_var = self.list_var(span, tail);
        if let Some(body) = self.build_list_tree(m, tail_var, deeper) {
            let binder = |symbol, name: &str| Param {
                symbol,
                name: name.into(),
                span,
            };
            let pattern = Pattern {
                tag: "Link".into(),
                span,
                payload: PatternPayload::Fields(vec![
                    ("0".into(), binder(head, "head")),
                    ("1".into(), binder(tail, "tail")),
                ]),
            };
            arms.push(MatchArm { pattern, body });
        }
        if arms.is_empty() {
            return None;
        }

        let else_branch = match m.otherwise.clone() {
            Some(body) if arms.len() < 2 => {
                let first_time = !std::mem::replace(&mut m.otherwise_lowered, true);
                Some(Box::new(
                    self.relower(first_time, |this| this.lower_expr(body)),
                ))
            }
            _ => None,
        };
        Some(self.node(
            span,
            ExprKind::Match {
                scrutinee: Box::new(scrutinee),
                arms,
                else_branch,
            },
        ))
    }

    /// An arm's body, with the names its pattern bound read off the list
    /// nodes the tree took apart to reach it.
    fn list_leaf(&mut self, m: &mut ListMatch<'_>, at: &Progress) -> Expr {
        let (pattern, then, lowered) = &mut m.rows[at.row];
        let span = pattern.span;
        let first_time = !std::mem::replace(lowered, true);
        let then = then.clone();

        self.list_leaves += 1;
        if self.list_leaves > MAX_LIST_LEAVES {
            if self.list_leaves == MAX_LIST_LEAVES + 1 {
                self.errors
                    .push(GoatError::new(span, "list patterns expand too far here"));
            }
            return self.node(span, ExprKind::Unit);
        }

        let names: Vec<(String, Span, Symbol)> = pattern
            .items
            .iter()
            .zip(&at.bound)
            .map(|((name, span), from)| (name.clone(), *span, *from))
            .chain(
                pattern
                    .rest
                    .as_ref()
                    .map(|(name, span)| (name.clone(), *span, at.rest_from)),
            )
            .collect();

        self.scopes.push(HashMap::new());
        let bindings: Vec<_> = names
            .into_iter()
            .map(|(name, span, from)| (self.bind(&name), name, span, from))
            .collect();
        let body = self.relower(first_time, |this| this.lower_then(then, span));
        self.scopes.pop();

        bindings
            .into_iter()
            .rev()
            .fold(body, |rest, (symbol, name, span, from)| {
                let value = self.list_var(span, from);
                self.node(
                    span,
                    ExprKind::Let {
                        symbol,
                        name,
                        value: Box::new(value),
                        rest: Some(Box::new(rest)),
                    },
                )
            })
    }

    /// Lower with `f`, discarding the diagnostics it adds when an earlier
    /// lowering of the same source already reported them.
    fn relower<T>(&mut self, first_time: bool, f: impl FnOnce(&mut Self) -> T) -> T {
        let (errors, warnings) = (self.errors.len(), self.warnings.len());
        let out = f(self);
        if !first_time {
            self.errors.truncate(errors);
            self.warnings.truncate(warnings);
        }
        out
    }

    fn lower_then(&mut self, then: Then<'_>, span: Span) -> Expr {
        match then {
            Then::Arm(body) | Then::Rest(Some(body)) => self.lower_expr(body),
            Then::Rest(None) => self.node(span, ExprKind::Unit),
            Then::Params(params, body) => self.lower_list_params(&params, body, span),
        }
    }

    /// Arms the tree never reaches are shadowed by earlier ones. They are
    /// still lowered so their own mistakes get reported.
    fn lower_unreached_arms(&mut self, m: &mut ListMatch<'_>) {
        for row in 0..m.rows.len() {
            if m.rows[row].2 {
                continue;
            }
            let span = m.rows[row].0.span;
            self.errors.push(GoatError::new(
                span,
                "this arm never matches; earlier arms already cover every list it would",
            ));
            let bound = m.rows[row]
                .0
                .items
                .iter()
                .map(|_| self.fresh_symbol())
                .collect();
            let rest_from = self.fresh_symbol();
            let at = Progress {
                row,
                bound,
                rest_from,
            };
            self.list_leaf(m, &at);
        }
        if let Some(body) = m.otherwise.clone()
            && !m.otherwise_lowered
        {
            self.lower_expr(body);
        }
    }

    /// `[a, b] = value` (or a `[a, b]` parameter): match `source` against the
    /// pattern, then run `then` with its names bound.
    fn lower_list_binding<'i>(
        &mut self,
        source: Symbol,
        pattern: Pair<'i, Rule>,
        then: Then<'i>,
    ) -> Expr {
        let pattern = self.list_pattern(pattern);
        let span = pattern.span;
        let scrutinee = self.list_var(span, source);
        self.compile_list_match(span, scrutinee, source, vec![(pattern, then, false)], None)
    }

    /// Unpack each list-pattern parameter in turn around `body`.
    fn lower_list_params<'i>(
        &mut self,
        params: &[(Symbol, Pair<'i, Rule>)],
        body: Option<Pair<'i, Rule>>,
        span: Span,
    ) -> Expr {
        match params.split_first() {
            None => match body {
                Some(body) => self.lower_expr(body),
                None => self.node(span, ExprKind::Unit),
            },
            Some(((source, pattern), later)) => {
                let then = Then::Params(later.to_vec(), body);
                self.lower_list_binding(*source, pattern.clone(), then)
            }
        }
    }

    fn lower_conditional(&mut self, pair: Pair<Rule>) -> Expr {
        let span = self.span_of(&pair);
        let mut inner = pair.into_inner();
        let cond = self.lower_expr(inner.next().expect("if has a condition"));
        let then_branch = self.lower_expr(inner.next().expect("if has a then branch"));
        let else_branch = inner.next().map(|p| Box::new(self.lower_expr(p)));
        self.node(
            span,
            ExprKind::If {
                cond: Box::new(cond),
                then_branch: Box::new(then_branch),
                else_branch,
            },
        )
    }

    /// A loop is a local function that runs the body and calls itself for the
    /// next step, so it needs no loop node: the tail call is the jump.
    ///
    /// ```text
    /// repeat n times do B done          for i from a to b do B done
    ///   start = 0  stop = n               start = a  stop = b
    ///   go = program(i) do                go = program(i) do
    ///     if i < stop then                  if i <= stop then
    ///       _ = B  go(i + 1)                  _ = B  go(i + 1)
    ///     else () done done                 else () done done
    ///   go(start)                         go(start)
    /// ```
    ///
    /// A counter's literals take whichever of `Int` and `Float` the loop's use of it needs.
    #[inline(never)]
    fn lower_loop(&mut self, pair: Pair<Rule>) -> Expr {
        let span = self.span_of(&pair);
        let rule = pair.as_rule();
        let mut inner = pair.into_inner().filter(|p| {
            !matches!(
                p.as_rule(),
                Rule::for_kw | Rule::from_kw | Rule::to_kw | Rule::in_kw
            )
        });
        if rule == Rule::each_loop {
            let name_pair = inner.next().expect("a `for` names its item");
            let list = self.lower_expr(inner.next().expect("`in` is followed by a list"));
            return self.each_loop(span, &name_pair, list, inner.next());
        }
        let counter =
            (rule == Rule::count_loop).then(|| inner.next().expect("a `for` names its counter"));
        let (start, stop, compare) = if counter.is_some() {
            let start = self.lower_expr(inner.next().expect("`from` is followed by a start"));
            let stop = self.lower_expr(inner.next().expect("`to` is followed by an end"));
            (start, stop, BinOp::Lte)
        } else {
            let count = self.lower_expr(inner.next().expect("`repeat` is followed by a count"));
            (self.node(span, ExprKind::Int(0)), count, BinOp::Lt)
        };
        self.counted_loop(span, counter.as_ref(), (start, stop, compare), inner.next())
    }

    fn counted_loop(
        &mut self,
        span: Span,
        counter: Option<&Pair<Rule>>,
        (start, stop, compare): (Expr, Expr, BinOp),
        body: Option<Pair<Rule>>,
    ) -> Expr {
        let start_symbol = self.fresh_symbol();
        let stop_symbol = self.fresh_symbol();
        let go = self.fresh_symbol();
        self.scopes.push(HashMap::new());
        let (i, i_name) = match counter {
            Some(name_pair) => (self.bind(name_pair.as_str()), name_pair.as_str()),
            None => (self.fresh_symbol(), LOOP_COUNTER_NAME),
        };
        let body = self.lower_loop_body(span, body);
        self.scopes.pop();

        let i_now = self.var_node(span, i, i_name);
        let stop_now = self.var_node(span, stop_symbol, LOOP_STOP_NAME);
        let in_range = self.node(
            span,
            ExprKind::Bin {
                op: compare,
                lhs: Box::new(i_now),
                rhs: Box::new(stop_now),
            },
        );
        let i_now = self.var_node(span, i, i_name);
        let one = self.node(span, ExprKind::Int(1));
        let next_i = self.node(
            span,
            ExprKind::Bin {
                op: BinOp::Add,
                lhs: Box::new(i_now),
                rhs: Box::new(one),
            },
        );
        let again = self.call_loop(span, go, next_i);
        let step = self.discard(span, body, again);
        let done = self.node(span, ExprKind::Unit);
        let looping = self.branch(span, in_range, step, done);

        let param = Param {
            symbol: i,
            name: i_name.into(),
            span,
        };
        let first = self.var_node(span, start_symbol, LOOP_START_NAME);
        let entry = self.call_loop(span, go, first);
        let run = self.bind_loop(span, (go, vec![param], looping), entry);
        let with_stop = self.let_node(span, (stop_symbol, LOOP_STOP_NAME), stop, run);
        self.let_node(span, (start_symbol, LOOP_START_NAME), start, with_stop)
    }

    fn each_loop(
        &mut self,
        span: Span,
        name_pair: &Pair<Rule>,
        list: Expr,
        body: Option<Pair<Rule>>,
    ) -> Expr {
        let go = self.fresh_symbol();
        let remaining = self.fresh_symbol();
        let tail = self.fresh_symbol();
        self.scopes.push(HashMap::new());
        let item = self.bind(name_pair.as_str());
        let body = self.lower_loop_body(span, body);
        self.scopes.pop();

        let tail_now = self.var_node(span, tail, LIST_NAME);
        let again = self.call_loop(span, go, tail_now);
        let step = self.discard(span, body, again);
        let param = |symbol, name: &str| Param {
            symbol,
            name: name.into(),
            span,
        };
        let link = MatchArm {
            pattern: Pattern {
                tag: "Link".into(),
                span,
                payload: PatternPayload::Fields(vec![
                    ("0".into(), param(item, name_pair.as_str())),
                    ("1".into(), param(tail, LIST_NAME)),
                ]),
            },
            body: step,
        };
        let empty = MatchArm {
            pattern: Pattern {
                tag: "Empty".into(),
                span,
                payload: PatternPayload::None,
            },
            body: self.node(span, ExprKind::Unit),
        };
        let scrutinee = self.var_node(span, remaining, LIST_NAME);
        let walk = self.node(
            span,
            ExprKind::Match {
                scrutinee: Box::new(scrutinee),
                arms: vec![empty, link],
                else_branch: None,
            },
        );

        let entry = self.call_loop(span, go, list);
        self.bind_loop(span, (go, vec![param(remaining, LIST_NAME)], walk), entry)
    }

    fn lower_loop_body(&mut self, span: Span, body: Option<Pair<Rule>>) -> Expr {
        match body {
            Some(body) => self.lower_expr(body),
            None => self.node(span, ExprKind::Unit),
        }
    }

    fn var_node(&mut self, span: Span, symbol: Symbol, name: &str) -> Expr {
        let name = name.into();
        self.node(span, ExprKind::Var { symbol, name })
    }

    fn call_loop(&mut self, span: Span, go: Symbol, arg: Expr) -> Expr {
        let callee = self.var_node(span, go, LOOP_NAME);
        self.node(
            span,
            ExprKind::App {
                callee: Box::new(callee),
                args: vec![arg],
            },
        )
    }

    /// `go = program(params) do body done  rest`
    fn bind_loop(
        &mut self,
        span: Span,
        (go, params, body): (Symbol, Vec<Param>, Expr),
        rest: Expr,
    ) -> Expr {
        let func = self.node(
            span,
            ExprKind::Func {
                params,
                body: Box::new(body),
            },
        );
        self.let_node(span, (go, LOOP_NAME), func, rest)
    }

    fn let_node(
        &mut self,
        span: Span,
        (symbol, name): (Symbol, &str),
        value: Expr,
        rest: Expr,
    ) -> Expr {
        self.node(
            span,
            ExprKind::Let {
                symbol,
                name: name.into(),
                value: Box::new(value),
                rest: Some(Box::new(rest)),
            },
        )
    }
}

fn within_one_edit(a: &[char], b: &[char]) -> bool {
    if a.len().abs_diff(b.len()) > 1 {
        return false;
    }
    let common = a.iter().zip(b).take_while(|(x, y)| x == y).count();
    let (a, b) = (&a[common..], &b[common..]);
    match a.len().cmp(&b.len()) {
        std::cmp::Ordering::Equal => a.is_empty() || a[1..] == b[1..],
        std::cmp::Ordering::Greater => a[1..] == *b,
        std::cmp::Ordering::Less => *a == b[1..],
    }
}

/// One link of a block's spine: a name bound to a value for what follows. A
/// `;`-sequenced statement binds its value to a name nothing can mention
/// (`symbol` is `None` until the link is built).
struct Binding {
    span: Span,
    symbol: Option<Symbol>,
    name: String,
    value: Expr,
}

/// The declaration that is all of what remains in `kids`, since a
/// declaration's `rest` takes everything after it.
fn sole_declaration<'i>(kids: &Peekable<Pairs<'i, Rule>>) -> Option<Pair<'i, Rule>> {
    let mut kids = kids.clone();
    match (kids.next(), kids.next()) {
        (Some(only), None) if only.as_rule() == Rule::declaration => Some(only),
        _ => None,
    }
}

/// How deep the statement at the front of `kids` can get: a left-leaning tree
/// of its operands, plus a level for each `not`. The statements after a `;`
/// are lowered on their own.
fn chain_depth(kids: &Peekable<Pairs<Rule>>) -> usize {
    let (mut nots, mut others) = (0, 0);
    for child in kids.clone().take_while(|p| p.as_rule() != Rule::sequel) {
        match child.as_rule() {
            Rule::not_op => nots += 1,
            _ => others += 1,
        }
    }
    others / 2 + 1 + nots
}

fn is_list_arm(child: &Pair<Rule>) -> bool {
    child.as_rule() == Rule::arm
        && child
            .clone()
            .into_inner()
            .next()
            .is_some_and(|p| p.as_rule() == Rule::list_pattern)
}

fn is_literal_arm(child: &Pair<Rule>) -> bool {
    child.as_rule() == Rule::arm
        && child
            .clone()
            .into_inner()
            .next()
            .is_some_and(|p| p.as_rule() == Rule::literal_pattern)
}

/// `Int` and `Float` literals are both numbers, so they may share a `match`.
fn scalar_kind(literal: &Expr) -> std::mem::Discriminant<ExprKind> {
    match literal.kind {
        ExprKind::Float(_) => std::mem::discriminant(&ExprKind::Int(0)),
        _ => std::mem::discriminant(&literal.kind),
    }
}

fn is_program_literal(expr: &Pair<Rule>) -> bool {
    let mut kids = expr.clone().into_inner();
    matches!((kids.next(), kids.next()), (Some(p), None) if p.as_rule() == Rule::function)
}

/// An operator while a chain is being folded: `and`/`or` lower to `if` rather
/// than to a `Bin`, and `not` is the one prefix operator.
#[derive(Clone, Copy, PartialEq)]
enum Op {
    Bin(BinOp),
    And,
    Or,
    Not,
}

fn infix_op(rule: Rule) -> Op {
    match rule {
        Rule::and_op => Op::And,
        Rule::or_op => Op::Or,
        Rule::plus => Op::Bin(BinOp::Add),
        Rule::minus => Op::Bin(BinOp::Sub),
        Rule::multiply => Op::Bin(BinOp::Mul),
        Rule::divide => Op::Bin(BinOp::Div),
        Rule::lt => Op::Bin(BinOp::Lt),
        Rule::lte => Op::Bin(BinOp::Lte),
        Rule::gt => Op::Bin(BinOp::Gt),
        Rule::gte => Op::Bin(BinOp::Gte),
        Rule::equal => Op::Bin(BinOp::Eq),
        Rule::not_equal => Op::Bin(BinOp::Ne),
        other => unreachable!("not an operator rule: {other:?}"),
    }
}

/// Binding strength, loosest first: `or`, `and`, `not`, equality,
/// comparison, `+ -`, `* /`.
fn prec(op: Op) -> u8 {
    match op {
        Op::Or => 1,
        Op::And => 2,
        Op::Not => 3,
        Op::Bin(BinOp::Eq | BinOp::Ne) => 4,
        Op::Bin(BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte) => 5,
        Op::Bin(BinOp::Add | BinOp::Sub) => 6,
        Op::Bin(BinOp::Mul | BinOp::Div) => 7,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn string_value(source: &str) -> Result<String, String> {
        let lowered = lower(source).map_err(|e| e.message)?;
        if let Some(e) = lowered.errors.first() {
            return Err(e.message.clone());
        }
        match lowered.root.kind {
            ExprKind::Str(s) => Ok(s),
            other => panic!("expected a string, got {other:?}"),
        }
    }

    #[test]
    fn decodes_escapes() {
        assert_eq!(string_value(r#""say \"hi\"""#).unwrap(), "say \"hi\"");
        assert_eq!(string_value(r#""line\nbreak""#).unwrap(), "line\nbreak");
        assert_eq!(string_value(r#""a\tb""#).unwrap(), "a\tb");
        assert_eq!(string_value(r#""\\""#).unwrap(), "\\");
    }

    #[test]
    fn rejects_unknown_escape() {
        let err = string_value(r#""bad \q""#).unwrap_err();
        assert!(err.contains("unknown escape `\\q`"), "{err}");
    }

    fn lowered(source: &str) -> Lowered {
        let lowered = lower(source).expect("parses");
        assert!(lowered.errors.is_empty(), "{:?}", lowered.errors);
        lowered
    }

    fn tag_parts(e: &Expr) -> (&str, Option<&Expr>) {
        match &e.kind {
            ExprKind::Tag { name, payload, .. } => (name, payload.as_deref()),
            other => panic!("expected a tag, got {other:?}"),
        }
    }

    #[test]
    fn nullary_tag_has_no_payload() {
        for src in ["Empty", "Empty()"] {
            let root = lowered(src).root;
            let (name, payload) = tag_parts(&root);
            assert_eq!(name, "Empty");
            assert!(payload.is_none());
        }
    }

    #[test]
    fn single_argument_tag_carries_the_argument_as_its_payload() {
        let root = lowered("tag Circle Circle(5)").root;
        let (name, payload) = tag_parts(&root);
        assert_eq!(name, "Circle");
        assert!(matches!(payload.unwrap().kind, ExprKind::Int(5)));
    }

    #[test]
    fn multi_argument_tag_payload_is_a_positionally_labelled_record() {
        let root = lowered("x = 1 Link(x, Empty, 3)").root;
        let ExprKind::Let { rest, .. } = &root.kind else {
            panic!("expected a let");
        };
        let (name, payload) = tag_parts(rest.as_ref().unwrap());
        assert_eq!(name, "Link");
        let ExprKind::Record { fields } = &payload.unwrap().kind else {
            panic!("expected a record payload");
        };
        let labels: Vec<_> = fields.iter().map(|(l, _)| l.as_str()).collect();
        assert_eq!(labels, ["0", "1", "2"]);
        assert!(matches!(fields[0].1.kind, ExprKind::Var { .. }));
        assert!(matches!(fields[1].1.kind, ExprKind::Tag { .. }));
        assert!(matches!(fields[2].1.kind, ExprKind::Int(3)));
    }

    #[test]
    fn match_lowers_arms_binders_and_else() {
        let root = lowered(
            "tag Circle s = Empty match s do Link(a, b) then a Circle(r) then r Empty then 0 else 1 done",
        )
        .root;
        let ExprKind::Let { rest, .. } = &root.kind else {
            panic!("expected a let");
        };
        let ExprKind::Match {
            scrutinee,
            arms,
            else_branch,
        } = &rest.as_ref().unwrap().kind
        else {
            panic!("expected a match");
        };
        assert!(matches!(scrutinee.kind, ExprKind::Var { .. }));
        assert!(else_branch.is_some());
        assert_eq!(arms.len(), 3);

        let PatternPayload::Fields(fields) = &arms[0].pattern.payload else {
            panic!("two binders are positional fields");
        };
        let labelled: Vec<_> = fields
            .iter()
            .map(|(l, p)| (l.as_str(), p.name.as_str()))
            .collect();
        assert_eq!(labelled, [("0", "a"), ("1", "b")]);
        let ExprKind::Var { symbol, .. } = arms[0].body.kind else {
            panic!("arm body reads a binder");
        };
        assert_eq!(symbol, fields[0].1.symbol);

        assert!(matches!(&arms[1].pattern.payload, PatternPayload::Whole(p) if p.name == "r"));
        assert_eq!(arms[1].pattern.tag, "Circle");
        assert!(matches!(arms[2].pattern.payload, PatternPayload::None));
    }

    #[test]
    fn match_without_else_has_no_catch_all() {
        let root = lowered("match Empty do Empty then 0 done").root;
        let ExprKind::Match { else_branch, .. } = root.kind else {
            panic!("expected a match");
        };
        assert!(else_branch.is_none());
    }

    #[test]
    fn pattern_binders_are_scoped_to_their_arm() {
        let lowered =
            lower("tag Circle match Empty do Circle(r) then r Empty then r done").unwrap();
        assert_eq!(lowered.errors.len(), 1);
        assert!(lowered.errors[0].message.contains("unknown name `r`"));
    }

    fn link_parts(e: &Expr) -> (&Expr, &Expr) {
        let (name, payload) = tag_parts(e);
        assert_eq!(name, "Link");
        let ExprKind::Record { fields } = &payload.expect("Link has a payload").kind else {
            panic!("Link's payload is a record");
        };
        let labels: Vec<_> = fields.iter().map(|(l, _)| l.as_str()).collect();
        assert_eq!(labels, ["0", "1"]);
        (&fields[0].1, &fields[1].1)
    }

    #[test]
    fn the_empty_list_is_the_empty_tag() {
        let root = lowered("[]").root;
        let (name, payload) = tag_parts(&root);
        assert_eq!(name, "Empty");
        assert!(payload.is_none());
    }

    #[test]
    fn a_list_literal_nests_links_ending_in_empty() {
        let root = lowered("[1, 2, 3,]").root;
        let mut node = &root;
        for expected in [1, 2, 3] {
            let (item, tail) = link_parts(node);
            assert!(matches!(item.kind, ExprKind::Int(n) if n == expected));
            node = tail;
        }
        assert_eq!(tag_parts(node).0, "Empty");
    }

    #[test]
    fn list_literals_nest_and_mix_expressions() {
        let root = lowered("x = 1 [[x], [], x + 1]").root;
        let ExprKind::Let { rest, .. } = &root.kind else {
            panic!("expected a let");
        };
        let (first, tail) = link_parts(rest.as_ref().unwrap());
        let (inner, inner_tail) = link_parts(first);
        assert!(matches!(inner.kind, ExprKind::Var { .. }));
        assert_eq!(tag_parts(inner_tail).0, "Empty");
        let (second, tail) = link_parts(tail);
        assert_eq!(tag_parts(second).0, "Empty");
        let (third, _) = link_parts(tail);
        assert!(matches!(third.kind, ExprKind::Bin { .. }));
    }

    #[test]
    fn a_list_literal_spans_its_brackets() {
        let root = lowered("  [1, 2]").root;
        assert_eq!((root.span.start, root.span.end), (2, 8));
    }

    #[test]
    fn an_overlong_list_literal_is_a_clean_error() {
        let items = vec!["1"; MAX_DEPTH + 1].join(", ");
        let lowered = lower(&format!("[{items}]")).unwrap();
        assert_eq!(lowered.errors.len(), 1);
        assert!(lowered.errors[0].message.contains("too many items"));
    }

    fn arm_tags(root: &Expr) -> Vec<&str> {
        let ExprKind::Match { arms, .. } = &root.kind else {
            panic!("expected a match");
        };
        arms.iter().map(|a| a.pattern.tag.as_str()).collect()
    }

    #[test]
    fn the_standard_list_arms_are_a_match_on_empty_and_link() {
        let lowered = lowered("xs = [] match xs do [] then 0 [first, ...rest] then first + 1 done");
        assert!(lowered.errors.is_empty(), "{:?}", lowered.errors);
        let ExprKind::Let { rest, .. } = &lowered.root.kind else {
            panic!("expected a let");
        };
        let tree = rest.as_ref().unwrap();
        assert_eq!(arm_tags(tree), ["Empty", "Link"]);
        let ExprKind::Match {
            scrutinee, arms, ..
        } = &tree.kind
        else {
            unreachable!()
        };
        assert!(matches!(scrutinee.kind, ExprKind::Var { .. }));
        assert!(matches!(arms[0].pattern.payload, PatternPayload::None));
        let PatternPayload::Fields(fields) = &arms[1].pattern.payload else {
            panic!("Link binds its head and tail");
        };
        assert_eq!(fields.len(), 2);
    }

    #[test]
    fn a_fixed_length_pattern_checks_for_the_end_of_the_list() {
        let lowered = lowered("match [] do [a, b] then a done");
        assert!(lowered.errors.is_empty(), "{:?}", lowered.errors);
        let mut node = &lowered.root;
        for _ in 0..2 {
            assert_eq!(arm_tags(node), ["Link"]);
            let ExprKind::Match { arms, .. } = &node.kind else {
                unreachable!()
            };
            node = &arms[0].body;
        }
        assert_eq!(arm_tags(node), ["Empty"]);
    }

    #[test]
    fn a_shadowed_list_arm_is_an_error_and_is_still_checked() {
        let lowered = lower("match [] do [] then 0 [] then zzz done").unwrap();
        let messages: Vec<_> = lowered.errors.iter().map(|e| e.message.as_str()).collect();
        assert_eq!(messages.len(), 2, "{messages:?}");
        assert!(messages[0].contains("never matches"), "{messages:?}");
        assert!(messages[1].contains("unknown name `zzz`"), "{messages:?}");
    }

    #[test]
    fn an_arm_body_lowered_at_several_leaves_reports_its_mistakes_once() {
        let src = "match [] do [a, b] then 0 [a, ...r] then zzz [] then 1 done";
        let lowered = lower(src).unwrap();
        let unknown: Vec<_> = lowered
            .errors
            .iter()
            .filter(|e| e.message.contains("zzz"))
            .collect();
        assert_eq!(unknown.len(), 1, "{:?}", lowered.errors);
    }

    #[test]
    fn mixing_list_and_tag_patterns_is_an_error() {
        let lowered = lower("match [] do [] then 0 Link(a, b) then 1 done").unwrap();
        assert_eq!(lowered.errors.len(), 1);
        assert!(lowered.errors[0].message.contains("can't mix"));
    }

    #[test]
    fn duplicate_list_pattern_names_are_errors() {
        for src in [
            "match [] do [a, a] then a done",
            "match [] do [a, ...a] then a done",
            "[a, a] = [1, 2] a",
        ] {
            let lowered = lower(src).unwrap();
            assert!(
                lowered
                    .errors
                    .iter()
                    .any(|e| e.message.contains("duplicate binding `a`")),
                "{src}: {:?}",
                lowered.errors
            );
        }
    }

    #[test]
    fn list_pattern_names_are_scoped_to_their_arm() {
        let lowered = lower("match [] do [a] then 0 [] then a done").unwrap();
        assert!(
            lowered
                .errors
                .iter()
                .any(|e| e.message.contains("unknown name `a`")),
            "{:?}",
            lowered.errors
        );
    }

    #[test]
    fn a_destructured_list_binds_its_names_for_the_rest() {
        let lowered = lower("[a, ...r] = [1, 2] a + 1").unwrap();
        assert!(lowered.errors.is_empty(), "{:?}", lowered.errors);
    }

    #[test]
    fn duplicate_pattern_binder_is_an_error() {
        let lowered = lower("tag Pair match Empty do Pair(a, a) then a done").unwrap();
        assert_eq!(lowered.errors.len(), 1);
        assert!(lowered.errors[0].message.contains("duplicate binding `a`"));
    }
}
