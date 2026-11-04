//! Lowering: the pest parse tree → the owned, name-resolved [`hir`].
//!
//! This pass does name resolution directly (assigning a fresh [`Symbol`] to
//! each binding and resolving each use to its binder), replacing the old
//! `Renamer`. It also parses literals to values and flattens the parse tree's
//! operator list into a precedence-correct expression tree.

use crate::error::GoatError;
use crate::hir::{
    BinOp, Expr, ExprId, ExprKind, MatchArm, Param, Pattern, PatternPayload, Span, Symbol,
};
use goat_parser::parser::{GoatParser, Rule};
use pest::Parser;
use pest::iterators::{Pair, Pairs};
use std::collections::{HashMap, HashSet};
use std::iter::Peekable;

/// Deepest expression tree lowering accepts; deeper input would overflow the
/// recursive passes (inference, codegen) that walk the tree.
// Kept well below the depth at which recursive inference/codegen overflows a
// small (2 MB) thread stack, so any expression the checker accepts is safe to
// walk. No real program nests this deep; pathological input gets a clean error.
const MAX_DEPTH: usize = 256;

pub struct Lowered {
    pub root: Expr,
    pub errors: Vec<GoatError>,
}

/// Parse and lower `source`. Parse errors abort (returned as the sole error);
/// name-resolution errors are collected so the inferer can still run and report
/// type errors in the same pass.
pub fn lower(source: &str) -> Result<Lowered, GoatError> {
    let mut pairs = GoatParser::parse(Rule::goat, source)
        .map_err(|e| GoatError::new(Span::new(0, 0), format!("parse error:\n{e}")))?;
    let goat = pairs.next().expect("goat rule always produces one pair");

    let mut ctx = Lower::default();
    let root = ctx.lower_goat(goat);
    Ok(Lowered {
        root,
        errors: ctx.errors,
    })
}

/// The names a `{x, y, ...rest}` pattern binds: `(symbol, name, span)` each.
struct RecordPattern {
    fields: Vec<(Symbol, String, Span)>,
    rest: Option<(Symbol, String, Span)>,
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
    depth: usize,
}

impl Lower {
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
        let span = span_of(&pair);
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
        let added = pair.clone().into_inner().count() / 2 + 1;
        if self.depth + added > MAX_DEPTH {
            let span = pair
                .clone()
                .into_inner()
                .next()
                .map_or_else(|| span_of(&pair), |first| span_of(&first));
            self.errors
                .push(GoatError::new(span, "expression nested too deeply"));
            return self.node(span, ExprKind::Unit);
        }
        self.depth += added;
        let expr = self.lower_expr_chain(pair);
        self.depth -= added;
        expr
    }

    fn lower_expr_chain(&mut self, pair: Pair<Rule>) -> Expr {
        let mut inner = pair.into_inner().peekable();
        let mut operands = vec![self.lower_operand(&mut inner)];
        let mut ops: Vec<(BinOp, Span)> = Vec::new();

        while let Some(op_pair) = inner.next() {
            let op = bin_op(op_pair.as_rule());
            let op_span = span_of(&op_pair);
            let rhs = self.lower_operand(&mut inner);

            while let Some((top, _)) = ops.last() {
                if prec(*top) >= prec(op) {
                    self.reduce(&mut operands, &mut ops);
                } else {
                    break;
                }
            }
            ops.push((op, op_span));
            operands.push(rhs);
        }

        while !ops.is_empty() {
            self.reduce(&mut operands, &mut ops);
        }
        operands.pop().expect("exactly one operand remains")
    }

    fn lower_operand(&mut self, inner: &mut Peekable<Pairs<Rule>>) -> Expr {
        let first = inner.next().expect("an operand begins with a primary");
        if first.as_rule() == Rule::negation {
            return self.lower_negation(first);
        }
        let expr = self.lower_primary(first);
        self.lower_postfixes(expr, inner)
    }

    /// `a.b(x).c` nests as `((a.b)(x)).c`.
    fn lower_postfixes(&mut self, mut expr: Expr, inner: &mut Peekable<Pairs<Rule>>) -> Expr {
        while let Some(postfix) =
            inner.next_if(|p| matches!(p.as_rule(), Rule::access | Rule::call))
        {
            let span = Span::new(expr.span.start, span_of(&postfix).end);
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
                    let args = postfix
                        .into_inner()
                        .flat_map(|a| a.into_inner())
                        .map(|a| self.lower_expr(a))
                        .collect();
                    self.node(
                        span,
                        ExprKind::App {
                            callee: Box::new(expr),
                            args,
                        },
                    )
                }
            };
        }
        expr
    }

    /// `-x` is `0 - x`: the HIR has no negation node.
    fn lower_negation(&mut self, pair: Pair<Rule>) -> Expr {
        let span = span_of(&pair);
        let mut inner = pair.into_inner().peekable();
        let minus = inner.next().expect("negation begins with `-`");
        let operand = self.lower_operand(&mut inner);
        let zero = self.node(span_of(&minus), ExprKind::Number(0.0));
        self.node(
            span,
            ExprKind::Bin {
                op: BinOp::Sub,
                lhs: Box::new(zero),
                rhs: Box::new(operand),
            },
        )
    }

    /// Fold the top operator and its two operands into one `Bin` node.
    fn reduce(&mut self, operands: &mut Vec<Expr>, ops: &mut Vec<(BinOp, Span)>) {
        let (op, _) = ops.pop().expect("reduce called with an operator");
        let rhs = operands.pop().expect("binary operator has a right operand");
        let lhs = operands.pop().expect("binary operator has a left operand");
        let span = Span::new(lhs.span.start, rhs.span.end);
        let node = self.node(
            span,
            ExprKind::Bin {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
        );
        operands.push(node);
    }

    /// Lower a single term (anything that can appear as an operand).
    fn lower_primary(&mut self, pair: Pair<Rule>) -> Expr {
        let span = span_of(&pair);
        match pair.as_rule() {
            Rule::expr => self.lower_expr(pair),
            Rule::number => {
                let text = pair.as_str().trim_end_matches('.');
                match text.parse::<f64>() {
                    Ok(n) => self.node(span, ExprKind::Number(n)),
                    Err(_) => {
                        self.errors
                            .push(GoatError::new(span, format!("invalid number `{text}`")));
                        self.node(span, ExprKind::Number(0.0))
                    }
                }
            }
            Rule::string => {
                let raw = pair.as_str();
                let decoded = self.decode_string(span, &raw[1..raw.len() - 1]);
                self.node(span, ExprKind::Str(decoded))
            }
            Rule::boolean => {
                let is_true = pair.as_str() == "true";
                self.node(span, ExprKind::Bool(is_true))
            }
            Rule::ident => {
                let name = pair.as_str().to_string();
                self.var(span, name)
            }
            Rule::record => self.lower_record(pair),
            Rule::declaration => self.lower_declaration(pair),
            Rule::destructure => self.lower_destructure(pair),
            Rule::function => self.lower_function(pair),
            Rule::conditional => self.lower_conditional(pair),
            Rule::tag => self.lower_tag(pair),
            Rule::match_expr => self.lower_match(pair),
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

    fn var(&mut self, span: Span, name: String) -> Expr {
        let symbol = self.resolve(&name).unwrap_or_else(|| {
            self.errors
                .push(GoatError::new(span, format!("unknown name `{name}`")));
            self.fresh_symbol()
        });
        self.node(span, ExprKind::Var { symbol, name })
    }

    fn lower_declaration(&mut self, pair: Pair<Rule>) -> Expr {
        let span = span_of(&pair);
        let mut inner = pair.into_inner();
        let name_pair = inner.next().expect("declaration starts with a name");
        let name = name_pair.as_str().to_string();
        let value_pair = inner.next().expect("declaration has a value");
        let rest_pair = inner.next();

        self.scopes.push(HashMap::new());
        let (symbol, value) = if is_program_literal(&value_pair) {
            let start = span_of(&name_pair).start;
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
            let value = self.lower_expr(value_pair);
            (self.bind(&name), value)
        };
        let rest = rest_pair.map(|p| self.lower_expr(p));
        self.scopes.pop();

        self.node(
            span,
            ExprKind::Let {
                symbol,
                name,
                value: Box::new(value),
                rest: rest.map(Box::new),
            },
        )
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
            if decl.as_rule() != Rule::declaration {
                break;
            }
            let mut parts = decl.into_inner();
            let name_pair = parts.next().expect("declaration starts with a name");
            let value = parts.next().expect("declaration has a value");
            rest = parts.next();
            if is_program_literal(&value) {
                self.reserve(&name_pair, &mut seen);
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
        self.grouped.insert(span_of(name_pair).start, reserved);
    }

    fn lower_function(&mut self, pair: Pair<Rule>) -> Expr {
        let span = span_of(&pair);
        self.scopes.push(HashMap::new());
        let mut params = Vec::new();
        let mut unpacked = Vec::new();
        let mut body = None;
        for child in pair.into_inner() {
            match child.as_rule() {
                Rule::params => {
                    for param in child.into_inner() {
                        let pspan = span_of(&param);
                        let name = param.as_str().to_string();
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
                Rule::expr => body = Some(self.lower_expr(child)),
                other => unreachable!("unexpected function child {other:?}"),
            }
        }
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
            let span = span_of(&name_pair);
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
        let span = span_of(&pair);
        let mut inner = pair.into_inner();
        let pattern_pair = inner.next().expect("destructuring begins with a pattern");
        let value_pair = inner.next().expect("destructuring has a value");
        let rest_pair = inner.next();
        let source_name = pattern_pair.as_str().to_string();

        let value = self.lower_expr(value_pair);
        self.scopes.push(HashMap::new());
        let source = self.fresh_symbol();
        let pattern = self.bind_record_pattern(pattern_pair, "name");
        let rest = rest_pair.map(|p| self.lower_expr(p));
        self.scopes.pop();

        let unpacked = self.unpack(source, &source_name, pattern, rest);
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
        let span = span_of(&pair);
        let mut base = None;
        let mut spreads = 0;
        let mut fields = Vec::new();
        for (position, item) in pair.into_inner().enumerate() {
            if item.as_rule() == Rule::spread {
                let item_span = span_of(&item);
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
            let label_span = span_of(&label_pair);
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

    fn lower_tag(&mut self, pair: Pair<Rule>) -> Expr {
        let span = span_of(&pair);
        let mut inner = pair.into_inner();
        let name = inner
            .next()
            .expect("a tag begins with its name")
            .as_str()
            .to_string();
        let mut args: Vec<Expr> = inner
            .flat_map(|arguments| arguments.into_inner())
            .map(|a| self.lower_expr(a))
            .collect();
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
        self.node(
            span,
            ExprKind::Tag {
                name,
                payload: payload.map(Box::new),
            },
        )
    }

    fn lower_match(&mut self, pair: Pair<Rule>) -> Expr {
        let span = span_of(&pair);
        let mut inner = pair.into_inner();
        let scrutinee = self.lower_expr(inner.next().expect("match has a scrutinee"));
        let mut arms = Vec::new();
        let mut else_branch = None;
        for child in inner {
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
        let span = span_of(&pair);
        let mut inner = pair.into_inner();
        let tag = inner
            .next()
            .expect("a pattern begins with a tag name")
            .as_str()
            .to_string();
        let mut binders: Vec<Param> = Vec::new();
        for label in inner.flat_map(|labels| labels.into_inner()) {
            let pspan = span_of(&label);
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

    fn lower_conditional(&mut self, pair: Pair<Rule>) -> Expr {
        let span = span_of(&pair);
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
}

fn is_program_literal(expr: &Pair<Rule>) -> bool {
    let mut kids = expr.clone().into_inner();
    matches!((kids.next(), kids.next()), (Some(p), None) if p.as_rule() == Rule::function)
}

fn span_of(pair: &Pair<Rule>) -> Span {
    let s = pair.as_span();
    Span::new(s.start(), s.end())
}

fn bin_op(rule: Rule) -> BinOp {
    match rule {
        Rule::plus => BinOp::Add,
        Rule::minus => BinOp::Sub,
        Rule::multiply => BinOp::Mul,
        Rule::divide => BinOp::Div,
        Rule::lt => BinOp::Lt,
        Rule::lte => BinOp::Lte,
        Rule::gt => BinOp::Gt,
        Rule::gte => BinOp::Gte,
        other => unreachable!("not an operator rule: {other:?}"),
    }
}

fn prec(op: BinOp) -> u8 {
    match op {
        BinOp::Mul | BinOp::Div => 3,
        BinOp::Add | BinOp::Sub => 2,
        BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte => 1,
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
            ExprKind::Tag { name, payload } => (name, payload.as_deref()),
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
        let root = lowered("Circle(5)").root;
        let (name, payload) = tag_parts(&root);
        assert_eq!(name, "Circle");
        assert!(matches!(payload.unwrap().kind, ExprKind::Number(n) if n == 5.0));
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
        assert!(matches!(fields[2].1.kind, ExprKind::Number(_)));
    }

    #[test]
    fn match_lowers_arms_binders_and_else() {
        let root = lowered(
            "s = Empty match s do Link(a, b) then a Circle(r) then r Empty then 0 else 1 done",
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
        let lowered = lower("match Empty do Circle(r) then r Empty then r done").unwrap();
        assert_eq!(lowered.errors.len(), 1);
        assert!(lowered.errors[0].message.contains("unknown name `r`"));
    }

    #[test]
    fn duplicate_pattern_binder_is_an_error() {
        let lowered = lower("match Empty do Pair(a, a) then a done").unwrap();
        assert_eq!(lowered.errors.len(), 1);
        assert!(lowered.errors[0].message.contains("duplicate binding `a`"));
    }
}
