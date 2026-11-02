//! Lowering: the pest parse tree → the owned, name-resolved [`hir`].
//!
//! This pass does name resolution directly (assigning a fresh [`Symbol`] to
//! each binding and resolving each use to its binder), replacing the old
//! `Renamer`. It also parses literals to values and flattens the parse tree's
//! operator list into a precedence-correct expression tree.

use crate::error::GoatError;
use crate::hir::{BinOp, Expr, ExprId, ExprKind, Param, Span, Symbol};
use goat_parser::parser::{GoatParser, Rule};
use pest::Parser;
use pest::iterators::{Pair, Pairs};
use std::collections::{HashMap, HashSet};
use std::iter::Peekable;

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
            Rule::function => self.lower_function(pair),
            Rule::conditional => self.lower_conditional(pair),
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
        let mut body = None;
        for child in pair.into_inner() {
            match child.as_rule() {
                Rule::labels => {
                    for label in child.into_inner() {
                        let pspan = span_of(&label);
                        let name = label.as_str().to_string();
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

        let body = body.unwrap_or_else(|| self.node(span, ExprKind::Unit));
        self.node(
            span,
            ExprKind::Func {
                params,
                body: Box::new(body),
            },
        )
    }

    fn lower_record(&mut self, pair: Pair<Rule>) -> Expr {
        let span = span_of(&pair);
        let mut fields = Vec::new();
        for field in pair.into_inner() {
            debug_assert_eq!(field.as_rule(), Rule::field);
            let mut it = field.into_inner();
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
        self.node(span, ExprKind::Record { fields })
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
}
