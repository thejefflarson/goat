//! Lowering: the pest parse tree → the owned, name-resolved [`hir`].
//!
//! This pass does name resolution directly (assigning a fresh [`Symbol`] to
//! each binding and resolving each use to its binder), replacing the old
//! `Renamer`. It also parses literals to values and flattens the parse tree's
//! operator list into a precedence-correct expression tree.

use crate::error::GoatError;
use crate::hir::{BinOp, Expr, ExprId, ExprKind, Param, Span, Symbol};
use goat_parser::parser::{GoatParser, Rule};
use pest::iterators::Pair;
use pest::Parser;
use std::collections::HashMap;

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
        self.scopes
            .last_mut()
            .expect("a scope is always open while binding")
            .insert(name.to_string(), symbol);
        symbol
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

    /// Lower an `expr` pair — a flat `term (op term)*` list — into a
    /// precedence-correct tree.
    fn lower_expr(&mut self, pair: Pair<Rule>) -> Expr {
        let mut inner = pair.into_inner();
        let first = inner.next().expect("expr has at least one term");
        let mut operands = vec![self.lower_primary(first)];
        let mut ops: Vec<(BinOp, Span)> = Vec::new();

        while let Some(op_pair) = inner.next() {
            let op = bin_op(op_pair.as_rule());
            let op_span = span_of(&op_pair);
            let rhs_pair = inner.next().expect("an operator is followed by a term");
            let rhs = self.lower_primary(rhs_pair);

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
                let inner = &raw[1..raw.len() - 1];
                self.node(span, ExprKind::Str(inner.to_string()))
            }
            Rule::boolean => {
                let is_true = pair.as_str() == "true";
                self.node(span, ExprKind::Bool(is_true))
            }
            Rule::ident => {
                let name = pair.as_str().to_string();
                self.var(span, name)
            }
            Rule::declaration => self.lower_declaration(pair),
            Rule::function => self.lower_function(pair),
            Rule::application => self.lower_application(pair),
            Rule::conditional => self.lower_conditional(pair),
            other => unreachable!("unexpected term rule {other:?}"),
        }
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

        // Bind the name in a fresh scope before lowering the value, so a
        // declaration can refer to itself (recursion, e.g. `fib`).
        self.scopes.push(HashMap::new());
        let symbol = self.bind(&name);
        let value = self.lower_expr(value_pair);
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

    fn lower_application(&mut self, pair: Pair<Rule>) -> Expr {
        let span = span_of(&pair);
        let mut inner = pair.into_inner();
        let ident = inner.next().expect("application starts with a name");
        let callee = {
            let ispan = span_of(&ident);
            self.var(ispan, ident.as_str().to_string())
        };

        // Each `arguments` child is one call group: `f(a)(b)` nests as
        // `(f(a))(b)`. A group with no arguments produces no `arguments` pair.
        let mut groups: Vec<Vec<Expr>> = Vec::new();
        for args_pair in inner {
            debug_assert_eq!(args_pair.as_rule(), Rule::arguments);
            let args = args_pair.into_inner().map(|p| self.lower_expr(p)).collect();
            groups.push(args);
        }
        // The grammar guarantees at least one `(...)` group, but a single empty
        // group leaves `groups` empty; model that as one call with no args.
        if groups.is_empty() {
            groups.push(Vec::new());
        }

        let mut expr = callee;
        for args in groups {
            expr = self.node(
                span,
                ExprKind::App {
                    callee: Box::new(expr),
                    args,
                },
            );
        }
        expr
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
