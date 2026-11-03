//! Evaluation-order check for value bindings (ADR 0003).
//!
//! Functions in a scope are an order-free group, so a function can name a
//! value binding that is defined above the function yet still unbound when the
//! function runs: the group is callable from code that comes before the value.
//! Name resolution cannot see that, so this pass walks each scope in
//! evaluation order and rejects a use of a function, as a call or as a value,
//! while a value it captures is still unbound.

use crate::captures::{Target, for_each_child};
use crate::error::GoatError;
use crate::hir::{Expr, ExprKind, Symbol};
use std::collections::HashMap;

pub fn check(root: &Expr, captures: &HashMap<Target, Vec<Symbol>>) -> Vec<GoatError> {
    let mut order = Order {
        captures,
        unbound: HashMap::new(),
        errors: Vec::new(),
    };
    order.expr(root);
    order.errors
}

struct Order<'a> {
    captures: &'a HashMap<Target, Vec<Symbol>>,
    /// Value bindings of the scopes being evaluated whose binding point has not
    /// run yet, with their names.
    unbound: HashMap<Symbol, &'a str>,
    errors: Vec<GoatError>,
}

impl<'a> Order<'a> {
    fn expr(&mut self, e: &'a Expr) {
        match &e.kind {
            ExprKind::Let { .. } => self.declarations(e),
            ExprKind::Func { body, .. } => {
                self.function_use(Target::Anon(e.id), e, "this program");
                self.body(body);
            }
            ExprKind::Var { symbol, name } => {
                self.function_use(Target::Named(*symbol), e, &format!("`{name}`"));
            }
            _ => for_each_child(e, &mut |c| self.expr(c)),
        }
    }

    /// A run of declarations: every value in it starts unbound and is bound
    /// as its declaration is evaluated, top to bottom.
    fn declarations(&mut self, first: &'a Expr) {
        let mut declared = Vec::new();
        let mut tail = Some(first);
        while let Some(e) = tail {
            let ExprKind::Let {
                symbol,
                name,
                value,
                rest,
            } = &e.kind
            else {
                break;
            };
            if !matches!(value.kind, ExprKind::Func { .. }) {
                self.unbound.insert(*symbol, name);
            }
            declared.push((e, *symbol, name, value, rest));
            tail = rest.as_deref();
        }

        for (e, symbol, name, value, rest) in declared {
            match &value.kind {
                ExprKind::Func { body, .. } => {
                    if rest.is_none() {
                        self.function_use(Target::Named(symbol), e, &format!("`{name}`"));
                    }
                    self.body(body);
                }
                _ => {
                    self.expr(value);
                    self.unbound.remove(&symbol);
                }
            }
        }
        if let Some(tail) = tail {
            self.expr(tail);
        }
    }

    /// A function body runs only when called, with everything it captures
    /// bound, so it starts a fresh scope; a use of the function is what is
    /// checked.
    fn body(&mut self, body: &'a Expr) {
        let outer = std::mem::take(&mut self.unbound);
        self.expr(body);
        self.unbound = outer;
    }

    fn function_use(&mut self, target: Target, at: &Expr, what: &str) {
        let Some(captures) = self.captures.get(&target) else {
            return;
        };
        if let Some(missing) = captures.iter().find_map(|c| self.unbound.get(c)) {
            self.errors.push(GoatError::new(
                at.span,
                format!("{what} uses `{missing}` before it is defined"),
            ));
        }
    }
}
