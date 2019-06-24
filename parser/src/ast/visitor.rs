use crate::ast::{Ast, Bool, Identifier, Label};
use pest::Span;

#[macro_export]
macro_rules! visit_impl {
    ($self:ident, $ast:ident) => {
        match $ast {
            Ast::Empty => $self.visit_empty(),
            Ast::Number(n) => $self.visit_number(n),
            Ast::Str(s) => $self.visit_string(s),
            Ast::Identifier(i) => $self.visit_identifier(i),
            Ast::Program(p) => $self.visit_program(p),
            Ast::Function { labels: l, body: p } => $self.visit_function(l, p),
            Ast::Application {
                identifier: i,
                arguments: a,
            } => $self.visit_application(i, a),
            Ast::Conditional {
                condition: c,
                true_branch: t,
                else_branch: e,
            } => $self.visit_conditional(c, t, e),
            Ast::Declaration {
                identifier: i,
                body: b,
                rest: r,
            } => $self.visit_declaration(i, b, r),
            Ast::Plus(lhs, rhs) => $self.visit_plus(lhs, rhs),
            Ast::Minus(lhs, rhs) => $self.visit_minus(lhs, rhs),
            Ast::Mult(lhs, rhs) => $self.visit_mult(lhs, rhs),
            Ast::Div(lhs, rhs) => $self.visit_div(lhs, rhs),
            Ast::Lte(lhs, rhs) => $self.visit_lte(lhs, rhs),
            Ast::Gte(lhs, rhs) => $self.visit_gte(lhs, rhs),
            Ast::Lt(lhs, rhs) => $self.visit_lt(lhs, rhs),
            Ast::Gt(lhs, rhs) => $self.visit_gt(lhs, rhs),
            Ast::Bool(b) => $self.visit_bool(b),
        }
    };
}

/// Visitors traverse an ast to build a single output.
pub trait Visitor {
    type Output;
    fn visit_empty(&self) -> Self::Output;
    fn visit_number(&self, number: Span) -> Self::Output;
    fn visit_string(&self, string: Span) -> Self::Output;
    fn visit_bool(&self, b: Bool) -> Self::Output;
    fn visit_identifier(&self, identifier: Identifier) -> Self::Output;
    fn visit_program(&self, ast: Box<Ast>) -> Self::Output;
    fn visit_function(&self, labels: Vec<Label>, program: Box<Ast>) -> Self::Output;
    fn visit_application(&self, identifier: Identifier, arguments: Vec<Box<Ast>>) -> Self::Output;
    fn visit_conditional(
        &self,
        condition: Box<Ast>,
        true_branch: Box<Ast>,
        else_branch: Option<Box<Ast>>,
    ) -> Self::Output;
    fn visit_declaration(
        &self,
        identifier: Identifier,
        body: Box<Ast>,
        rest: Option<Box<Ast>>,
    ) -> Self::Output;
    fn visit_plus(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    fn visit_minus(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    fn visit_mult(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    fn visit_div(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    fn visit_lte(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    fn visit_gte(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    fn visit_lt(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    fn visit_gt(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    fn visit(&self, ast: Ast) -> Self::Output {
        visit_impl!(self, ast)
    }
}
