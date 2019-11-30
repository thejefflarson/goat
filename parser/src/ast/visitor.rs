use crate::ast::Function;
use crate::ast::{Ast, Bool, Identifier};
use pest::Span;

#[macro_export]
macro_rules! visit_impl {
    ($self:ident, $ast:ident) => {
        match $ast {
            Ast::Empty => $self.visit_empty(),
            Ast::Number(n) => $self.visit_number(n),
            Ast::Str(s) => $self.visit_string(s),
            Ast::Identifier(i) => $self.visit_identifier(i),
            Ast::Program(p) => $self.visit_program(*p),
            Ast::Function(f) => $self.visit_function(f),
            Ast::Application {
                identifier: i,
                arguments: a,
            } => $self.visit_application(i, a),
            Ast::Conditional {
                condition: c,
                true_branch: t,
                else_branch: e,
            } => $self.visit_conditional(*c, *t, e),
            Ast::Declaration {
                identifier: i,
                body: b,
                rest: r,
            } => $self.visit_declaration(i, *b, r),
            Ast::Plus(lhs, rhs) => $self.visit_plus(*lhs, *rhs),
            Ast::Minus(lhs, rhs) => $self.visit_minus(*lhs, *rhs),
            Ast::Mult(lhs, rhs) => $self.visit_mult(*lhs, *rhs),
            Ast::Div(lhs, rhs) => $self.visit_div(*lhs, *rhs),
            Ast::Lte(lhs, rhs) => $self.visit_lte(*lhs, *rhs),
            Ast::Gte(lhs, rhs) => $self.visit_gte(*lhs, *rhs),
            Ast::Lt(lhs, rhs) => $self.visit_lt(*lhs, *rhs),
            Ast::Gt(lhs, rhs) => $self.visit_gt(*lhs, *rhs),
            Ast::Bool(b) => $self.visit_bool(b),
        }
    };
}

macro_rules! visit_op {
    ($name:ident) => {
        fn $name(&self, lhs: Ast, rhs: Ast) -> Self::Output;
    }
}

/// Visitors traverse an ast to build a single output.
pub trait Visitor {
    type Output;
    fn visit_empty(&self) -> Self::Output;

    fn visit_number(&self, number: Span) -> Self::Output;
    fn visit_string(&self, string: Span) -> Self::Output;
    fn visit_bool(&self, b: Bool) -> Self::Output;
    fn visit_identifier(&self, identifier: Identifier) -> Self::Output;
    fn visit_program(&self, ast: Ast) -> Self::Output;
    fn visit_function(&self, function: Function) -> Self::Output;
    // Labels are special. Implementors of this trait need to manually handle them in
    // `visit_function`
    fn visit_label(&self, label: Function) -> Self::Output;
    fn visit_application(&self, identifier: Identifier, arguments: Vec<Ast>) -> Self::Output;
    fn visit_conditional(
        &self,
        condition: Ast,
        true_branch: Ast,
        else_branch: Option<Box<Ast>>,
    ) -> Self::Output;
    fn visit_declaration(
        &self,
        identifier: Identifier,
        body: Ast,
        rest: Option<Box<Ast>>,
    ) -> Self::Output;

    visit_op!(visit_plus);
    visit_op!(visit_minus);
    visit_op!(visit_mult);
    visit_op!(visit_div);
    visit_op!(visit_lte);
    visit_op!(visit_gte);
    visit_op!(visit_lt);
    visit_op!(visit_gt);

    fn visit(&self, ast: Ast) -> Self::Output {
        visit_impl!(self, ast)
    }
}
