use crate::ast::*;
use pest::Span;

/// Folders transform an ast into a new tree.
pub trait Folder<'a> {
    fn visit_empty(&self) -> Ast<'a> {
        Ast::Empty
    }

    fn visit_number(&self, number: Span<'a>) -> Ast<'a> {
        Ast::Number(number.clone())
    }

    fn visit_string(&self, string: Span<'a>) -> Ast<'a> {
        Ast::Str(string.clone())
    }

    fn visit_identifier(&self, identifier: Identifier<'a>) -> Ast<'a> {
        Ast::Identifier(identifier.clone())
    }

    fn visit_bool(&self, b: Bool) -> Ast<'a> {
        Ast::Bool(b)
    }

    fn visit_program(&self, ast: Box<Ast<'a>>) -> Ast<'a> {
        Ast::Program(Box::new(self.visit(*ast)))
    }

    fn visit_function(&self, labels: Vec<Label<'a>>, program: Box<Ast<'a>>) -> Ast<'a> {
        let body = Box::new(Folder::visit_program(self, program));
        Ast::Function {
            labels: labels.clone(),
            body,
        }
    }

    fn visit_application(
        &self,
        identifier: Identifier<'a>,
        arguments: Vec<Box<Ast<'a>>>,
    ) -> Ast<'a> {
        let mut args: Vec<Box<Ast<'a>>> = vec![];
        for arg in arguments {
            args.push(Box::new(self.visit(*arg)))
        }

        Ast::Application {
            identifier: identifier.clone(),
            arguments: args,
        }
    }

    fn visit_conditional(
        &self,
        condition: Box<Ast<'a>>,
        true_branch: Box<Ast<'a>>,
        else_branch: Option<Box<Ast<'a>>>,
    ) -> Ast<'a> {
        Ast::Conditional {
            condition: Box::new(self.visit(*condition)),
            true_branch: Box::new(self.visit(*true_branch)),
            else_branch: else_branch.and_then(|x| Some(Box::new(self.visit(*x)))),
        }
    }

    fn visit_declaration(
        &self,
        identifier: Identifier<'a>,
        body: Box<Ast<'a>>,
        rest: Option<Box<Ast<'a>>>,
    ) -> Ast<'a> {
        Ast::Declaration {
            identifier: identifier.clone(),
            body: Box::new(self.visit(*body)),
            rest: rest.and_then(|x| Some(Box::new(self.visit(*x)))),
        }
    }

    fn visit_plus(&self, lhs: Box<Ast<'a>>, rhs: Box<Ast<'a>>) -> Ast<'a> {
        Ast::Plus(Box::new(self.visit(*lhs)), Box::new(self.visit(*rhs)))
    }

    fn visit_minus(&self, lhs: Box<Ast<'a>>, rhs: Box<Ast<'a>>) -> Ast<'a> {
        Ast::Minus(Box::new(self.visit(*lhs)), Box::new(self.visit(*rhs)))
    }

    fn visit_mult(&self, lhs: Box<Ast<'a>>, rhs: Box<Ast<'a>>) -> Ast<'a> {
        Ast::Mult(Box::new(self.visit(*lhs)), Box::new(self.visit(*rhs)))
    }

    fn visit_div(&self, lhs: Box<Ast<'a>>, rhs: Box<Ast<'a>>) -> Ast<'a> {
        Ast::Div(Box::new(self.visit(*lhs)), Box::new(self.visit(*rhs)))
    }

    fn visit_lte(&self, lhs: Box<Ast<'a>>, rhs: Box<Ast<'a>>) -> Ast<'a> {
        Ast::Lte(Box::new(self.visit(*lhs)), Box::new(self.visit(*rhs)))
    }

    fn visit_gte(&self, lhs: Box<Ast<'a>>, rhs: Box<Ast<'a>>) -> Ast<'a> {
        Ast::Gte(Box::new(self.visit(*lhs)), Box::new(self.visit(*rhs)))
    }

    fn visit_lt(&self, lhs: Box<Ast<'a>>, rhs: Box<Ast<'a>>) -> Ast<'a> {
        Ast::Lt(Box::new(self.visit(*lhs)), Box::new(self.visit(*rhs)))
    }

    fn visit_gt(&self, lhs: Box<Ast<'a>>, rhs: Box<Ast<'a>>) -> Ast<'a> {
        Ast::Gt(Box::new(self.visit(*lhs)), Box::new(self.visit(*rhs)))
    }

    fn visit(&self, ast: Ast<'a>) -> Ast<'a> {
        visit_impl!(self, ast)
    }
}
