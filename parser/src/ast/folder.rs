use crate::ast::Label;
use crate::ast::{Ast, Bool, Function, Identifier};
use pest::Span;

macro_rules! fold_op {
    ($name:ident, $enum:ident) => {
        fn $name(&self, lhs: Ast<'a>, rhs: Ast<'a>) -> Ast<'a> {
            Ast::$enum(Box::new(self.visit(lhs)), Box::new(self.visit(rhs)))
        }
    }
}

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

    fn visit_program(&self, ast: Ast<'a>) -> Ast<'a> {
        Ast::Program(Box::new(self.visit(ast)))
    }

    fn visit_label(&self, label: Label<'a>) -> Label<'a> {
        label.clone()
    }

    fn visit_function(&self, function: Function<'a>) -> Ast<'a> {
        let body = function
            .body
            .map(|body| Box::new(Folder::visit(self, *body)));
        let labels = function.labels.map(|labels| {
            labels
                .into_iter()
                .map(|label| Folder::visit_label(self, label))
                .collect()
        });
        Ast::Function(Function::new(labels, body))
    }

    fn visit_application(&self, identifier: Identifier<'a>, arguments: Vec<Ast<'a>>) -> Ast<'a> {
        let mut args: Vec<Ast<'a>> = vec![];
        for arg in arguments {
            args.push(self.visit(arg))
        }

        Ast::Application {
            identifier: identifier.clone(),
            arguments: args,
        }
    }

    fn visit_conditional(
        &self,
        condition: Ast<'a>,
        true_branch: Ast<'a>,
        else_branch: Option<Box<Ast<'a>>>,
    ) -> Ast<'a> {
        Ast::Conditional {
            condition: Box::new(self.visit(condition)),
            true_branch: Box::new(self.visit(true_branch)),
            else_branch: else_branch.and_then(|x| Some(Box::new(self.visit(*x)))),
        }
    }

    fn visit_declaration(
        &self,
        identifier: Identifier<'a>,
        body: Ast<'a>,
        rest: Option<Box<Ast<'a>>>,
    ) -> Ast<'a> {
        Ast::Declaration {
            identifier: identifier.clone(),
            body: Box::new(self.visit(body)),
            rest: rest.and_then(|x| Some(Box::new(self.visit(*x)))),
        }
    }

    fold_op!(visit_plus, Plus);
    fold_op!(visit_minus, Minus);
    fold_op!(visit_mult, Mult);
    fold_op!(visit_div, Div);
    fold_op!(visit_lte, Lte);
    fold_op!(visit_gte, Gte);
    fold_op!(visit_lt, Lt);
    fold_op!(visit_gt, Gt);

    fn visit(&self, ast: Ast<'a>) -> Ast<'a> {
        visit_impl!(self, ast)
    }
}
