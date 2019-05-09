use parser::*;
use pest::iterators::Pair;
use pest::prec_climber::{Assoc, Operator, PrecClimber};
use pest::Span;

#[derive(Hash, Eq, PartialEq, Debug, Clone)]
pub struct Identifier<'a> {
    name: Span<'a>,
    internal: String,
}

impl<'a> Identifier<'a> {
    fn new(name: Span<'a>) -> Self {
        Identifier {
            name: name.clone(),
            internal: String::from(name.as_str()),
        }
    }

    fn rename(&mut self, name: String) {
        self.internal = name;
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Label<'a> {
    identifier: Identifier<'a>,
}

impl<'a> Label<'a> {
    fn new(identifier: Identifier<'a>) -> Self {
        Label { identifier }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Ast<'a> {
    Empty,
    Number(Span<'a>),
    Identifier(Identifier<'a>),
    Str(Span<'a>),
    Program(Box<Ast<'a>>),
    Function {
        labels: Vec<Label<'a>>,
        body: Box<Ast<'a>>,
    },
    Application {
        identifier: Identifier<'a>,
        arguments: Vec<Box<Ast<'a>>>,
    },
    Conditional {
        condition: Box<Ast<'a>>,
        true_branch: Box<Ast<'a>>,
        else_branch: Option<Box<Ast<'a>>>,
    },
    Plus(Box<Ast<'a>>, Box<Ast<'a>>),
    Minus(Box<Ast<'a>>, Box<Ast<'a>>),
    Mult(Box<Ast<'a>>, Box<Ast<'a>>),
    Div(Box<Ast<'a>>, Box<Ast<'a>>),
    Lte(Box<Ast<'a>>, Box<Ast<'a>>),
    Gte(Box<Ast<'a>>, Box<Ast<'a>>),
    Lt(Box<Ast<'a>>, Box<Ast<'a>>),
    Gt(Box<Ast<'a>>, Box<Ast<'a>>),
    Declaration {
        identifier: Identifier<'a>,
        body: Box<Ast<'a>>,
        rest: Option<Box<Ast<'a>>>,
    },
}

fn child<'a>(pair: Pair<'a, Rule>) -> Ast<'a> {
    match pair.as_rule() {
        Rule::goat => {
            let inner = pair.into_inner().next();
            let node = match inner {
                None => Ast::Empty,
                Some(pair) => Ast::new(pair),
            };
            Ast::Program(Box::new(node))
        }
        Rule::string => Ast::Str(pair.as_span()),
        Rule::number => Ast::Number(pair.as_span()),
        Rule::ident => Ast::Identifier(Identifier::new(pair.as_span())),
        Rule::function => {
            let mut inner = pair.into_inner();
            let labels = inner.next().unwrap().into_inner();
            let block = inner.next().unwrap();
            Ast::Function {
                labels: labels
                    .map(|label| Label::new(Identifier::new(label.as_span())))
                    .collect(),
                body: Box::new(Ast::new(block)),
            }
        }
        Rule::application => {
            let mut inner = pair.into_inner();
            let ident = inner.next().unwrap();
            let arguments = inner.map(|it| Box::new(Ast::new(it))).collect();
            Ast::Application {
                identifier: Identifier::new(ident.as_span()),
                arguments,
            }
        }
        Rule::conditional => {
            let mut inner = pair.into_inner();
            let cond = Ast::new(inner.next().unwrap());
            let then = Ast::new(inner.next().unwrap());
            let else_branch = inner.next().map(|i| Box::new(Ast::new(i)));
            Ast::Conditional {
                condition: Box::new(cond),
                true_branch: Box::new(then),
                else_branch,
            }
        }
        Rule::expr => {
            let climber = PrecClimber::new(vec![
                Operator::new(Rule::lt, Assoc::Left)
                    | Operator::new(Rule::lte, Assoc::Left)
                    | Operator::new(Rule::gt, Assoc::Left)
                    | Operator::new(Rule::gte, Assoc::Left),
                Operator::new(Rule::plus, Assoc::Left) | Operator::new(Rule::minus, Assoc::Left),
                Operator::new(Rule::multiply, Assoc::Left)
                    | Operator::new(Rule::divide, Assoc::Left),
            ]);

            let infix = |lhs: Ast<'a>, op: Pair<'a, Rule>, rhs: Ast<'a>| match op.as_rule() {
                Rule::plus => Ast::Plus(Box::new(lhs), Box::new(rhs)),
                Rule::minus => Ast::Minus(Box::new(lhs), Box::new(rhs)),
                Rule::multiply => Ast::Mult(Box::new(lhs), Box::new(rhs)),
                Rule::divide => Ast::Div(Box::new(lhs), Box::new(rhs)),
                Rule::lte => Ast::Lte(Box::new(lhs), Box::new(rhs)),
                Rule::lt => Ast::Lt(Box::new(lhs), Box::new(rhs)),
                Rule::gte => Ast::Gte(Box::new(lhs), Box::new(rhs)),
                Rule::gt => Ast::Gt(Box::new(lhs), Box::new(rhs)),

                _ => unreachable!(),
            };
            climber.climb(pair.into_inner(), Ast::new, infix)
        }
        Rule::EOI => Ast::Empty,
        _ => unimplemented!(),
    }
}

impl<'i> Ast<'i> {
    fn new<'a: 'i>(pair: Pair<'a, Rule>) -> Self {
        child(pair)
    }
}

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
        }
    };
}

/// Visitors traverse an ast to build a single output.
pub trait Visitor {
    type Output;
    fn visit_empty(&self) -> Self::Output;
    fn visit_number(&self, number: Span) -> Self::Output;
    fn visit_string(&self, string: Span) -> Self::Output;
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

    fn visit_program(&self, ast: Box<Ast<'a>>) -> Ast<'a> {
        self.visit(*ast)
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

struct Env {}
const ALPHA: &str = "abcdefghijklmnopqrstuvwxyz";
struct Rewriter {
    last: usize,
}
impl Rewriter {
    fn new() -> Self {
        Rewriter { last: 0 }
    }

    fn next(&mut self) -> String {
        if self.last == 0 {
            self.last += 1;
            return "a".to_string();
        }
        let mut accum = "".to_string();
        let mut current = self.last;
        while current > 0 {
            let idx = current % ALPHA.len();
            accum.push(ALPHA.chars().nth(idx).unwrap());
            current /= ALPHA.len()
        }
        self.last += 1;
        accum
    }
}

impl<'a> Folder<'a> for Rewriter {}

#[cfg(test)]
mod tests {
    use super::*;
    use pest::Parser;

    #[test]
    fn converts_empty() {
        let pairs = GoatParser::parse(Rule::goat, "").unwrap().nth(0).unwrap();
        println!("{:x?}", pairs.clone());
        let ast = Ast::new(pairs);
        assert_eq!(ast, Ast::Program(Box::new(Ast::Empty)));
    }

    #[test]
    fn converts_number() {
        let prog = "1";
        let pairs = GoatParser::parse(Rule::goat, prog).unwrap().nth(0).unwrap();
        println!("{:#?}", pairs.clone());
        let ast = Ast::new(pairs);
        let span = GoatParser::parse(Rule::number, prog)
            .unwrap()
            .nth(0)
            .unwrap()
            .as_span();
        assert_eq!(ast, Ast::Program(Box::new(Ast::Number(span))))
    }

    #[test]
    fn converts_function() {
        let pairs = GoatParser::parse(Rule::goat, "program(a, b) do a done")
            .unwrap()
            .nth(0)
            .unwrap();
        let ast = Ast::new(pairs);
        println!("{:#?}", ast)
    }

    #[test]
    fn converts_math() {
        let pairs = GoatParser::parse(Rule::goat, "1 + 1")
            .unwrap()
            .nth(0)
            .unwrap();
        let ast = Ast::new(pairs);
        println!("{:#?}", ast)
    }
}
