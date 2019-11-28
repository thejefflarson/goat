pub mod renamer;
#[macro_use]
pub mod visitor;
pub mod folder;

pub use self::folder::Folder;
pub use self::renamer::Renamer;
pub use self::visitor::Visitor;

use crate::parser::*;
use pest::iterators::Pair;
use pest::prec_climber::{Assoc, Operator, PrecClimber};
use pest::Span;

#[derive(Hash, Eq, PartialEq, Debug, Clone)]
pub struct Identifier<'a> {
    name: Span<'a>,
    internal: String,
}

impl<'a> Identifier<'a> {
    pub(super) fn new(name: Span<'a>) -> Self {
        Identifier {
            name: name.clone(),
            internal: String::from(name.as_str()),
        }
    }

    pub(super) fn rename(&self, name: String) -> Self {
        Identifier {
            name: self.name.clone(),
            internal: name,
        }
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
pub enum Bool {
    True,
    False,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Ast<'a> {
    Empty,
    Number(Span<'a>),
    Identifier(Identifier<'a>),
    Str(Span<'a>),
    Bool(Bool),
    Program(Box<Ast<'a>>),
    Function {
        labels: Vec<Label<'a>>,
        body: Box<Ast<'a>>,
    },
    Application {
        identifier: Identifier<'a>,
        arguments: Vec<Ast<'a>>,
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
        Rule::boolean => child(pair.into_inner().nth(0).unwrap()),
        Rule::true_lit => Ast::Bool(Bool::True),
        Rule::false_lit => Ast::Bool(Bool::False),
        Rule::function => {
            let t = pair.clone();
            let mut inner = pair.into_inner();
            println!("{:?}", t);
            let labels = inner.next().unwrap().into_inner();
            println!("{:?}", labels);
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
            let arguments = inner.map(Ast::new).collect();
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
        _ => panic!("Couldn't build {:?}", message = pair),
    }
}

impl<'i> Ast<'i> {
    pub fn new<'a: 'i>(pair: Pair<'a, Rule>) -> Self {
        child(pair)
    }
}

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
        let pairs = GoatParser::parse(Rule::goat, "program( ) do a done")
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
