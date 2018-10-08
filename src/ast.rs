use parser::*;
use pest::iterators::Pair;
use pest::prec_climber::{Assoc, Operator, PrecClimber};
use pest::Span;

#[derive(Hash, Eq, PartialEq, Debug)]
pub struct Identifier<'a> {
    name: Span<'a>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Label<'a> {
    identifier: Identifier<'a>,
}

#[derive(Debug, Eq, PartialEq)]
pub enum Ast<'a> {
    Empty,
    Number(Span<'a>),
    Identifier(Identifier<'a>),
    Str(Span<'a>),
    Program(Box<Ast<'a>>),
    Function(Vec<Label<'a>>, Box<Ast<'a>>),
    Application(Identifier<'a>, Vec<Box<Ast<'a>>>),
    Conditional(Box<Ast<'a>>, Box<Ast<'a>>, Option<Box<Ast<'a>>>),
    Plus(Box<Ast<'a>>, Box<Ast<'a>>),
    Minus(Box<Ast<'a>>, Box<Ast<'a>>),
    Mult(Box<Ast<'a>>, Box<Ast<'a>>),
    Div(Box<Ast<'a>>, Box<Ast<'a>>),
    Lte(Box<Ast<'a>>, Box<Ast<'a>>),
    Gte(Box<Ast<'a>>, Box<Ast<'a>>),
    Lt(Box<Ast<'a>>, Box<Ast<'a>>),
    Gt(Box<Ast<'a>>, Box<Ast<'a>>),
    Declaration(Identifier<'a>, Box<Ast<'a>>, Option<Box<Ast<'a>>>),
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
        Rule::string => Ast::Str(pair.into_span()),
        Rule::number => Ast::Number(pair.into_span()),
        Rule::ident => Ast::Identifier(Identifier {
            name: pair.into_span(),
        }),
        Rule::function => {
            let mut inner = pair.into_inner();
            let labels = inner.next().unwrap().into_inner();
            let block = inner.next().unwrap();
            Ast::Function(
                labels
                    .map(|label| Label {
                        identifier: Identifier {
                            name: label.into_span(),
                        },
                    }).collect(),
                Box::new(Ast::new(block)),
            )
        }
        Rule::application => {
            let mut inner = pair.into_inner();
            let ident = inner.next().unwrap();
            let arguments = inner.map(|it| Box::new(Ast::new(it))).collect();
            Ast::Application(
                Identifier {
                    name: ident.into_span(),
                },
                arguments,
            )
        }
        Rule::conditional => {
            let mut inner = pair.into_inner();
            let cond = Ast::new(inner.next().unwrap());
            let then = Ast::new(inner.next().unwrap());
            let els = inner.next().map(|i| Box::new(Ast::new(i)));
            Ast::Conditional(Box::new(cond), Box::new(then), els)
        }
        Rule::expr => {
            let climber = PrecClimber::new(vec![
                Operator::new(Rule::lt, Assoc::Left)
                    | Operator::new(Rule::lte, Assoc::Left)
                    | Operator::new(Rule::gt, Assoc::Left)
                    | Operator::new(Rule::gt, Assoc::Left),
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
        _ => unimplemented!(),
    }
}

impl<'i> Ast<'i> {
    fn new<'a: 'i>(pair: Pair<'a, Rule>) -> Self {
        child(pair)
    }
}

trait Visitor<T> {
    fn visit_empty(&self) -> T;
    fn visit_number(&self, number: &Span) -> T;
    fn visit_string(&self, string: &Span) -> T;
    fn visit_identifier(&self, identifier: &Identifier) -> T;
    fn visit_program(&self, ast: &Box<Ast>) -> T;
    fn visit_function(&self, labels: &Vec<Label>, program: &Box<Ast>) -> T;
    fn visit_application(&self, identifier: &Identifier, arguments: &Vec<Box<Ast>>) -> T;
    fn visit_conditional(
        &self,
        true_branch: &Box<Ast>,
        false_branch: &Box<Ast>,
        else_branch: &Box<Ast>,
    ) -> T;
    fn visit_declaration(
        &self,
        identifier: &Identifier,
        rhs: &Box<Ast>,
        rest: &Option<Box<Ast>>,
    ) -> T;
    fn visit_plus(&self, lhs: &Box<Ast>, rhs: &Box<Ast>) -> T;
    fn visit_minus(&self, lhs: &Box<Ast>, rhs: &Box<Ast>) -> T;
    fn visit_mult(&self, lhs: &Box<Ast>, rhs: &Box<Ast>) -> T;
    fn visit_div(&self, lhs: &Box<Ast>, rhs: &Box<Ast>) -> T;
    fn visit_lte(&self, lhs: &Box<Ast>, rhs: &Box<Ast>) -> T;
    fn visti_gte(&self, lhs: &Box<Ast>, rhs: &Box<Ast>) -> T;
    fn visit_lt(&self, lhs: &Box<Ast>, rhs: &Box<Ast>) -> T;
    fn visit_gt(&self, lhs: &Box<Ast>, rhs: &Box<Ast>) -> T;
    fn visit(&self, ast: Ast) -> T {
        match ast {
            Ast::Empty => self.visit_empty(),
            Ast::Number(n) => self.visit_number(&n),
            Ast::Str(s) => self.visit_string(&s),
            Ast::Identifier(i) => self.visit_identifier(&i),
            Ast::Program(p) => self.visit_program(&p),
            Ast::Function(l, p) => self.visit_function(&l, &p),
            _ => unimplemented!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pest::Parser;
    use pest::Position;

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
        let start = Position::from_start(prog);
        let end = start.clone().match_string("1").unwrap();
        assert_eq!(ast, Ast::Program(Box::new(Ast::Number(start.span(&end)))))
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
