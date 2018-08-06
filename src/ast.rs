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
                    })
                    .collect(),
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
                Operator::new(Rule::plus, Assoc::Left) | Operator::new(Rule::minus, Assoc::Left),
                Operator::new(Rule::multiply, Assoc::Left)
                    | Operator::new(Rule::divide, Assoc::Left),
            ]);

            let infix = |lhs: Ast<'a>, op: Pair<'a, Rule>, rhs: Ast<'a>| match op.as_rule() {
                Rule::plus => Ast::Plus(Box::new(lhs), Box::new(rhs)),
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
        GoatParser::parse(Rule::goat, "1 + 1").map_err(|e| println!("{}", e));
        let pairs = GoatParser::parse(Rule::goat, "1 + 1")
            .unwrap()
            .nth(0)
            .unwrap();
        let ast = Ast::new(pairs);
        println!("{:#?}", ast)
    }
}
