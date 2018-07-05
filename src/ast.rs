use parser::*;
use pest::iterators::{Pair, Pairs};
use pest::Span;
use types::Ty;

#[derive(Hash, Eq, PartialEq, Debug)]
pub struct Identifier<'a> {
    name: Span<'a>,
    internal: Option<String>,
    ty: Option<Ty>,
}

#[derive(Debug)]
pub struct Label<'a> {
    identifier: Identifier<'a>,
    expression: Option<Expr<'a>>,
}

#[derive(Debug)]
pub enum Expr<'a> {
    Empty,
    Number(Span<'a>),
    Identifier(Identifier<'a>),
    Str(Span<'a>),
    Program(Box<Expr<'a>>),
    Function(Vec<Label<'a>>),
    Application(Identifier<'a>, Vec<Box<Expr<'a>>>),
    Conditional(Box<Expr<'a>>, Box<Expr<'a>>),
    Plus(Box<Expr<'a>>, Box<Expr<'a>>),
    Minus(Box<Expr<'a>>, Box<Expr<'a>>),
    Mult(Box<Expr<'a>>, Box<Expr<'a>>),
    Div(Box<Expr<'a>>, Box<Expr<'a>>),
    Lte(Box<Expr<'a>>, Box<Expr<'a>>),
    Gte(Box<Expr<'a>>, Box<Expr<'a>>),
    Lt(Box<Expr<'a>>, Box<Expr<'a>>),
    Gt(Box<Expr<'a>>, Box<Expr<'a>>),
    Declaration(Identifier<'a>, Box<Expr<'a>>, Option<Box<Expr<'a>>>),
}

pub trait Ast {
    fn to_ast(&self) -> Result<Expr, &str>;
}

fn child<'a>(pair: &Pair<'a, Rule>) -> Result<Expr<'a>, &'a str> {
    match pair.as_rule() {
        Rule::goat => pair.into_inner()
            .next()
            .ok_or(Err(""))
            .map(|it| it.to_ast()),
        _ => unimplemented!(),
    }
}

impl<'a> Ast for Pair<'a, Rule> {
    fn to_ast(&self) -> Result<Expr, &str> {
        child(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pest::Parser;

    #[test]
    fn converts_empty() {
        let pairs = GoatParser::parse(Rule::goat, "").unwrap().nth(0).unwrap();
        pairs.to_ast().unwrap();
    }

    #[test]
    fn converts_number() {
        let pairs = GoatParser::parse(Rule::goat, "1").unwrap().nth(0).unwrap();
        println!("{:?}", pairs.to_ast());
        pairs.to_ast().unwrap();
    }
}
