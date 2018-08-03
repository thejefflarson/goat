use parser::*;
use pest::iterators::Pair;
use pest::Span;
use types::Ty;

#[derive(Hash, Eq, PartialEq, Debug)]
pub struct Identifier<'a> {
    name: Span<'a>,
    internal: Option<String>,
    ty: Option<Ty>,
}

impl<'a> Identifier<'a> {
    fn new(name: Span<'a>) -> Self {
        Identifier {
            name,
            internal: None,
            ty: None,
        }
    }
}

#[derive(Debug)]
pub struct Label<'a> {
    identifier: Identifier<'a>,
    expression: Option<Ast<'a>>,
}

#[derive(Debug)]
pub enum Ast<'a> {
    Empty,
    Number(Span<'a>),
    Identifier(Identifier<'a>),
    Str(Span<'a>),
    Program(Box<Ast<'a>>),
    Function(Vec<Label<'a>>),
    Application(Identifier<'a>, Vec<Box<Ast<'a>>>),
    Conditional(Box<Ast<'a>>, Box<Ast<'a>>),
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

fn child<'a>(pair: Pair<'a, Rule>) -> Result<Ast<'a>, String> {
    match pair.as_rule() {
        Rule::goat => {
            let inner = pair.into_inner().next();
            match inner {
                None => Ok(Ast::Empty),
                Some(pair) => Ast::new(pair),
            }.map(|i| Ast::Program(Box::new(i)))
        }
        Rule::number => Ok(Ast::Number(pair.into_span())),
        Rule::ident => Ok(Ast::Identifier(Identifier::new(pair.into_span()))),
        Rule::string => Ok(Ast::Str(pair.into_span())),
        _ => unimplemented!(),
    }
}

impl<'i> Ast<'i> {
    fn new<'a: 'i>(pair: Pair<'a, Rule>) -> Result<Self, String> {
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
        Ast::new(pairs).unwrap();
    }

    #[test]
    fn converts_number() {
        let pairs = GoatParser::parse(Rule::goat, "1").unwrap().nth(0).unwrap();
        println!("{:?}", pairs.clone());
        Ast::new(pairs).unwrap();
    }
}
