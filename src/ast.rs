use parser::*;
use pest::iterators::Pair;
use pest::prec_climber::{Assoc, Operator, PrecClimber};
use pest::Span;

#[derive(Hash, Eq, PartialEq, Debug)]
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
}

#[derive(Debug, Eq, PartialEq)]
pub struct Label<'a> {
    identifier: Identifier<'a>,
}

impl<'a> Label<'a> {
    fn new(identifier: Identifier<'a>) -> Self {
        Label { identifier }
    }
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
        Rule::ident => Ast::Identifier(Identifier::new(pair.into_span())),
        Rule::function => {
            let mut inner = pair.into_inner();
            let labels = inner.next().unwrap().into_inner();
            let block = inner.next().unwrap();
            Ast::Function(
                labels
                    .map(|label| Label::new(Identifier::new(label.into_span())))
                    .collect(),
                Box::new(Ast::new(block)),
            )
        }
        Rule::application => {
            let mut inner = pair.into_inner();
            let ident = inner.next().unwrap();
            let arguments = inner.map(|it| Box::new(Ast::new(it))).collect();
            Ast::Application(Identifier::new(ident.into_span()), arguments)
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

pub trait Visitor {
    type Output;
    fn visit_empty(&self) -> Self::Output;
    fn visit_number(&self, number: &Span) -> Self::Output;
    fn visit_string(&self, string: &Span) -> Self::Output;
    fn visit_identifier(&self, identifier: &Identifier) -> Self::Output;
    fn visit_program(&self, ast: Box<Ast>) -> Self::Output;
    fn visit_function(&self, labels: &Vec<Label>, program: Box<Ast>) -> Self::Output;
    fn visit_label(&self, label: &Label) -> Self::Output;
    fn visit_application(&self, identifier: &Identifier, arguments: Vec<Box<Ast>>) -> Self::Output;
    fn visit_conditional(
        &self,
        true_branch: Box<Ast>,
        false_branch: Box<Ast>,
        else_branch: Option<Box<Ast>>,
    ) -> Self::Output;
    fn visit_declaration(
        &self,
        identifier: &Identifier,
        rhs: Box<Ast>,
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
        match ast {
            Ast::Empty => self.visit_empty(),
            Ast::Number(n) => self.visit_number(&n),
            Ast::Str(s) => self.visit_string(&s),
            Ast::Identifier(i) => self.visit_identifier(&i),
            Ast::Program(p) => self.visit_program(p),
            Ast::Function(l, p) => self.visit_function(&l, p),
            Ast::Application(i, a) => self.visit_application(&i, a),
            Ast::Conditional(t, f, e) => self.visit_conditional(t, f, e),
            Ast::Declaration(i, r, rst) => self.visit_declaration(&i, r, rst),
            Ast::Plus(lhs, rhs) => self.visit_plus(lhs, rhs),
            Ast::Minus(lhs, rhs) => self.visit_minus(lhs, rhs),
            Ast::Mult(lhs, rhs) => self.visit_mult(lhs, rhs),
            Ast::Div(lhs, rhs) => self.visit_div(lhs, rhs),
            Ast::Lte(lhs, rhs) => self.visit_lte(lhs, rhs),
            Ast::Gte(lhs, rhs) => self.visit_gte(lhs, rhs),
            Ast::Lt(lhs, rhs) => self.visit_lt(lhs, rhs),
            Ast::Gt(lhs, rhs) => self.visit_gt(lhs, rhs),
        }
    }
}

pub fn fold_empty<T: Folder + ?Sized>(_folder: &T) -> Ast {
    Ast::Empty
}

pub fn fold_span<'b, 'a: 'b, T: Folder + ?Sized>(_folder: &'b T, number: &'a Span<'a>) -> Span<'a> {
    number.clone()
}

pub fn fold_identifier<'b, 'a: 'b, T: Folder + ?Sized>(
    _folder: &'b T,
    identifier: &'a Identifier<'a>,
) -> Identifier<'a> {
    identifier.clone()
}

pub fn fold_program<T: Folder + ?Sized>(folder: &T, program: Box<Ast>) -> Box<Ast> {
    folder.fold(program)
}

pub fn fold_label<T: Folder + ?Sized>(folder: &T, label: Label) -> Label {
    let identifier = label.fold_identifier(label.identifier);
    Label::new(identifier)
}

pub fn fold_function<T: Folder + ?Sized>(
    folder: &T,
    labels: &Vec<Label>,
    program: Box<Ast>,
) -> Box<Ast> {
    let program = folder.fold_program(program);
    let labels: Vec<Label> = labels.map(|l| l.clone()).collect();
    Box::new(Ast::Function(labels, program))
}

pub trait Folder {
    fn fold_empty(&self) -> Ast {
        fold_empty(self)
    }

    fn fold_number<'b, 'a: 'b>(&'b self, number: &'a Span<'a>) -> Span<'a> {
        fold_span(self, number)
    }

    fn fold_string<'b, 'a: 'b>(&'b self, string: &'a Span<'a>) -> Span<'a> {
        fold_span(self, string)
    }

    fn fold_identifier<'b, 'a: 'b>(&'b self, identifier: &'a Identifier<'a>) -> Identifier<'a> {
        fold_identifier(self, identifier)
    }

    fn fold_program(&self, program: Box<Ast>) -> Box<Ast> {
        fold_program(self, program)
    }

    fn fold_label(&self, label: Label) -> Label {
        fold_label(self, label)
    }

    fn fold_function(&self, labels: &Vec<Label>, program: Box<Ast>) -> Box<Ast> {
        fold_function(self, labels, program)
    }
    // fn visit_label(&self, label: &Label) -> Self::Output;
    // fn visit_application(&self, identifier: &Identifier, arguments: Vec<Box<Ast>>) -> Self::Output;
    // fn visit_conditional(
    //     &self,
    //     true_branch: Box<Ast>,
    //     false_branch: Box<Ast>,
    //     else_branch: Option<Box<Ast>>,
    // ) -> Self::Output;
    // fn visit_declaration(
    //     &self,
    //     identifier: &Identifier,
    //     rhs: Box<Ast>,
    //     rest: Option<Box<Ast>>,
    // ) -> Self::Output;
    // fn visit_plus(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    // fn visit_minus(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    // fn visit_mult(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    // fn visit_div(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    // fn visit_lte(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    // fn visit_gte(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    // fn visit_lt(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
    // fn visit_gt(&self, lhs: Box<Ast>, rhs: Box<Ast>) -> Self::Output;
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
