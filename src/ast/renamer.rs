use ast::{Ast, Folder, Identifier};
use std::cell::RefCell;

const ALPHA: &str = "abcdefghijklmnopqrstuvwxyz";
struct Namer {
    last: usize,
}
impl Namer {
    fn new() -> Self {
        Namer { last: 0 }
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

pub struct Renamer {
    namer: RefCell<Namer>,
}

impl Renamer {
    pub fn new() -> Self {
        Renamer {
            namer: RefCell::new(Namer::new()),
        }
    }
}

impl<'a> Folder<'a> for Renamer {
    fn visit_identifier(&self, identifier: Identifier<'a>) -> Ast<'a> {
        let mut namer = self.namer.borrow_mut();
        let var = namer.next();
        Ast::Identifier(identifier.rename(var))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::Bool;
    use parser::{GoatParser, Rule};
    use pest::Parser;
    #[test]
    fn rewrites_ast() {
        let id = "b";
        let pairs = GoatParser::parse(Rule::goat, id).unwrap().nth(0).unwrap();
        let ast = Ast::new(pairs.clone());
        let rewrite = Renamer::new().visit(ast);
        let ident = GoatParser::parse(Rule::ident, id)
            .unwrap()
            .nth(0)
            .unwrap()
            .as_span();

        assert_eq!(
            Ast::new(pairs),
            Ast::Program(Box::new(Ast::Identifier(Identifier {
                internal: "b".to_string(),
                name: ident.clone()
            })))
        );

        assert_eq!(
            rewrite,
            Ast::Program(Box::new(Ast::Identifier(Identifier {
                internal: "a".to_string(),
                name: ident
            })))
        );
    }

    #[test]
    fn parses_boolean_comparisons() {
        let math = "true<false";
        let pairs = GoatParser::parse(Rule::goat, math).unwrap().nth(0).unwrap();
        let ast = Ast::new(pairs);
        let rewrite = Renamer::new().visit(ast.clone());

        assert_eq!(
            rewrite,
            Ast::Program(Box::new(Ast::Lt(
                Box::new(Ast::Bool(Bool::True)),
                Box::new(Ast::Bool(Bool::False))
            )))
        );
    }
}
