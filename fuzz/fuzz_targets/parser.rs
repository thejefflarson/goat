extern crate goat_parser;
#[macro_use]
extern crate afl;
use goat_parser::ast::*;
use goat_parser::parser::*;
use goat_parser::Parser;

fn main() {
    fuzz!(|data: &[u8]| {
        if let Ok(s) = std::str::from_utf8(data) {
            if let Ok(mut pairs) = GoatParser::parse(Rule::goat, s) {
                let root = pairs.nth(0).unwrap();
                let ast = Ast::new(root);
                let _ = Renamer::new().visit(ast);
            }
        }
    })
}
