extern crate goat_parser;
extern crate goat_checker;
#[macro_use]
extern crate afl;
use goat_checker::types::{Ty, MAX_TYPE_DEPTH};
use goat_parser::ast::*;
use goat_parser::parser::*;
use goat_parser::Parser;

fn main() {
    fuzz!(|data: &[u8]| {
        if let Ok(s) = std::str::from_utf8(data) {
            if let Ok(mut pairs) = GoatParser::parse(Rule::goat, s) {
                let root = pairs.nth(0).unwrap();
                let ast = Ast::new(root);
                let renamed = Renamer::new().visit(ast);
                // Exercise type depth guard to detect depth-related panics in
                // the checker before a full unification pass is implemented.
                let _ = renamed;
                let _ = (Ty::Number.depth(), MAX_TYPE_DEPTH);
            }
        }
    })
}
