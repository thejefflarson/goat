#![no_main]
#[macro_use]
extern crate libfuzzer_sys;
extern crate goat;
use goat::ast::*;
use goat::parser::*;
use goat::Parser;

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        if let Ok(mut pairs) = GoatParser::parse(Rule::goat, s) {
            let root = pairs.nth(0).unwrap();
            let ast = Ast::new(root);
            let _ = Renamer::new().visit(ast);
        }
    }
});
