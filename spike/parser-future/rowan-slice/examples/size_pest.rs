//! Baseline for `size.rs`: the same measurement with the real pest grammar.
use goat_parser::parser::{GoatParser, Rule};
use pest::Parser;

fn main() {
    let src = std::hint::black_box(String::from("a = 1; match a do A then 2 done"));
    std::hint::black_box(GoatParser::parse(Rule::goat, &src).is_ok());
}
