#![no_main]
#[macro_use]
extern crate libfuzzer_sys;
extern crate goat;
use goat::parser::*;
use goat::Parser;

fuzz_target!(|data: &[u8]| {
    // fuzzed code goes here
    if let Ok(s) = std::str::from_utf8(data) {
        let _ = GoatParser::parse(Rule::goat, s);
    }
});
