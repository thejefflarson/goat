use goat_parser::parser::{GoatParser, Rule};
use pest::Parser;

fn main() {
    for src in [
        "a = ;\nb = 2;\nb",
        "match x do",
        "m = match x do\n  A then 1\ny = 2;\ny",
    ] {
        println!("=== {src:?}");
        match GoatParser::parse(Rule::goat, src) {
            Ok(_) => println!("pest: ok"),
            Err(e) => println!("pest: 1 error, no tree\n{e}"),
        }
        let p = rowan_slice::parse(src);
        println!("rowan: {} diagnostic(s), full tree:", p.diagnostics.len());
        for d in &p.diagnostics {
            println!("  {}..{}: {}", d.range.start, d.range.end, d.message);
        }
        print!("{:#?}", p.syntax());
    }
}
