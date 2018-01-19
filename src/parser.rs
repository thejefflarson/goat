#[cfg(debug_assertions)]
const _GRAMMAR: &'static str = include_str!("grammar.pest");
#[derive(Parser)]
#[grammar = "grammar.pest"]
struct GoatParser;
