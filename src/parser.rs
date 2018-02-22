#[cfg(debug_assertions)]
const _GRAMMAR: &'static str = include_str!("grammar.pest");

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct GoatParser;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn parses_empty() {
        parses_to! {
            parser: GoatParser,
            input: "",
            rule: Rule::goat,
            tokens: [goat(0, 0)]
        };
    }

    #[test]
    fn parses_numbers() {
        parses_to! {
            parser: GoatParser,
            input: "1",
            rule: Rule::number,
            tokens: [number(0, 1)]
        }

        parses_to! {
            parser: GoatParser,
            input: "1.1",
            rule: Rule::number,
            tokens: [number(0, 3)]
        }
    }

    #[test]
    fn parses_strings() {
        parses_to! {
            parser: GoatParser,
            input: "\"hello\"",
            rule: Rule::string,
            tokens: [string(0, 7)]
        }
    }

    #[test]
    fn parses_boolean() {
        parses_to! {
            parser: GoatParser,
            input: "true",
            rule: Rule::boolean,
            tokens: [boolean(0, 4)]
        }

        parses_to! {
            parser: GoatParser,
            input: "false",
            rule: Rule::boolean,
            tokens: [boolean(0, 5)]
        }
    }
}
