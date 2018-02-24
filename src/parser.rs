#[cfg(debug_assertions)]
const _GRAMMAR: &'static str = include_str!("grammar.pest");

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct GoatParser;

#[cfg(test)]
mod tests {
    use super::*;
    use pest::Parser;

    #[test]
    fn parses_empty() {
        parses_to! {
            parser: GoatParser,
            input: "",
            rule: Rule::goat,
            tokens: [goat(0, 0)]
        }
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
            input: r#""hello""#,
            rule: Rule::string,
            tokens: [string(0, 7)]
        }
    }

    #[test]
    fn parses_booleans() {
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

    #[test]
    fn parses_idents() {
        parses_to! {
            parser: GoatParser,
            input: "a",
            rule: Rule::ident,
            tokens: [ident(0, 1)]
        }

        parses_to! {
            parser: GoatParser,
            input: "aA",
            rule: Rule::ident,
            tokens: [ident(0, 2)]
        }

        parses_to! {
            parser: GoatParser,
            input: "a9",
            rule: Rule::ident,
            tokens: [ident(0, 2)]
        }
    }

    #[test]
    fn parses_declarations() {
        parses_to! {
            parser: GoatParser,
            input: "a = b",
            rule: Rule::declaration,
            tokens: [declaration(0, 5, [ident(0, 1), ident(4, 5)])]
        }
    }

    #[test]
    fn parses_functions() {
        parses_to! {
            parser: GoatParser,
            input: "a, b",
            rule: Rule::labels,
            tokens: [labels(0, 4, [ident(0, 1), ident(3, 4)])]
        }

        parses_to! {
            parser: GoatParser,
            input: "a",
            rule: Rule::labels,
            tokens: [labels(0, 1, [ident(0, 1)])]
        }

        parses_to! {
            parser: GoatParser,
            input: "program(a) do a done",
            rule: Rule::function,
            tokens: [function(0, 20, [labels(8, 9, [ident(8, 9)]), ident(14, 15)])]
        }

        parses_to! {
            parser: GoatParser,
            input: "a(1, true, b, program(a) do a done)",
            rule: Rule::application,
            tokens: [
                application(0, 35, [
                    ident(0, 1),
                    arguments(2, 34, [
                        number(2, 3),
                        boolean(5, 9),
                        ident(11, 12),
                        function(14, 34, [
                            labels(22, 23, [ident(22, 23)]), ident(28, 29)
                        ])
                    ])
                ])
            ]
        }
    }
}
