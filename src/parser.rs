#[cfg(debug_assertions)]
const _GRAMMAR: &str = include_str!("grammar.pest");

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
            tokens: [goat(0, 0, [EOI(0, 0)])]
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
    fn parses_identifiers() {
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
            tokens: [
                declaration(0, 5, [
                    ident(0, 1),
                    expr(4, 5, [ident(4, 5)])
                ])
            ]
        }

        parses_to! {
            parser: GoatParser,
            input: "a = b a",
            rule: Rule::declaration,
            tokens: [
                declaration(0, 7, [
                    ident(0, 1),
                    expr(4, 6, [ident(4, 5)]),
                    expr(6, 7, [ident(6, 7)])
                ])
            ]
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
            tokens: [
                function(0, 20, [
                    labels(8, 9, [ident(8, 9)]),
                    expr(14, 16, [ident(14, 15)])
                ])
            ]
        }
    }
    #[test]
    fn parses_applications() {
        parses_to! {
            parser: GoatParser,
            input: "a(1, true, b, program(a) do a done)",
            rule: Rule::application,
            tokens: [
                application(0, 35, [
                    ident(0, 1),
                    arguments(2, 34, [
                        expr(2, 3, [number(2, 3)]),
                        expr(5, 9, [boolean(5, 9)]),
                        expr(11, 12, [ident(11, 12)]),
                        expr(14, 34, [
                            function(14, 34, [
                                labels(22, 23, [ident(22, 23)]),
                                expr(28, 30, [ident(28, 29)])
                            ])
                        ])
                    ])
                ])
            ]
        }

        parses_to! {
            parser: GoatParser,
            input: "a()",
            rule: Rule::application,
            tokens: [
                application(0, 3, [ident(0,1)])
            ]
        }
    }

    #[test]
    fn parses_conditional() {
        parses_to! {
            parser: GoatParser,
            input: "if true then 1 else 0 done",
            rule: Rule::conditional,
            tokens: [
                conditional(0, 26, [
                    expr(3, 8, [boolean(3,7)]),
                    expr(13, 15, [number(13, 14)]),
                    expr(20, 22, [number(20, 21)])
                ])
            ]
        }
    }

    #[test]
    fn parses_math() {
        parses_to! {
            parser: GoatParser,
            input: "1 + 2",
            rule: Rule::expr,
            tokens: [expr(0, 5, [number(0, 1), plus(2, 3), number(4, 5)])]
        }

        parses_to! {
            parser: GoatParser,
            input: "1 + (3 - 5)",
            rule: Rule::expr,
            tokens: [
                expr(0, 11, [
                    number(0, 1),
                    plus(2, 3),
                    expr(5, 10, [
                        number(5, 6),
                        minus(7, 8),
                        number(9, 10)
                    ])
                ])
            ]
        }
    }
}
