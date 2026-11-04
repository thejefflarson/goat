use pest::error::Error;
use std::fmt;

#[cfg(debug_assertions)]
const _GRAMMAR: &str = include_str!("grammar.pest");

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct GoatParser;

#[derive(Debug)]
pub struct ParseError(Error<Rule>);

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for ParseError {}

impl From<Error<Rule>> for ParseError {
    fn from(error: Error<Rule>) -> Self {
        ParseError(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_records_and_field_access() {
        use pest::Parser;
        for src in [
            "{x: 1, y: 2}",
            "{}",
            "p.x",
            "p.x.y",
            "{a: {b: 1}}",
            "f(1).x",
            "{point: {x: 1, y: 2}}.point.x",
        ] {
            assert!(
                GoatParser::parse(Rule::goat, src).is_ok(),
                "failed to parse: {src}"
            );
        }
    }

    #[test]
    fn identifiers_may_start_with_a_keyword() {
        use pest::Parser;
        // A word boundary guards the keyword check, so names that merely begin
        // with a keyword are valid identifiers.
        for name in [
            "double",
            "doner",
            "ifx",
            "thenable",
            "truthy",
            "programmer",
            "functions",
        ] {
            let pairs = GoatParser::parse(Rule::ident, name);
            assert!(pairs.is_ok(), "{name} should be a valid identifier");
            assert_eq!(pairs.unwrap().as_str(), name);
        }
        // Bare keywords are still reserved.
        for kw in ["do", "done", "if", "then", "program", "function"] {
            assert!(
                GoatParser::parse(Rule::ident, kw).is_err(),
                "{kw} should be reserved"
            );
        }
    }

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
    fn parses_comment() {
        parses_to! {
            parser: GoatParser,
            input: "# comment",
            rule: Rule::goat,
            tokens: [goat(0, 9, [EOI(9, 9)])]
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
            tokens: [boolean(0, 4, [true_lit(0, 4)])]
        }

        parses_to! {
            parser: GoatParser,
            input: "false",
            rule: Rule::boolean,
            tokens: [boolean(0, 5, [false_lit(0, 5)])]
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
            input: "a_",
            rule: Rule::ident,
            tokens: [ident(0, 2)]
        }

        parses_to! {
            parser: GoatParser,
            input: "a9",
            rule: Rule::ident,
            tokens: [ident(0, 2)]
        }

        parses_to! {
            parser: GoatParser,
            input: "نامهای",
            rule: Rule::ident,
            tokens: [ident(0, 12)]
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
                    params(8, 9, [ident(8, 9)]),
                    expr(14, 16, [ident(14, 15)])
                ])
            ]
        }
    }

    #[test]
    fn program_and_function_are_synonyms() {
        use pest::Parser;
        // `function` introduces a function literal identically to `program`; the
        // keyword is silent, so both lower to the same `function` node.
        for src in ["program(a) do a done", "function(a) do a done"] {
            assert!(
                GoatParser::parse(Rule::function, src).is_ok(),
                "failed to parse function literal: {src}"
            );
        }
    }
    #[test]
    fn parses_calls() {
        parses_to! {
            parser: GoatParser,
            input: "a(1, true, b, program(a) do a done)",
            rule: Rule::expr,
            tokens: [
                expr(0, 35, [
                    ident(0, 1),
                    call(1, 35, [
                        arguments(2, 34, [
                            expr(2, 3, [number(2, 3)]),
                            expr(5, 9, [boolean(5, 9, [true_lit(5, 9)])]),
                            expr(11, 12, [ident(11, 12)]),
                            expr(14, 34, [
                                function(14, 34, [
                                    params(22, 23, [ident(22, 23)]),
                                    expr(28, 30, [ident(28, 29)])
                                ])
                            ])
                        ])
                    ])
                ])
            ]
        }

        parses_to! {
            parser: GoatParser,
            input: "a()",
            rule: Rule::expr,
            tokens: [expr(0, 3, [ident(0, 1), call(1, 3)])]
        }

        // Calls and accesses interleave on any callee.
        parses_to! {
            parser: GoatParser,
            input: "s.f(1)(2)",
            rule: Rule::expr,
            tokens: [
                expr(0, 9, [
                    ident(0, 1),
                    access(1, 3, [ident(2, 3)]),
                    call(3, 6, [arguments(4, 5, [expr(4, 5, [number(4, 5)])])]),
                    call(6, 9, [arguments(7, 8, [expr(7, 8, [number(7, 8)])])])
                ])
            ]
        }
    }

    #[test]
    fn grouped_expression_is_not_a_call() {
        parses_to! {
            parser: GoatParser,
            input: "(1 + 2) < 3",
            rule: Rule::expr,
            tokens: [
                expr(0, 11, [
                    expr(1, 6, [number(1, 2), plus(3, 4), number(5, 6)]),
                    lt(8, 9),
                    number(10, 11)
                ])
            ]
        }
    }

    #[test]
    fn number_has_no_sign() {
        use pest::Parser;
        parses_to! {
            parser: GoatParser,
            input: "5 -1",
            rule: Rule::expr,
            tokens: [expr(0, 4, [number(0, 1), minus(2, 3), number(3, 4)])]
        }
        parses_to! {
            parser: GoatParser,
            input: "-3",
            rule: Rule::expr,
            tokens: [expr(0, 2, [negation(0, 2, [minus(0, 1), number(1, 2)])])]
        }
        for src in [".5", "007", "0.5", "-f(x).y", "--3"] {
            assert!(GoatParser::parse(Rule::goat, src).is_ok(), "failed: {src}");
        }
    }

    #[test]
    fn parses_empty_string_and_trailing_commas() {
        use pest::Parser;
        for src in [r#""""#, "{x: 1,}", "f(1,)", "f(1, 2,)"] {
            assert!(GoatParser::parse(Rule::goat, src).is_ok(), "failed: {src}");
        }
        for src in ["{,}", "f(,)"] {
            assert!(
                GoatParser::parse(Rule::goat, src).is_err(),
                "accepted: {src}"
            );
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
                    expr(3, 8, [boolean(3, 7, [true_lit(3, 7)])]),
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

    #[test]
    fn uppercase_names_are_tags_and_lowercase_are_identifiers() {
        use pest::Parser;
        for name in ["circle", "x", "matchbox", "matcher", "éclair"] {
            assert!(GoatParser::parse(Rule::ident, name).is_ok(), "{name}");
            assert!(GoatParser::parse(Rule::tag_name, name).is_err(), "{name}");
        }
        for name in ["Circle", "Empty", "X", "Éclair", "Matchbox"] {
            assert!(GoatParser::parse(Rule::tag_name, name).is_ok(), "{name}");
            assert!(GoatParser::parse(Rule::ident, name).is_err(), "{name}");
        }
    }

    #[test]
    fn match_is_a_reserved_word() {
        use pest::Parser;
        assert!(GoatParser::parse(Rule::ident, "match").is_err());
    }

    #[test]
    fn parses_tags() {
        parses_to! {
            parser: GoatParser,
            input: "Empty",
            rule: Rule::tag,
            tokens: [tag(0, 5, [tag_name(0, 5)])]
        }

        parses_to! {
            parser: GoatParser,
            input: "Circle(5)",
            rule: Rule::tag,
            tokens: [tag(0, 9, [
                tag_name(0, 6),
                arguments(7, 8, [expr(7, 8, [number(7, 8)])])
            ])]
        }

        parses_to! {
            parser: GoatParser,
            input: "Link(x, rest)",
            rule: Rule::tag,
            tokens: [tag(0, 13, [
                tag_name(0, 4),
                arguments(5, 12, [
                    expr(5, 6, [ident(5, 6)]),
                    expr(8, 12, [ident(8, 12)])
                ])
            ])]
        }
    }

    #[test]
    fn parses_match() {
        use pest::Parser;
        let src = "match s do Circle(r) then r Empty then 0 else 1 done";
        let mut pairs = GoatParser::parse(Rule::match_expr, src).unwrap();
        let children: Vec<_> = pairs
            .next()
            .unwrap()
            .into_inner()
            .map(|p| p.as_rule())
            .collect();
        assert_eq!(children, [Rule::expr, Rule::arm, Rule::arm, Rule::expr]);

        let arm = GoatParser::parse(Rule::arm, "Circle(r) then r")
            .unwrap()
            .next()
            .unwrap();
        let parts: Vec<_> = arm.into_inner().map(|p| p.as_rule()).collect();
        assert_eq!(parts, [Rule::pattern, Rule::expr]);
    }

    #[test]
    fn parses_match_programs() {
        use pest::Parser;
        for src in [
            "match x do done",
            "match x do else 0 done",
            "match x do A then 1 done",
            "match x do Link(a, b) then a\n  Empty then 0\n  else 2 done",
            "match Circle(5) do Circle(r) then r * r done",
            "match x do A then match y do B then 1 else 2 done else 3 done",
            "area = program(s) do match s do Circle(r) then r Square(w, h) then w * h done done\narea(Circle(2))",
            "f(Link(1, Empty))",
            "Circle(5).x",
            "{shape: Empty}",
        ] {
            assert!(
                GoatParser::parse(Rule::goat, src).is_ok(),
                "failed to parse: {src}"
            );
        }
    }

    #[test]
    fn parses_record_spread() {
        parses_to! {
            parser: GoatParser,
            input: "{...p, x: 1}",
            rule: Rule::record,
            tokens: [record(0, 12, [
                spread(1, 5, [expr(4, 5, [ident(4, 5)])]),
                field(7, 11, [ident(7, 8), expr(10, 11, [number(10, 11)])])
            ])]
        }
        parses_to! {
            parser: GoatParser,
            input: "{...p}",
            rule: Rule::record,
            tokens: [record(0, 6, [spread(1, 5, [expr(4, 5, [ident(4, 5)])])])]
        }
    }

    #[test]
    fn a_second_spread_still_parses_so_lowering_can_explain_it() {
        use pest::Parser;
        for src in ["{...a, ...b}", "{x: 1, ...a}", "{...a.b, y: f(1),}"] {
            assert!(
                GoatParser::parse(Rule::goat, src).is_ok(),
                "failed to parse: {src}"
            );
        }
        for src in ["{...}", "{,...a}", "{.. a}"] {
            assert!(
                GoatParser::parse(Rule::goat, src).is_err(),
                "accepted: {src}"
            );
        }
    }

    #[test]
    fn parses_destructuring() {
        parses_to! {
            parser: GoatParser,
            input: "{x, y} = p",
            rule: Rule::destructure,
            tokens: [destructure(0, 10, [
                record_pattern(0, 6, [ident(1, 2), ident(4, 5)]),
                expr(9, 10, [ident(9, 10)])
            ])]
        }
        parses_to! {
            parser: GoatParser,
            input: "{x, ...rest} = p x",
            rule: Rule::destructure,
            tokens: [destructure(0, 18, [
                record_pattern(0, 12, [ident(1, 2), rest_binding(4, 11, [ident(7, 11)])]),
                expr(15, 17, [ident(15, 16)]),
                expr(17, 18, [ident(17, 18)])
            ])]
        }
    }

    #[test]
    fn destructuring_does_not_capture_record_literals() {
        use pest::Parser;
        for src in ["{x: 1}", "{x: 1} = 2"] {
            let pairs = GoatParser::parse(Rule::destructure, src);
            assert!(pairs.is_err(), "{src} is not a pattern");
        }
        for src in [
            "{x}",
            "{x, y}",
            "{x, ...r}",
            "{...r} = p",
            "{...r, } = p",
            "{x,} = p",
        ] {
            let ok = GoatParser::parse(Rule::goat, src).is_ok();
            assert_eq!(ok, src.contains('='), "{src}");
        }
        for src in [
            "{} = p",
            "{...a, x} = p",
            "{...a, ...b} = p",
            "{x, ...r, y} = p",
        ] {
            assert!(
                GoatParser::parse(Rule::goat, src).is_err(),
                "accepted: {src}"
            );
        }
    }

    #[test]
    fn parses_destructuring_parameters() {
        use pest::Parser;
        let src = "program({x, y}) do x + y done";
        let function = GoatParser::parse(Rule::function, src)
            .unwrap()
            .next()
            .unwrap();
        let params = function.into_inner().next().unwrap();
        assert_eq!(params.as_rule(), Rule::params);
        let kinds: Vec<_> = params.into_inner().map(|p| p.as_rule()).collect();
        assert_eq!(kinds, [Rule::record_pattern]);

        for src in [
            "program(a, {x, ...r}, b) do a done",
            "program({...r}) do r done",
            "function({x}) do x done",
        ] {
            assert!(
                GoatParser::parse(Rule::goat, src).is_ok(),
                "failed to parse: {src}"
            );
        }
    }
}
