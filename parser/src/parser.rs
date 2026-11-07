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
            let pairs = GoatParser::parse(Rule::name, name);
            assert!(pairs.is_ok(), "{name} should be a valid identifier");
            assert_eq!(pairs.unwrap().as_str(), name);
        }
        // Bare keywords are still reserved.
        for kw in ["do", "done", "if", "then", "program", "function"] {
            assert!(
                GoatParser::parse(Rule::name, kw).is_err(),
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
            rule: Rule::name,
            tokens: [name(0, 1)]
        }

        parses_to! {
            parser: GoatParser,
            input: "a_",
            rule: Rule::name,
            tokens: [name(0, 2)]
        }

        parses_to! {
            parser: GoatParser,
            input: "a9",
            rule: Rule::name,
            tokens: [name(0, 2)]
        }

        parses_to! {
            parser: GoatParser,
            input: "نامهای",
            rule: Rule::name,
            tokens: [name(0, 12)]
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
                    name(0, 1),
                    value(4, 5, [name(4, 5)])
                ])
            ]
        }

        parses_to! {
            parser: GoatParser,
            input: "a = b a",
            rule: Rule::declaration,
            tokens: [
                declaration(0, 7, [
                    name(0, 1),
                    value(4, 6, [name(4, 5)]),
                    expr(6, 7, [name(6, 7)])
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
            tokens: [labels(0, 4, [name(0, 1), name(3, 4)])]
        }

        parses_to! {
            parser: GoatParser,
            input: "a",
            rule: Rule::labels,
            tokens: [labels(0, 1, [name(0, 1)])]
        }

        parses_to! {
            parser: GoatParser,
            input: "program(a) do a done",
            rule: Rule::function,
            tokens: [
                function(0, 20, [
                    params(8, 9, [name(8, 9)]),
                    expr(14, 16, [name(14, 15)])
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
                    name(0, 1),
                    call(1, 35, [
                        arguments(2, 34, [
                            expr(2, 3, [number(2, 3)]),
                            expr(5, 9, [boolean(5, 9, [true_lit(5, 9)])]),
                            expr(11, 12, [name(11, 12)]),
                            expr(14, 34, [
                                function(14, 34, [
                                    params(22, 23, [name(22, 23)]),
                                    expr(28, 30, [name(28, 29)])
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
            tokens: [expr(0, 3, [name(0, 1), call(1, 3)])]
        }

        // Calls and accesses interleave on any callee.
        parses_to! {
            parser: GoatParser,
            input: "s.f(1)(2)",
            rule: Rule::expr,
            tokens: [
                expr(0, 9, [
                    name(0, 1),
                    access(1, 3, [name(2, 3)]),
                    call(3, 6, [arguments(4, 5, [expr(4, 5, [number(4, 5)])])]),
                    call(6, 9, [arguments(7, 8, [expr(7, 8, [number(7, 8)])])])
                ])
            ]
        }
    }

    #[test]
    fn parses_foreign_declarations() {
        use pest::Parser;
        for src in [
            r#"f = foreign "m" "f" (Number) -> Unit"#,
            r#"f = foreign "m" "f" () -> Bool"#,
            r#"f = foreign "m" "f" (Number, String,) -> Unit f(1, "a")"#,
            r#"f = foreign "m" "f" ({x: Number}) -> [Bool]"#,
            r#"f = foreign "m" "f" ((Number) -> Unit) -> Unit"#,
            r#"f = foreign m "f" (Number) -> Unit"#,
            "foreign = 1 foreign + 1",
        ] {
            assert!(GoatParser::parse(Rule::goat, src).is_ok(), "failed: {src}");
        }
        for src in [
            r#"f = foreign "m" "f" (Number)"#,
            r#"f = foreign "m" "f" Number -> Unit"#,
            r#"f = foreign "m" (Number) -> Unit"#,
        ] {
            assert!(
                GoatParser::parse(Rule::goat, src).is_err(),
                "accepted: {src}"
            );
        }
    }

    #[test]
    fn a_foreign_declaration_is_a_declaration_with_a_signature() {
        parses_to! {
            parser: GoatParser,
            input: r#"f = foreign "m" "g" (Number) -> Unit"#,
            rule: Rule::declaration,
            tokens: [
                declaration(0, 36, [
                    name(0, 1),
                    foreign_decl(4, 36, [
                        foreign_kw(4, 11),
                        foreign_name(12, 15, [string(12, 15)]),
                        foreign_name(16, 19, [string(16, 19)]),
                        fn_type(20, 36, [type_name(21, 27), type_name(32, 36)])
                    ])
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
    fn parses_list_literals() {
        parses_to! {
            parser: GoatParser,
            input: "[]",
            rule: Rule::list,
            tokens: [list(0, 2)]
        }
        parses_to! {
            parser: GoatParser,
            input: "[1, x]",
            rule: Rule::list,
            tokens: [list(0, 6, [arguments(1, 5, [
                expr(1, 2, [number(1, 2)]),
                expr(4, 5, [name(4, 5)])
            ])])]
        }
        use pest::Parser;
        for src in ["[]", "[1,]", "[[1], [], [2, 3]]", "[f(1), a + 1]", "[1].x"] {
            assert!(GoatParser::parse(Rule::goat, src).is_ok(), "failed: {src}");
        }
        for src in ["[,]", "[1,,2]", "[1", "1]"] {
            assert!(
                GoatParser::parse(Rule::goat, src).is_err(),
                "accepted: {src}"
            );
        }
    }

    #[test]
    fn parses_list_patterns() {
        use pest::Parser;
        for src in [
            "[]",
            "[a]",
            "[a, b]",
            "[a, ...rest]",
            "[...rest]",
            "[a, b,]",
        ] {
            assert!(
                GoatParser::parse(Rule::list_pattern, src).is_ok(),
                "failed: {src}"
            );
        }
        for src in ["[...a, b]", "[a, ...b, ...c]", "[1]", "[a b]"] {
            assert!(
                GoatParser::parse(Rule::list_pattern, src).is_err(),
                "accepted: {src}"
            );
        }
    }

    #[test]
    fn a_bracket_is_a_pattern_only_where_a_pattern_goes() {
        use pest::Parser;
        // Before `=` it destructures; anywhere else the same text is a literal.
        let destructure = GoatParser::parse(Rule::goat, "[a, b] = xs a").unwrap();
        assert_eq!(first_rule(destructure), Rule::destructure);
        let literal = GoatParser::parse(Rule::goat, "[a, b]").unwrap();
        assert_eq!(first_rule(literal), Rule::list);
        for src in [
            "match xs do [] then 0 [a, ...r] then a done",
            "program([a, b], {x}, y) do a done",
            "[first, ...rest] = [1, 2, 3] first",
        ] {
            assert!(GoatParser::parse(Rule::goat, src).is_ok(), "failed: {src}");
        }
    }

    fn first_rule(pairs: pest::iterators::Pairs<Rule>) -> Rule {
        pairs
            .flatten()
            .find(|p| !matches!(p.as_rule(), Rule::goat | Rule::expr))
            .unwrap()
            .as_rule()
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
    fn capitalization_does_not_change_what_a_name_is() {
        use pest::Parser;
        for name in ["circle", "Circle", "X", "matchbox", "Éclair", "éclair"] {
            assert!(GoatParser::parse(Rule::name, name).is_ok(), "{name}");
        }
    }

    #[test]
    fn tag_is_a_reserved_word_only_on_its_own() {
        use pest::Parser;
        assert!(GoatParser::parse(Rule::name, "tag").is_err());
        for name in ["tagline", "tags", "tag_"] {
            assert!(GoatParser::parse(Rule::name, name).is_ok(), "{name}");
        }
    }

    #[test]
    fn parses_tag_declarations_before_the_program() {
        use pest::Parser;
        parses_to! {
            parser: GoatParser,
            input: "tag Circle tag Square 1",
            rule: Rule::goat,
            tokens: [goat(0, 23, [
                tag_decl(0, 11, [tag_kw(0, 3), tag_case(4, 11, [name(4, 10)])]),
                tag_decl(11, 22, [tag_kw(11, 14), tag_case(15, 22, [name(15, 21)])]),
                expr(22, 23, [number(22, 23)]),
                EOI(23, 23)
            ])]
        }
        assert!(GoatParser::parse(Rule::goat, "tagCircle").is_ok());
        assert!(GoatParser::parse(Rule::goat, "tag Circle").is_ok());
        assert!(GoatParser::parse(Rule::goat, "1 tag Circle").is_err());
    }

    #[test]
    fn parses_a_grouped_tag_declaration() {
        use pest::Parser;
        parses_to! {
            parser: GoatParser,
            input: "tag T = A | B(Number)",
            rule: Rule::tag_decl,
            tokens: [tag_decl(0, 21, [
                tag_kw(0, 3),
                group_name(4, 5, [name(4, 5)]),
                tag_case(8, 10, [name(8, 9)]),
                tag_case(12, 21, [name(12, 13), type_name(14, 20)])
            ])]
        }
        for ok in [
            "tag A | B",
            "tag A(Number, String) | B",
            "tag T = A | B({x: Number, y: T}) 1",
            "tag A tag B | C a = 1",
        ] {
            assert!(GoatParser::parse(Rule::goat, ok).is_ok(), "{ok}");
        }
        for bad in ["tag", "tag A |", "tag T = ", "tag A | | B"] {
            assert!(GoatParser::parse(Rule::goat, bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn match_is_a_reserved_word() {
        use pest::Parser;
        assert!(GoatParser::parse(Rule::name, "match").is_err());
    }

    #[test]
    fn a_tag_construction_is_a_name_and_a_call() {
        parses_to! {
            parser: GoatParser,
            input: "Circle(5)",
            rule: Rule::expr,
            tokens: [expr(0, 9, [
                name(0, 6),
                call(6, 9, [arguments(7, 8, [expr(7, 8, [number(7, 8)])])])
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
    fn an_arm_may_lead_with_a_scalar_literal() {
        use pest::Parser;
        for src in ["0 then 1", "\"go\" then 1", "true then 1", "2.5 then 1"] {
            let arm = GoatParser::parse(Rule::arm, src).unwrap().next().unwrap();
            let first = arm.into_inner().next().unwrap().as_rule();
            assert_eq!(first, Rule::literal_pattern, "{src}");
        }
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
                spread(1, 5, [expr(4, 5, [name(4, 5)])]),
                field(7, 11, [name(7, 8), expr(10, 11, [number(10, 11)])])
            ])]
        }
        parses_to! {
            parser: GoatParser,
            input: "{...p}",
            rule: Rule::record,
            tokens: [record(0, 6, [spread(1, 5, [expr(4, 5, [name(4, 5)])])])]
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
                record_pattern(0, 6, [name(1, 2), name(4, 5)]),
                value(9, 10, [name(9, 10)])
            ])]
        }
        parses_to! {
            parser: GoatParser,
            input: "{x, ...rest} = p x",
            rule: Rule::destructure,
            tokens: [destructure(0, 18, [
                record_pattern(0, 12, [name(1, 2), rest_binding(4, 11, [name(7, 11)])]),
                value(15, 17, [name(15, 16)]),
                expr(17, 18, [name(17, 18)])
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
    #[test]
    fn a_semicolon_sequences_expressions() {
        parses_to! {
            parser: GoatParser,
            input: "a; b",
            rule: Rule::expr,
            tokens: [expr(0, 4, [
                name(0, 1),
                sequel(1, 4, [expr(3, 4, [name(3, 4)])])
            ])]
        }
        parses_to! {
            parser: GoatParser,
            input: "a;",
            rule: Rule::expr,
            tokens: [expr(0, 2, [name(0, 1), sequel(1, 2)])]
        }
        use pest::Parser;
        for src in [
            "f(1); g(2);",
            "x = 1; x",
            "x = 1  f(x); g(x)",
            "{a} = r; a",
            "a;;",
        ] {
            let ok = GoatParser::parse(Rule::goat, src).is_ok();
            assert_eq!(ok, src != "a;;", "{src}");
        }
    }

    #[test]
    fn without_a_semicolon_a_paren_is_a_call_and_a_minus_is_subtraction() {
        parses_to! {
            parser: GoatParser,
            input: "f(1) (2)",
            rule: Rule::expr,
            tokens: [expr(0, 8, [
                name(0, 1),
                call(1, 4, [arguments(2, 3, [expr(2, 3, [number(2, 3)])])]),
                call(5, 8, [arguments(6, 7, [expr(6, 7, [number(6, 7)])])])
            ])]
        }
        use pest::Parser;
        let pairs = GoatParser::parse(Rule::expr, "f(1) -2").unwrap();
        assert!(pairs.flatten().any(|p| p.as_rule() == Rule::minus));
        assert!(GoatParser::parse(Rule::goat, "f(1) g(2)").is_err());
    }

    #[test]
    fn and_or_not_are_operators_and_words() {
        parses_to! {
            parser: GoatParser,
            input: "not a and b or c",
            rule: Rule::expr,
            tokens: [expr(0, 16, [
                not_op(0, 3),
                name(4, 5),
                and_op(6, 9),
                name(10, 11),
                or_op(12, 14),
                name(15, 16)
            ])]
        }
        use pest::Parser;
        for name in ["nothing", "android", "order", "format", "forty", "nothing2"] {
            assert!(GoatParser::parse(Rule::name, name).is_ok(), "{name}");
        }
        for word in ["and", "or", "not", "for", "repeat", "times"] {
            assert!(GoatParser::parse(Rule::name, word).is_err(), "{word}");
        }
        for word in ["from", "to", "in"] {
            assert!(GoatParser::parse(Rule::name, word).is_ok(), "{word}");
        }
        assert!(GoatParser::parse(Rule::goat, "a andb").is_err());
        assert!(GoatParser::parse(Rule::goat, "a and(b)").is_ok());
    }

    #[test]
    fn parses_loops() {
        use pest::Parser;
        for (src, rule) in [
            ("repeat 3 times do done", Rule::repeat_loop),
            ("repeat n + 1 times do f(); g() done", Rule::repeat_loop),
            ("for i from 1 to 10 do f(i) done", Rule::count_loop),
            ("for i from a.from to a.to do done", Rule::count_loop),
            ("for x in xs do f(x) done", Rule::each_loop),
            ("for x in [1, 2] do done", Rule::each_loop),
        ] {
            let pair = GoatParser::parse(Rule::goat, src)
                .unwrap_or_else(|e| panic!("{src}: {e}"))
                .flatten()
                .find(|p| !matches!(p.as_rule(), Rule::goat | Rule::expr))
                .unwrap();
            assert_eq!(pair.as_rule(), rule, "{src}");
        }
        for src in [
            "repeat 3 do done",
            "for i from 1 do done",
            "for i 1 to 2 do done",
            "for i in do done",
            "for x in xs done",
            "for i fromm 1 to 2 do done",
        ] {
            assert!(
                GoatParser::parse(Rule::goat, src).is_err(),
                "accepted: {src}"
            );
        }
    }
}
