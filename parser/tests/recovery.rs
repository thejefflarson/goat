//! Recovery on invalid input. pest stops at the first error, so these are not
//! dual-run: they hold the recovering parser to the shape ADR 0022 §3 describes,
//! and to the three properties the fuzzers also check: it never panics, every
//! byte stays in the tree, and it ends.

mod corpus;

use corpus::{goat_programs, rust_sources, string_literals};
use goat_parser::cst::{Child, Node};
use goat_parser::interp::{Recovered, parse, parse_recovering};

/// The tree as nested kinds, with a leaf's text for the nodes that hold none.
fn shape(node: Node) -> String {
    match node.kind() {
        "ERROR" => format!("ERROR({:?})", node.text()),
        "MISSING" => format!("MISSING({})", node.expected().unwrap()),
        kind => {
            let inner: Vec<String> = node.children().map(shape).collect();
            if inner.is_empty() {
                format!("{kind}({:?})", node.text())
            } else {
                format!("{kind}[{}]", inner.join(" "))
            }
        }
    }
}

/// Parse, check the invariants that hold for every input, and return the
/// tree's shape and each diagnostic's message with the text it spans.
fn recover(source: &str) -> (String, Vec<(String, String)>) {
    let recovered = parse_recovering(source);
    assert_invariants(source, &recovered);
    let diagnostics = recovered
        .diagnostics
        .iter()
        .map(|d| (d.message.clone(), source[d.span.clone()].to_string()))
        .collect();
    (shape(recovered.cst.root()), diagnostics)
}

fn assert_invariants(source: &str, recovered: &Recovered) {
    let Recovered { cst, diagnostics } = recovered;
    let text: String = cst
        .root()
        .tokens()
        .iter()
        .map(|t| &source[t.start..t.end])
        .collect();
    assert_eq!(text, source, "the tree reproduces the source");
    assert_eq!(cst.root().span(), 0..source.len());
    let mut errors = Vec::new();
    let mut missing = Vec::new();
    assert_tiles(cst.root(), &mut errors, &mut missing);

    let mut empty: Vec<_> = diagnostics
        .iter()
        .filter(|d| d.span.is_empty())
        .map(|d| d.span.clone())
        .collect();
    empty.sort_by_key(|s| s.start);
    missing.sort_by_key(|s| s.start);
    assert_eq!(
        empty, missing,
        "a zero-width diagnostic per MISSING: {source:?}"
    );
    for d in diagnostics.iter().filter(|d| !d.span.is_empty()) {
        let ok = errors.contains(&d.span) || d.message.contains("too deeply");
        assert!(ok, "{:?} spans no ERROR node: {source:?}", d.message);
    }
}

/// A node's pieces follow one another from its start to its end, so nothing in
/// the source falls between them; a `MISSING` node has no width.
fn assert_tiles(
    node: Node,
    errors: &mut Vec<std::ops::Range<usize>>,
    missing: &mut Vec<std::ops::Range<usize>>,
) {
    match node.kind() {
        "ERROR" => errors.push(node.span()),
        "MISSING" => {
            assert!(node.span().is_empty());
            missing.push(node.span());
        }
        _ => {}
    }
    let mut at = node.span().start;
    for child in node.elements() {
        let (start, end) = match child {
            Child::Token(t) => (t.start, t.end),
            Child::Node(n) => {
                assert_tiles(n, errors, missing);
                (n.span().start, n.span().end)
            }
        };
        assert_eq!(start, at, "a gap or overlap inside {}", node.kind());
        at = end;
    }
    assert_eq!(
        at,
        node.span().end,
        "{} ends where its pieces do",
        node.kind()
    );
}

fn messages(diagnostics: &[(String, String)]) -> Vec<&str> {
    diagnostics.iter().map(|(m, _)| m.as_str()).collect()
}

#[test]
fn an_unterminated_match_gets_a_missing_done() {
    let (shape, diagnostics) = recover("match x do ");
    assert_eq!(
        shape,
        "goat[expr[match_expr[expr[name(\"x\")] MISSING(done)]]]"
    );
    assert_eq!(messages(&diagnostics), ["expected `done`"]);
    let spans = parse_recovering("match x do ").diagnostics;
    assert_eq!(spans[0].span, 11..11, "where the source ends");
}

#[test]
fn a_binding_with_no_value_keeps_the_binding_after_it() {
    let (shape, diagnostics) = recover("a = ; b = 2; b");
    assert_eq!(
        shape,
        "goat[expr[declaration[name(\"a\") MISSING(value)] \
         declaration[name(\"b\") value[number(\"2\")]] name(\"b\")]]"
    );
    assert_eq!(messages(&diagnostics), ["expected value"]);
}

#[test]
fn a_dot_with_no_field_gets_a_missing_name() {
    let (shape, _) = recover("turtle.");
    assert_eq!(shape, "goat[expr[name(\"turtle\") access[MISSING(name)]]]");
}

#[test]
fn closers_the_input_never_reaches_are_inserted_in_order() {
    let (shape, diagnostics) = recover("for i from 1 to 3 do forward(i");
    assert!(shape.contains("MISSING())]] MISSING(done)]]]"), "{shape}");
    assert_eq!(messages(&diagnostics), ["expected `)`", "expected `done`"]);
    let (_, diagnostics) = recover("x = (1 + ");
    assert_eq!(messages(&diagnostics), ["expected operand", "expected `)`"]);
    let (shape, _) = recover("{a: 1, b:");
    assert!(
        shape.contains("field[name(\"b\") MISSING(expr)] MISSING(})"),
        "{shape}"
    );
    let (shape, _) = recover("tag A |");
    assert!(shape.ends_with("MISSING(tag_case)]]"), "{shape}");
}

#[test]
fn a_wrong_token_before_the_expected_one_becomes_an_error_node() {
    let (shape, diagnostics) = recover("f(a b)");
    assert_eq!(
        shape,
        "goat[expr[name(\"f\") call[arguments[expr[name(\"a\")]] ERROR(\"b\")]]]"
    );
    assert_eq!(
        diagnostics,
        [("unexpected input, expected `)`".into(), "b".into())]
    );
}

#[test]
fn recovery_resyncs_at_the_expected_keyword_and_keeps_what_follows() {
    let (shape, _) = recover("if a b then c done; z = 1; z");
    assert_eq!(
        shape,
        "goat[expr[conditional[expr[name(\"a\")] ERROR(\"b\") expr[name(\"c\")]] \
         sequel(\";\") declaration[name(\"z\") value[number(\"1\")]] name(\"z\")]]"
    );
}

#[test]
fn panic_mode_at_the_top_skips_through_the_next_semicolon() {
    let (shape, diagnostics) = recover("x = 1 \u{1} y = 2; y");
    assert_eq!(
        shape,
        "goat[expr[declaration[name(\"x\") value[number(\"1\")]]] \
         ERROR(\"\\u{1} y = 2;\") expr[name(\"y\")]]"
    );
    assert_eq!(messages(&diagnostics), ["unexpected input"]);
    let (shape, _) = recover("1 ? 2");
    assert_eq!(shape, "goat[expr[number(\"1\")] ERROR(\"? 2\")]");
    let (shape, _) = recover("; ;");
    assert_eq!(shape, "goat[ERROR(\";\") ERROR(\";\")]");
}

#[test]
fn an_anchor_keeps_an_inner_recovery_from_crossing_into_its_construct() {
    // The `)` a few tokens on belongs to the `if`'s condition, but `then` is a
    // wall: the paren is left unclosed and `then c` stays in the conditional.
    let (shape, diagnostics) = recover("if (a then c) done");
    assert_eq!(
        shape,
        "goat[expr[conditional[expr[expr[name(\"a\")] MISSING())] expr[name(\"c\")] \
         ERROR(\")\")]]]"
    );
    assert_eq!(
        messages(&diagnostics),
        ["expected `)`", "unexpected input, expected `done`"]
    );
}

#[test]
fn an_inner_error_never_consumes_the_done_of_the_match_around_it() {
    let (shape, _) = recover("match a do A then f(1 2 done; z");
    assert!(
        shape.contains("call[arguments[expr[number(\"1\")]] MISSING())]"),
        "{shape}"
    );
    assert!(shape.ends_with("sequel(\";\") name(\"z\")]]"), "{shape}");
    assert!(
        !shape.contains("MISSING(done)"),
        "the match closes: {shape}"
    );
    assert!(!shape.contains("ERROR"), "nothing swallowed: {shape}");
}

#[test]
fn a_semicolon_walls_off_a_scan_inside_a_block() {
    let (shape, _) = recover("x = (1 2; y)");
    assert!(shape.contains("MISSING())"), "{shape}");
    let (shape, _) = recover("x = 1 + ; y");
    assert!(shape.ends_with("name(\"y\")]]"), "{shape}");
}

#[test]
fn a_half_written_arm_is_kept_with_its_missing_pieces() {
    let (shape, diagnostics) = recover("match x do A then 1 B done");
    assert_eq!(
        shape,
        "goat[expr[match_expr[expr[name(\"x\")] arm[pattern[name(\"A\")] expr[number(\"1\")]] \
         arm[pattern[name(\"B\")] MISSING(then) MISSING(expr)]]]]"
    );
    assert_eq!(messages(&diagnostics), ["expected `then`", "expected expr"]);
}

#[test]
fn a_keyword_stays_a_name_where_the_grammar_wants_a_name_while_recovering() {
    let (shape, _) = recover("x = foreign \"m\" (Number");
    assert!(shape.starts_with("goat[expr[declaration[name(\"x\") value[name(\"foreign\")]]"));
}

#[test]
fn valid_input_recovers_to_the_strict_tree_with_no_diagnostics() {
    let check = |source: &str| {
        let strict = parse(source).ok()?;
        let recovered = parse_recovering(source);
        assert_eq!(recovered.diagnostics, [], "{source:?}");
        assert_eq!(
            shape(recovered.cst.root()),
            shape(strict.root()),
            "{source:?}"
        );
        Some(())
    };
    let mut valid = 0;
    for program in goat_programs() {
        assert!(check(&program).is_some());
    }
    for rust in rust_sources() {
        for literal in string_literals(&rust) {
            valid += usize::from(check(&literal).is_some());
        }
    }
    assert!(valid > 1000, "the corpus must hold real programs");
}

#[test]
fn every_prefix_of_every_program_is_lossless() {
    let mut prefixes = 0;
    for source in goat_programs() {
        let step = (source.len() / 1000).max(1);
        for end in (0..=source.len())
            .step_by(step)
            .filter(|&i| source.is_char_boundary(i))
        {
            let prefix = &source[..end];
            assert_invariants(prefix, &parse_recovering(prefix));
            prefixes += 1;
        }
    }
    eprintln!("{prefixes} prefixes, all lossless");
    assert!(prefixes > 1000);
}

#[test]
fn every_prefix_of_a_small_program_recovers_to_some_tree() {
    let source = "tag Shape = Circle(Number) | Dot\n\
                  area = program(s) do match s do Circle(r) then r * r else 0 done done\n\
                  xs = [1, 2, ...rest]; for i in xs do forward(i) done";
    let mut with_diagnostics = 0;
    for end in (0..=source.len()).filter(|&i| source.is_char_boundary(i)) {
        let prefix = &source[..end];
        let recovered = parse_recovering(prefix);
        assert_invariants(prefix, &recovered);
        with_diagnostics += usize::from(!recovered.diagnostics.is_empty());
    }
    assert!(with_diagnostics > 20, "most prefixes are broken programs");
}

#[test]
fn nesting_past_the_limit_is_one_spanned_error_and_never_overflows() {
    let on_small_stack = |source: String| {
        std::thread::Builder::new()
            .stack_size(4 << 20)
            .spawn(move || {
                let recovered = parse_recovering(&source);
                assert_invariants(&source, &recovered);
                recovered
                    .diagnostics
                    .iter()
                    .any(|d| d.message == "expression nested too deeply" && !d.span.is_empty())
            })
            .unwrap()
            .join()
            .unwrap()
    };
    let nested = |n: usize| format!("{}1{}", "(".repeat(n), ")".repeat(n));
    assert!(!on_small_stack(nested(100)));
    assert!(!on_small_stack(nested(250)));
    assert!(on_small_stack(nested(300)));
    assert!(on_small_stack(nested(100_000)));
    assert!(on_small_stack("-".repeat(100_000)));
    assert!(on_small_stack("f(".repeat(100_000)));
    assert!(on_small_stack("[".repeat(100_000)));
    assert!(on_small_stack(
        "x = foreign \"m\" \"n\" (".to_string() + &"[".repeat(100_000)
    ));
    assert!(on_small_stack("if a then ".repeat(100_000)));
    assert!(on_small_stack("(1; ".repeat(100_000)));
}

fn soups(count: usize, mut each: impl FnMut(&str)) {
    const PIECES: &[&str] = &[
        "a", "b", "x", "Circle", "tag", "=", "|", "(", ")", "{", "}", "[", "]", ",", ":", ";", ".",
        "...", "+", "-", "*", "/", "//", "%", "==", "!=", "<", "<=", ">", ">=", "and", "or", "not",
        "->", "if", "then", "else", "done", "do", "match", "program", "function", "repeat",
        "times", "for", "from", "to", "in", "foreign", "true", "false", "1", "2.5", "\"s\"",
        "\"open", "?", "\u{1}", "é", "# c\n", " ", "\n",
    ];
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move |bound: usize| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state % bound as u64) as usize
    };
    for _ in 0..count {
        let source: String = (0..1 + next(14))
            .map(|_| PIECES[next(PIECES.len())])
            .collect::<Vec<_>>()
            .join(" ");
        each(&source);
    }
}

#[test]
fn generated_token_soups_always_recover_losslessly() {
    let mut broken = 0;
    soups(60_000, |source| {
        let recovered = parse_recovering(source);
        assert_invariants(source, &recovered);
        broken += usize::from(!recovered.diagnostics.is_empty());
    });
    eprintln!("token soups: 60000 recovered, {broken} with diagnostics");
    assert!(broken > 10_000);
}

#[test]
fn a_tree_without_diagnostics_is_exactly_what_the_strict_parser_accepts() {
    soups(60_000, |source| {
        let clean = parse_recovering(source).diagnostics.is_empty();
        assert_eq!(clean, parse(source).is_ok(), "{source:?}");
    });
}

#[test]
fn arbitrary_text_never_panics_and_stays_lossless() {
    bolero::check!()
        .with_iterations(5_000)
        .with_type::<String>()
        .for_each(|source| assert_invariants(source, &parse_recovering(source)));
}

#[test]
fn arbitrary_bytes_of_goat_pieces_stay_lossless() {
    let all: Vec<&str> = vec![
        "match", "x", "do", "then", "done", "(", ")", ";", "=", "if", "else", "[", "]", "{", "}",
        "f", "1", ",", ".", ":", "+", "tag", "|", "program", "for", "in", "from", "to",
    ];
    bolero::check!()
        .with_iterations(5_000)
        .with_max_len(64)
        .for_each(|data: &[u8]| {
            let source = data
                .iter()
                .map(|&b| all[usize::from(b) % all.len()])
                .collect::<Vec<_>>()
                .join(" ");
            assert_invariants(&source, &parse_recovering(&source));
        });
}
