//! Dual-run: pest is the oracle. Every source goes through both parsers and
//! must give the same tree or, when pest rejects it, be rejected too.

mod corpus;

use corpus::{goat_programs, rust_sources, string_literals};
use goat_parser::tree::{parse_cst, parse_pest};

fn assert_parity(source: &str) -> bool {
    match (parse_pest(source), parse_cst(source)) {
        (Ok(pest), Ok(cst)) => {
            assert_eq!(cst.outline(), pest.outline(), "trees differ on {source:?}");
            true
        }
        (Err(_), Err(_)) => false,
        (Ok(_), Err(e)) => panic!("the CST path rejects what pest accepts ({e}): {source:?}"),
        (Err(_), Ok(_)) => panic!("the CST path accepts what pest rejects: {source:?}"),
    }
}

#[test]
fn every_goat_file_in_the_repo_parses_to_pests_tree() {
    let programs = goat_programs();
    assert!(programs.len() >= 10, "found the examples and the prelude");
    for source in &programs {
        assert!(assert_parity(source), "a .goat file must parse");
    }
}

#[test]
fn every_prefix_of_every_goat_file_agrees() {
    for source in goat_programs() {
        let step = (source.len() / 1000).max(1);
        for end in (0..=source.len())
            .step_by(step)
            .filter(|&i| source.is_char_boundary(i))
        {
            assert_parity(&source[..end]);
        }
    }
}

#[test]
fn every_string_literal_in_the_rust_tests_agrees() {
    let (mut accepted, mut total) = (0, 0);
    for rust in rust_sources() {
        for literal in string_literals(&rust) {
            total += 1;
            accepted += usize::from(assert_parity(&literal));
        }
    }
    eprintln!(
        "string literals: {total} dual-run, {accepted} valid goat, {} rejected by both",
        total - accepted
    );
    assert!(accepted > 1000, "the corpus must hold real programs");
}

#[test]
fn every_line_and_file_of_the_rust_sources_agrees() {
    for rust in rust_sources() {
        assert_parity(&rust);
        for line in rust.lines() {
            assert_parity(line);
        }
    }
}

#[test]
fn generated_token_soups_agree() {
    const PIECES: &[&str] = &[
        "a", "b", "x", "Circle", "tag", "=", "|", "(", ")", "{", "}", "[", "]", ",", ":", ";", ".",
        "...", "+", "-", "*", "/", "//", "%", "==", "!=", "<", "<=", ">", ">=", "and", "or", "not",
        "->", "if", "then", "else", "done", "do", "match", "program", "function", "repeat",
        "times", "for", "from", "to", "in", "foreign", "true", "false", "1", "2.5", "\"s\"",
        "# c\n", " ", "\n",
    ];
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move |bound: usize| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state % bound as u64) as usize
    };
    let mut accepted = 0;
    for _ in 0..60_000 {
        let source: String = (0..1 + next(12))
            .map(|_| PIECES[next(PIECES.len())])
            .collect::<Vec<_>>()
            .join(" ");
        accepted += usize::from(assert_parity(&source));
    }
    eprintln!("token soups: 60000 dual-run, {accepted} valid");
    assert!(accepted > 500, "the generator must reach valid programs");
}
