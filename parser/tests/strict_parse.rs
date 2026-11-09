//! The strict parser over the repo's own sources. With nothing to compare
//! against, each input is held to what must be true of any parse: strict
//! acceptance and a clean recovery agree, and an accepted tree reproduces the
//! source with every node tiled by its pieces.

mod corpus;

use corpus::{goat_programs, rust_sources, string_literals};
use goat_parser::cst::{Child, Cst, Node};
use goat_parser::interp::{parse, parse_recovering};

fn assert_tiles(node: Node) {
    let mut at = node.span().start;
    for child in node.elements() {
        let (start, end) = match child {
            Child::Token(t) => (t.start, t.end),
            Child::Node(n) => {
                assert_tiles(n);
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

fn assert_sound(source: &str, cst: &Cst) {
    assert_eq!(cst.root().kind(), "goat");
    assert_eq!(cst.root().span(), 0..source.len(), "{source:?}");
    assert_eq!(cst.root().text(), source);
    assert_tiles(cst.root());
}

/// Whether `source` is valid goat, after checking the two readings agree.
fn check(source: &str) -> bool {
    let recovered = parse_recovering(source);
    match parse(source) {
        Ok(cst) => {
            assert!(
                recovered.diagnostics.is_empty(),
                "strict accepts what recovery flags: {source:?}"
            );
            assert_sound(source, &cst);
            true
        }
        Err(_) => {
            assert!(
                !recovered.diagnostics.is_empty(),
                "strict rejects what recovery finds clean: {source:?}"
            );
            false
        }
    }
}

#[test]
fn every_goat_file_in_the_repo_parses() {
    let programs = goat_programs();
    assert!(programs.len() >= 10, "found the examples and the prelude");
    for source in &programs {
        assert!(check(source), "a .goat file must parse");
    }
}

#[test]
fn every_prefix_of_every_goat_file_is_sound() {
    for source in goat_programs() {
        let step = (source.len() / 1000).max(1);
        for end in (0..=source.len())
            .step_by(step)
            .filter(|&i| source.is_char_boundary(i))
        {
            check(&source[..end]);
        }
    }
}

#[test]
fn every_string_literal_in_the_rust_tests_is_sound() {
    let (mut accepted, mut total) = (0, 0);
    for rust in rust_sources() {
        for literal in string_literals(&rust) {
            total += 1;
            accepted += usize::from(check(&literal));
        }
    }
    eprintln!(
        "string literals: {total} parsed, {accepted} valid goat, {} rejected",
        total - accepted
    );
    assert!(accepted > 1000, "the corpus must hold real programs");
}

#[test]
fn every_line_and_file_of_the_rust_sources_is_sound() {
    for rust in rust_sources() {
        check(&rust);
        for line in rust.lines() {
            check(line);
        }
    }
}

#[test]
fn generated_token_soups_are_sound() {
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
        accepted += usize::from(check(&source));
    }
    eprintln!("token soups: 60000 parsed, {accepted} valid");
    assert!(accepted > 500, "the generator must reach valid programs");
}
