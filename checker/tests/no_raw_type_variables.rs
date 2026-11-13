//! A diagnostic is read by a child, so it never shows an internal type
//! variable such as `t36`. The corpus is every program the docs and the checker
//! tests mention, plus the programs that once leaked one.

use goat_checker::check;
use std::fs;
use std::path::Path;

fn leaks_variable(text: &str) -> bool {
    let bytes = text.as_bytes();
    let is_word = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    (0..bytes.len()).any(|i| {
        bytes[i] == b't'
            && (i == 0 || !is_word(bytes[i - 1]))
            && bytes[i + 1..].first().is_some_and(u8::is_ascii_digit)
            && bytes[i + 1..]
                .iter()
                .find(|b| !b.is_ascii_digit())
                .is_none_or(|b| !is_word(*b))
    })
}

fn rendered(source: &str) -> Vec<String> {
    match check(source) {
        Ok(_) => Vec::new(),
        Err(errors) => errors
            .iter()
            .flat_map(|e| {
                let notes = e.labels.iter().map(|label| label.message.clone());
                std::iter::once(e.message.clone()).chain(notes)
            })
            .collect(),
    }
}

fn assert_clean(source: &str) {
    for text in rendered(source) {
        assert!(
            !leaks_variable(&text),
            "raw type variable in:\n{text}\nfor program:\n{source}"
        );
    }
}

/// The text of every ordinary `"..."` literal in a Rust file.
fn string_literals(code: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut chars = code.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '/' && chars.peek() == Some(&'/') {
            for c in chars.by_ref() {
                if c == '\n' {
                    break;
                }
            }
        } else if c == '\'' {
            if chars.peek() == Some(&'\\') {
                chars.next();
                chars.next();
            } else {
                chars.next();
            }
            if chars.peek() == Some(&'\'') {
                chars.next();
            }
        } else if c == '"' {
            let mut text = String::new();
            while let Some(c) = chars.next() {
                match c {
                    '"' => break,
                    '\\' => match chars.next() {
                        Some('n') => text.push('\n'),
                        Some('"') => text.push('"'),
                        Some('\\') => text.push('\\'),
                        Some('\n') => {
                            while chars.peek().is_some_and(|c| c.is_whitespace()) {
                                chars.next();
                            }
                        }
                        _ => {}
                    },
                    c => text.push(c),
                }
            }
            out.push(text);
        }
    }
    out
}

#[test]
fn the_programs_that_once_leaked_a_variable_are_clean() {
    for source in [
        "h = program(r) do if true then r.g else h done done  1",
        "f = program(x) do x(x) done  1",
        "f = program(x) do if true then x else {a: x} done done  1",
        "f = program(x) do if true then x else program() do x done done done  1",
        "f = program(r) do r.x + 1 done  f(true)",
        "f = program(r) do r.x + 1 done  f({x: \"a\"}) ",
        "f = program(r) do r.x end done  1",
        "f = program(r) do 1 + r done  f({x: 1})",
        "f = program(r) do r.x + 1 done  g = program(r) do f(r) + r done  1",
    ] {
        assert_clean(source);
    }
}

#[test]
fn a_cycle_names_how_the_value_contains_itself() {
    let text = rendered("h = program(r) do if true then r.g else h done done  1").join("\n");
    assert!(
        text.contains(
            "this value would have to contain itself (through its argument, then its `g` field)"
        ),
        "{text}"
    );
    let text = rendered("f = program(x) do if true then x else {a: x} done done  1").join("\n");
    assert!(text.contains("through its `a` field"), "{text}");
    let text = rendered("f = program(x) do if true then x else program() do x done done done  1")
        .join("\n");
    assert!(text.contains("through its result"), "{text}");
}

#[test]
fn an_open_record_prints_its_known_fields_and_an_ellipsis() {
    let text = rendered("f = program(r) do r.x + 1 done  f(true)").join("\n");
    assert!(text.contains("{x: Number, …}"), "{text}");
}

#[test]
fn one_variable_gets_one_letter_across_a_message() {
    let text = rendered("f = program(x) do x(x) done  1").join("\n");
    assert!(!leaks_variable(&text), "{text}");
}

#[test]
fn the_docs_and_the_checker_tests_never_leak_a_variable() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let doc = fs::read_to_string(root.join("../docs/llm.md")).unwrap();
    let mut block = String::new();
    let mut inside = false;
    for line in doc.lines() {
        match (inside, line.trim_end()) {
            (false, "```goat" | "```goat error") => inside = true,
            (true, "```") => {
                assert_clean(&block);
                block.clear();
                inside = false;
            }
            (true, text) => {
                block.push_str(text);
                block.push('\n');
            }
            _ => {}
        }
    }

    let mut files: Vec<_> = fs::read_dir(root.join("tests"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "rs"))
        .collect();
    files.push(root.join("src/lib.rs"));
    files.push(root.join("src/infer.rs"));
    let mut tried = 0;
    for path in files {
        for literal in string_literals(&fs::read_to_string(path).unwrap()) {
            if literal.len() > 8 && literal.len() < 4000 {
                tried += 1;
                assert_clean(&literal);
            }
        }
    }
    assert!(tried > 500, "only {tried} literals tried");
}
