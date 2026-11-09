//! The sources the corpus tests feed the parser: every `.goat` file in the
//! repo, and the text of every string literal in its Rust sources, which holds
//! the goat programs the tests quote.

use std::fs;
use std::path::{Path, PathBuf};

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..")
}

pub fn files_with(extension: &str) -> Vec<PathBuf> {
    fn walk(dir: &Path, extension: &str, out: &mut Vec<PathBuf>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let name = entry.file_name();
            if path.is_dir() {
                let skip = name.to_str().is_some_and(|n| {
                    n.starts_with('.')
                        || matches!(n, "target" | "node_modules" | "proofs" | "papers")
                });
                if !skip {
                    walk(&path, extension, out);
                }
            } else if path.extension().is_some_and(|e| e == extension) {
                out.push(path);
            }
        }
    }
    let mut out = Vec::new();
    walk(&repo(), extension, &mut out);
    out.sort();
    out
}

pub fn goat_programs() -> Vec<String> {
    files_with("goat")
        .iter()
        .map(|p| fs::read_to_string(p).expect("readable"))
        .collect()
}

/// The text of every string literal in some Rust source: ordinary and raw,
/// escapes resolved. A rough scan is enough, since a stray fragment is one more
/// input the parser must handle.
pub fn string_literals(rust: &str) -> Vec<String> {
    let chars: Vec<char> = rust.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        match chars[i] {
            '/' if chars.get(i + 1) == Some(&'/') => {
                while i < chars.len() && chars[i] != '\n' {
                    i += 1;
                }
            }
            '\'' if chars.get(i + 2) == Some(&'\'') => i += 3,
            '\'' if chars.get(i + 1) == Some(&'\\') && chars.get(i + 3) == Some(&'\'') => i += 4,
            'r' if matches!(chars.get(i + 1), Some('"' | '#'))
                && (i == 0 || !chars[i - 1].is_alphanumeric()) =>
            {
                let hashes = chars[i + 1..].iter().take_while(|&&c| c == '#').count();
                if chars.get(i + 1 + hashes) != Some(&'"') {
                    i += 1;
                    continue;
                }
                let start = i + 2 + hashes;
                let close: Vec<char> = std::iter::once('"')
                    .chain(std::iter::repeat_n('#', hashes))
                    .collect();
                let Some(len) = chars[start..].windows(close.len()).position(|w| w == close) else {
                    break;
                };
                out.push(chars[start..start + len].iter().collect());
                i = start + len + close.len();
            }
            '"' => {
                let mut text = String::new();
                i += 1;
                while i < chars.len() && chars[i] != '"' {
                    if chars[i] != '\\' {
                        text.push(chars[i]);
                        i += 1;
                        continue;
                    }
                    i += 1;
                    match chars.get(i) {
                        Some('n') => text.push('\n'),
                        Some('t') => text.push('\t'),
                        Some('r') => text.push('\r'),
                        Some('0') => text.push('\0'),
                        Some('\n') => {
                            while chars.get(i + 1).is_some_and(|c| c.is_whitespace()) {
                                i += 1;
                            }
                        }
                        Some(&c) => text.push(c),
                        None => {}
                    }
                    i += 1;
                }
                out.push(text);
                i += 1;
            }
            _ => i += 1,
        }
    }
    out
}

pub fn rust_sources() -> Vec<String> {
    files_with("rs")
        .iter()
        .map(|p| fs::read_to_string(p).expect("readable"))
        .collect()
}
