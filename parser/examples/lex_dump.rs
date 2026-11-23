//! Writes what `parser::lexer::lex` says of every goat source the repository
//! holds, for the differential test of the Coq lexer (`proofs/GoatLexExtract.v`
//! extracts `lex`, and `differential/lex_driver.ml` compares it with this):
//!
//!     X <TAB> S|C <TAB> LO <TAB> HI     code points of 128 and up that
//!                                       `unicode_ident` takes as `XID_Start` (S)
//!                                       or `XID_Continue` (C), as inclusive ranges
//!     L <TAB> CODE POINTS <TAB> TOKENS  a source and its tokens
//!
//! A source is its code points in decimal, separated by spaces; a token is
//! `K:START:END` for a kind letter and the code-point offsets of its span.
//! Sources are every `.goat` file of the repo, one per line of standard input
//! in the same encoding (`core_corpus --sources` writes the programs the
//! generators make), and a fixed-seed fuzz of lexer fragments that reaches the
//! corners: unterminated strings, `1e+`, `start at`, names of 255 characters,
//! non-ASCII identifiers and code points no token takes.
//!
//!     cargo run -q -p goat_parser --example lex_dump < sources.txt > lex.tsv

use goat_parser::lexer::{TokenKind, lex};
use std::collections::HashSet;
use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};
use unicode_ident::{is_xid_continue, is_xid_start};

const FUZZED: usize = 30_000;

fn kind_letter(kind: TokenKind) -> char {
    match kind {
        TokenKind::Whitespace => 'W',
        TokenKind::Comment => 'C',
        TokenKind::String => 'S',
        TokenKind::Number => 'N',
        TokenKind::Literal => 'L',
        TokenKind::Keyword => 'K',
        TokenKind::Name => 'I',
        TokenKind::Operator => 'O',
        TokenKind::Punct => 'P',
        TokenKind::Unknown => 'U',
        TokenKind::Tag => unreachable!("lex produces no tag"),
    }
}

fn ranges(out: &mut impl Write, letter: char, holds: fn(char) -> bool) {
    let mut open: Option<u32> = None;
    for code in 128..=0x11_0000u32 {
        let yes = char::from_u32(code).is_some_and(holds);
        match (yes, open) {
            (true, None) => open = Some(code),
            (false, Some(lo)) => {
                writeln!(out, "X\t{letter}\t{lo}\t{}", code - 1).unwrap();
                open = None;
            }
            _ => {}
        }
    }
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        if path.is_dir() {
            let skip = name.to_str().is_some_and(|n| {
                n.starts_with('.') || matches!(n, "target" | "node_modules" | "proofs" | "papers")
            });
            if !skip {
                walk(&path, out);
            }
        } else if path.extension().is_some_and(|e| e == "goat") {
            out.push(path);
        }
    }
}

struct Rng(u64);

impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

const FRAGMENTS: &[&str] = &[
    "if",
    "match",
    "then",
    "else",
    "done",
    "do",
    "doner",
    "start",
    "at",
    "start at",
    "startat",
    "repeat",
    "times",
    "for",
    "from",
    "to",
    "in",
    "foreign",
    "and",
    "or",
    "not",
    "return",
    "tag",
    "program",
    "function",
    "fn",
    "true",
    "false",
    "truex",
    "x",
    "y1",
    "_",
    "_x",
    "É",
    "日本",
    "Ω1",
    "1",
    "12",
    "1.",
    "1.5",
    ".5",
    "1e5",
    "1e+5",
    "1e+",
    "1e",
    "1E-2",
    "..",
    "...",
    ".",
    "5 -1",
    "+",
    "-",
    "*",
    "/",
    "//",
    "%",
    "==",
    "!=",
    "<",
    "<=",
    ">",
    ">=",
    "->",
    "::",
    ":",
    "=",
    "!",
    "(",
    ")",
    "{",
    "}",
    "[",
    "]",
    ",",
    ";",
    "|",
    "\"",
    "\"a b\"",
    "\"a\\\"b\"",
    "\"\\",
    "\\",
    "#",
    "# note",
    " ",
    "  ",
    "\t",
    "\n",
    "\r",
    "\r\n",
    "\u{a0}",
    "\u{200b}",
    "€",
    "😀",
    "\u{0}",
    "\u{301}",
    "ǅ",
    "·",
];

fn fuzzed() -> Vec<String> {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let mut out: Vec<String> = (0..FUZZED)
        .map(|_| {
            (0..1 + rng.below(40))
                .map(|_| FRAGMENTS[rng.below(FRAGMENTS.len())])
                .collect()
        })
        .collect();
    for run in [253, 254, 255, 256, 257, 300, 509, 510, 511] {
        out.push("a".repeat(run));
        out.push(format!("é{}", "é".repeat(run)));
        out.push(format!("a{}😀", "1".repeat(run)));
    }
    out
}

fn main() {
    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    ranges(&mut out, 'S', is_xid_start);
    ranges(&mut out, 'C', is_xid_continue);

    let mut sources: Vec<String> = Vec::new();
    let mut files = Vec::new();
    walk(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join(".."),
        &mut files,
    );
    files.sort();
    for path in files {
        sources.push(std::fs::read_to_string(path).expect("a goat file"));
    }
    for line in std::io::stdin().lock().lines() {
        let line = line.expect("standard input");
        sources.push(
            line.split_whitespace()
                .filter_map(|n| char::from_u32(n.parse().expect("a code point")))
                .collect(),
        );
    }
    sources.extend(fuzzed());

    let mut seen = HashSet::new();
    for source in sources.iter().filter(|s| seen.insert(s.as_str())) {
        let offsets: std::collections::HashMap<usize, usize> = source
            .char_indices()
            .map(|(byte, _)| byte)
            .chain([source.len()])
            .enumerate()
            .map(|(chars, byte)| (byte, chars))
            .collect();
        let code_points: Vec<String> = source.chars().map(|c| (c as u32).to_string()).collect();
        let tokens: Vec<String> = lex(source)
            .iter()
            .map(|t| {
                format!(
                    "{}:{}:{}",
                    kind_letter(t.kind),
                    offsets[&t.start],
                    offsets[&t.end]
                )
            })
            .collect();
        writeln!(out, "L\t{}\t{}", code_points.join(" "), tokens.join(" ")).unwrap();
    }
}
