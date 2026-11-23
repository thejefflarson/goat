//! Fuzz target: the Rust checker and the extracted, proven inference algorithm
//! (`proofs/GoatExtract.v`) must agree on every program the fuzzer writes, in
//! acceptance and in the inferred type up to renaming of variables. The
//! algorithm runs in a long-lived child, `differential/driver.ml --serve`, one
//! corpus line in and one verdict out per program; a disagreement panics inside
//! `for_each`, so bolero shrinks it and the nightly's crash steps take over.
//!
//! Needs the driver built from the extracted sources (`differential/README.md`,
//! "The nightly fuzz"); `GOAT_W_DRIVER` is its path. `GOAT_W_PLANT=1` starts it
//! with `--plant`, which inverts every checker verdict, to see a divergence
//! caught and shrunk.

#[path = "../../checker/examples/core_corpus.rs"]
#[allow(dead_code)]
mod corpus;
#[path = "../../cli/tests/support/mod.rs"]
#[allow(dead_code)]
mod support;

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::Mutex;

struct Driver {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
}

impl Driver {
    fn spawn(plant: bool) -> Driver {
        let path = std::env::var("GOAT_W_DRIVER")
            .expect("GOAT_W_DRIVER names the built differential driver (see fuzz/README.md)");
        let mut command = Command::new(path);
        command.arg("--serve");
        if plant {
            command.arg("--plant");
        }
        let mut child = command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .expect("the driver starts");
        let stdin = child.stdin.take().expect("a piped stdin");
        let stdout = BufReader::new(child.stdout.take().expect("a piped stdout"));
        Driver {
            child,
            stdin,
            stdout,
        }
    }

    fn ask(&mut self, line: &str) -> String {
        writeln!(self.stdin, "{line}")
            .and_then(|()| self.stdin.flush())
            .expect("the driver takes a line");
        let mut reply = String::new();
        let read = self
            .stdout
            .read_line(&mut reply)
            .expect("the driver replies");
        assert!(read > 0, "the driver exited on: {line}");
        reply.trim_end().to_string()
    }
}

impl Drop for Driver {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

thread_local! {
    static DRIVER: RefCell<Option<Driver>> = const { RefCell::new(None) };
}

/// The driver's reply to a corpus line, starting the driver on first use.
fn ask_driver(line: &str) -> String {
    DRIVER.with_borrow_mut(|driver| {
        driver
            .get_or_insert_with(|| Driver::spawn(std::env::var_os("GOAT_W_PLANT").is_some()))
            .ask(line)
    })
}

/// A corpus line, split into the columns a gap's predicate reads.
struct Case<'a> {
    mode: &'a str,
    term: &'a str,
    verdict: &'a str,
    source: &'a str,
}

impl<'a> Case<'a> {
    fn parse(line: &'a str) -> Case<'a> {
        let mut columns = line.splitn(4, '\t');
        let mut column = || columns.next().expect("a corpus line has four columns");
        Case {
            mode: column(),
            term: column(),
            verdict: column(),
            source: column(),
        }
    }
}

/// A class of program the algorithm is known to refuse although the checker
/// accepts it (`docs/design/phase7-proof-plan.md`, section 3), and the stage
/// that removes the class. When the stage lands it deletes its row, and the
/// target then fails on the class.
struct Gap {
    name: &'static str,
    until: &'static str,
    covers: fn(&Case) -> bool,
}

/// Only a `w-refuses` reply is ever excused: a type that differs, or a program
/// the algorithm accepts and the checker rejects, is never a known gap. The
/// rows are tried in order and the first to match names the program.
///
/// Not rows, because the driver or the corpus reader already leave them out of
/// the comparison and count them: a recursive-type program the algorithm refuses
/// (`SKIP refused-R`, `refused-K`: #606's deep coercion and two mu types for
/// one regular tree, the row knot, a group member needing a `fold`; stage
/// 7.11), a program using a binding group's member before its last member
/// (`SplitGroup`), and every other reader skip.
const GAPS: [Gap; 0] = [];

static TALLY: Mutex<BTreeMap<String, u64>> = Mutex::new(BTreeMap::new());
const REPORT_EVERY: u64 = 5_000;

/// Counts `what` and, every `REPORT_EVERY` programs, prints the tally, so a
/// nightly log shows the target compared programs and what it set aside.
fn count(what: String) {
    let mut tally = TALLY.lock().unwrap_or_else(|e| e.into_inner());
    *tally.entry(what).or_default() += 1;
    let total: u64 = tally.values().sum();
    if total.is_multiple_of(REPORT_EVERY) {
        eprintln!("differential_checker_vs_w after {total} programs: {tally:?}");
    }
}

/// Compares one program, or does nothing when the corpus reader leaves it out.
fn compare(source: &str) {
    let line = match corpus::line(source) {
        Ok(line) => line,
        Err(skip) => return count(format!("reader skip: {}", skip.describe())),
    };
    let reply = ask_driver(&line);
    let (head, detail) = reply.split_once(' ').unwrap_or((&reply, ""));
    match head {
        "OK" => count("compared".into()),
        "SKIP" => count(format!("driver skip: {detail}")),
        "SLOW" => count("slow".into()),
        "MISMATCH" => {
            let case = Case::parse(&line);
            let refusal = detail.starts_with("w-refuses ");
            match GAPS.iter().find(|gap| refusal && (gap.covers)(&case)) {
                Some(gap) => count(format!("known gap ({}): {}", gap.until, gap.name)),
                None => panic!(
                    "the checker and W disagree ({detail})\n  mode:    {}\n  source:  {}\n  term:    {}\n  checker: {}",
                    case.mode, case.source, case.term, case.verdict
                ),
            }
        }
        _ => panic!("the driver rejected a corpus line: {reply}\n  line: {line}"),
    }
}

/// The positions of the tokens of `source` that are not whitespace: a run of
/// word characters, or one other character.
fn tokens(source: &str) -> Vec<(usize, usize)> {
    let word = |c: char| c.is_alphanumeric() || c == '_';
    let mut spans = Vec::new();
    let mut chars = source.char_indices().peekable();
    while let Some((start, c)) = chars.next() {
        if c.is_whitespace() {
            continue;
        }
        let mut end = start + c.len_utf8();
        if word(c) {
            while let Some(&(at, next)) = chars.peek() {
                if !word(next) {
                    break;
                }
                end = at + next.len_utf8();
                chars.next();
            }
        }
        spans.push((start, end));
    }
    spans
}

/// `source` with one token deleted, doubled, swapped with the next, or replaced
/// (by another word of the program or a numeral if it is a word; by another
/// punctuation mark otherwise). `at` and `with` pick the token and the
/// replacement.
fn mutate(source: &str, op: u8, at: u16, with: u8) -> String {
    let spans = tokens(source);
    if spans.is_empty() {
        return source.to_string();
    }
    let i = usize::from(at) % spans.len();
    let (start, end) = spans[i];
    let token = &source[start..end];
    let replacement = match op % 4 {
        0 => String::new(),
        1 => format!("{token} {token}"),
        2 => match spans.get(i + 1) {
            Some(&(next_start, next_end)) => {
                return format!(
                    "{}{}{}{}{}",
                    &source[..start],
                    &source[next_start..next_end],
                    &source[end..next_start],
                    token,
                    &source[next_end..]
                );
            }
            None => token.to_string(),
        },
        _ if token.chars().all(|c| c.is_alphanumeric() || c == '_') => {
            let words: Vec<_> = spans
                .iter()
                .map(|&(s, e)| &source[s..e])
                .filter(|t| t.chars().all(|c| c.is_alphanumeric() || c == '_'))
                .collect();
            if with.is_multiple_of(2) {
                words[usize::from(with / 2) % words.len()].to_string()
            } else {
                (with / 2).to_string()
            }
        }
        _ => {
            const PUNCTUATION: &[u8] = b"()+-*/<>=,.:{}";
            char::from(PUNCTUATION[usize::from(with) % PUNCTUATION.len()]).to_string()
        }
    };
    format!("{}{}{}", &source[..start], replacement, &source[end..])
}

/// A program of one of five generators: the corpus's four (typed, groups,
/// spreads, core), then the wasm differential's.
fn generated(kind: u8, tape: &[u8]) -> String {
    match kind % 5 {
        4 => support::generate(tape),
        k => corpus::generate_from_tape(k, tape),
    }
}

/// The program the fuzz input encodes. The first byte picks plain generation
/// (two inputs in three, mostly well typed, which tests the accept direction) or
/// a mutation of a generated program (mostly rejected, which tests the reject
/// direction). A generated program reads its choices from the bytes, so the
/// fuzzer mutates the choices and not a seed.
fn program(data: &[u8]) -> Option<String> {
    let (&head, rest) = data.split_first()?;
    if head % 3 == 2 {
        let (&[kind, op, lo, hi, with], tape) = rest.split_first_chunk::<5>()?;
        let base = generated(kind, tape);
        return Some(mutate(&base, op, u16::from_le_bytes([lo, hi]), with));
    }
    let (&kind, tape) = rest.split_first()?;
    Some(generated(kind, tape))
}

#[test]
fn differential_checker_vs_w() {
    bolero::check!().with_max_len(768).for_each(|data: &[u8]| {
        if let Some(source) = program(data) {
            compare(&source);
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_mutation_deletes_doubles_swaps_or_replaces_one_token() {
        assert_eq!(mutate("a + b", 0, 1, 0), "a  b");
        assert_eq!(mutate("a + b", 1, 0, 0), "a a + b");
        assert_eq!(mutate("a + b", 2, 0, 0), "+ a b");
        assert_eq!(mutate("a + b", 3, 0, 2), "b + b");
        assert_eq!(mutate("a + b", 3, 0, 7), "3 + b");
        assert_eq!(mutate("a + b", 3, 1, 0), "a ( b");
        assert_eq!(mutate("", 0, 0, 0), "");
    }

    #[test]
    fn the_generators_write_programs_the_reader_keeps() {
        let kept = (0..=255u8)
            .filter(|&seed| {
                let mut data = vec![seed % 2, seed % 5];
                data.extend((0..200u8).map(|i| i.wrapping_mul(seed).wrapping_add(seed ^ 0x5A)));
                corpus::line(&program(&data).expect("a program")).is_ok()
            })
            .count();
        assert!(kept > 128, "the reader kept only {kept} of 256 programs");
    }

    #[test]
    fn a_program_is_a_function_of_its_bytes() {
        let data = [2, 1, 1, 7, 0, 3, 9, 8, 7, 6, 5, 4];
        assert_eq!(program(&data), program(&data));
        assert_eq!(program(&[]), None);
        assert_eq!(program(&[2, 0, 0]), None);
    }

    /// The harness must see a divergence. A driver that never disagrees would
    /// pass without it, so this starts the driver with `--plant` (every checker
    /// verdict inverted) and requires `MISMATCH`.
    #[test]
    #[ignore = "needs GOAT_W_DRIVER"]
    fn a_planted_divergence_is_caught() {
        let line = corpus::line("1 + 2").expect("a program of the fragment");
        assert_eq!(Driver::spawn(false).ask(&line), "OK");
        let reply = Driver::spawn(true).ask(&line);
        assert!(reply.starts_with("MISMATCH w-accepts"), "{reply}");
    }

    #[test]
    #[ignore = "needs GOAT_W_DRIVER"]
    fn a_malformed_line_is_an_error_and_the_driver_keeps_serving() {
        let mut driver = Driver::spawn(false);
        assert!(driver.ask("not a corpus line").starts_with("ERROR"));
        assert!(driver.ask("U\t(bogus)\tOK Number\tx").starts_with("ERROR"));
        let line = corpus::line("true").expect("a program of the fragment");
        assert_eq!(driver.ask(&line), "OK");
    }
}
