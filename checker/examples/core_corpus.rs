//! Writes the programs of the differential test (ADR 0037, decision 6), one per
//! line, with what the Rust checker says about each:
//!
//!     MODE <TAB> SEXP <TAB> VERDICT <TAB> SOURCE
//!
//! `proofs/GoatExtract.v` extracts the proven inference algorithm, and
//! `differential/driver.ml` runs it on these lines and fails on any
//! disagreement. See `differential/README.md`.
//!
//! The programs are every goat source the repository holds (`examples/`, the
//! code blocks of `docs/llm.md`, every string literal in the checker's Rust
//! sources and tests) plus a fixed-seed generator. A program is kept when it is
//! in the core fragment of `proofs/goat_ln.ott`: numerals, booleans, functions,
//! calls, `let` of a syntactic value that does not name itself, record literals
//! with distinct labels, and field access, using only names it binds. The value
//! restriction (ADR 0027) is outside the calculus, so a `let` of anything but a
//! syntactic value is outside the fragment.
//!
//!     cargo run -q -p goat_checker --example core_corpus > corpus.tsv

use goat_checker::check_with_prelude;
use goat_checker::hir::{Expr, ExprId, ExprKind, Symbol};
use goat_checker::lower::lower;
use goat_checker::ty::{Row, Ty};
use std::collections::HashSet;
use std::fmt::Write;
use std::path::Path;

const GENERATED: usize = 4000;
const SEED: u64 = 0x9E37_79B9_7F4A_7C15;
const MAX_DEPTH: u32 = 6;

/// A term of the locally nameless core: a variable is the number of binders
/// between its use and its binder.
enum Core {
    Var(usize),
    Num(u64),
    Bool(bool),
    Abs(Box<Core>),
    App(Box<Core>, Box<Core>),
    Let(Box<Core>, Box<Core>),
    Rec(Vec<(usize, Core)>),
    Proj(Box<Core>, usize),
}

impl Core {
    fn sexp(&self, out: &mut String) {
        match self {
            Core::Var(i) => write!(out, "(b {i})").unwrap(),
            Core::Num(n) => write!(out, "(n {n})").unwrap(),
            Core::Bool(true) => out.push('t'),
            Core::Bool(false) => out.push('f'),
            Core::Abs(body) => {
                out.push_str("(abs ");
                body.sexp(out);
                out.push(')');
            }
            Core::App(f, a) => {
                out.push_str("(app ");
                f.sexp(out);
                out.push(' ');
                a.sexp(out);
                out.push(')');
            }
            Core::Let(v, b) => {
                out.push_str("(let ");
                v.sexp(out);
                out.push(' ');
                b.sexp(out);
                out.push(')');
            }
            Core::Rec(fields) => {
                out.push_str("(rec");
                for (label, value) in fields {
                    write!(out, " ({label} ").unwrap();
                    value.sexp(out);
                    out.push(')');
                }
                out.push(')');
            }
            Core::Proj(e, label) => {
                out.push_str("(proj ");
                e.sexp(out);
                write!(out, " {label})").unwrap();
            }
        }
    }
}

/// Reads lowered HIR as a core term, or says it is outside the fragment.
struct Reader {
    /// The nodes lowering marked as dot calls and takes, which pass or move a
    /// receiver and are outside the calculus.
    special: HashSet<ExprId>,
    labels: Vec<String>,
    scope: Vec<(String, Symbol)>,
    /// Cleared when a function or call has more than one parameter or argument.
    unary: bool,
}

fn is_syntactic_value(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Var { .. } | ExprKind::Func { .. } => true,
        ExprKind::Record { fields } => fields.iter().all(|(_, f)| is_syntactic_value(f)),
        _ => false,
    }
}

impl Reader {
    fn label(&mut self, name: &str) -> usize {
        match self.labels.iter().position(|l| l == name) {
            Some(at) => at,
            None => {
                self.labels.push(name.to_string());
                self.labels.len() - 1
            }
        }
    }

    fn read(&mut self, expr: &Expr) -> Option<Core> {
        if self.special.contains(&expr.id) {
            return None;
        }
        match &expr.kind {
            ExprKind::Int(n) => u64::try_from(*n)
                .ok()
                .filter(|n| *n < 1 << 30)
                .map(Core::Num),
            ExprKind::Bool(b) => Some(Core::Bool(*b)),
            ExprKind::Var { symbol, name } => {
                let at = self.scope.iter().rposition(|(n, _)| n == name)?;
                (self.scope[at].1 == *symbol).then(|| Core::Var(self.scope.len() - 1 - at))
            }
            ExprKind::Func { params, body } => {
                if params.is_empty() || params.iter().any(|p| p.name == "self") {
                    return None;
                }
                self.unary &= params.len() == 1;
                let mark = self.scope.len();
                self.scope
                    .extend(params.iter().map(|p| (p.name.clone(), p.symbol)));
                let body = self.read(body);
                self.scope.truncate(mark);
                Some(
                    params
                        .iter()
                        .fold(body?, |body, _| Core::Abs(Box::new(body))),
                )
            }
            ExprKind::App { callee, args } => {
                if args.is_empty() {
                    return None;
                }
                self.unary &= args.len() == 1;
                let callee = self.read(callee)?;
                args.iter().try_fold(callee, |callee, arg| {
                    Some(Core::App(Box::new(callee), Box::new(self.read(arg)?)))
                })
            }
            ExprKind::Let {
                symbol,
                name,
                value,
                rest: Some(rest),
            } => {
                if !is_syntactic_value(value) {
                    return None;
                }
                let value = self.read(value)?;
                self.scope.push((name.clone(), *symbol));
                let body = self.read(rest);
                self.scope.pop();
                Some(Core::Let(Box::new(value), Box::new(body?)))
            }
            ExprKind::Record { fields } => {
                let mut seen = Vec::new();
                let mut out = Vec::new();
                for (label, value) in fields {
                    if seen.contains(label) {
                        return None;
                    }
                    seen.push(label.clone());
                    let label = self.label(label);
                    out.push((label, self.read(value)?));
                }
                Some(Core::Rec(out))
            }
            ExprKind::Field { record, label } => {
                let base = self.read(record)?;
                Some(Core::Proj(Box::new(base), self.label(label)))
            }
            _ => None,
        }
    }
}

/// The type in the driver's canonical form: functions curried, record fields in
/// label order, variables numbered by first occurrence. `None` outside the
/// fragment's types.
struct Canon<'a> {
    labels: &'a [String],
    vars: Vec<u32>,
}

impl Canon<'_> {
    fn var(&mut self, v: u32) -> usize {
        match self.vars.iter().position(|w| *w == v) {
            Some(at) => at,
            None => {
                self.vars.push(v);
                self.vars.len() - 1
            }
        }
    }

    fn ty(&mut self, ty: &Ty, out: &mut String) -> Option<()> {
        match ty {
            Ty::Int => out.push_str("Number"),
            Ty::Bool => out.push_str("Bool"),
            Ty::Var(v) => write!(out, "v{}", self.var(*v)).unwrap(),
            Ty::Func(params, ret) => {
                for param in params {
                    out.push('(');
                    self.ty(param, out)?;
                    out.push_str(" -> ");
                }
                self.ty(ret, out)?;
                out.extend(std::iter::repeat_n(')', params.len()));
            }
            Ty::Record(row) => {
                let mut fields = Vec::new();
                let mut at = row;
                let tail = loop {
                    match at {
                        Row::Empty => break None,
                        Row::Var(v) => break Some(*v),
                        Row::Extend {
                            label,
                            field,
                            method,
                            rest,
                        } => {
                            if **method != goat_checker::ty::PLAIN {
                                return None;
                            }
                            let id = self.labels.iter().position(|l| l == label)?;
                            fields.push((id, &**field));
                            at = rest;
                        }
                        Row::Maybe { .. } => return None,
                    }
                };
                fields.sort_by_key(|(id, _)| *id);
                out.push('{');
                for (i, (id, field)) in fields.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    write!(out, "l{id}: ").unwrap();
                    self.ty(field, out)?;
                }
                if let Some(v) = tail {
                    out.push_str(if fields.is_empty() { "| " } else { " | " });
                    write!(out, "v{}", self.var(v)).unwrap();
                }
                out.push('}');
            }
            _ => return None,
        }
        Some(())
    }
}

/// The line for `source`, or `None` when it is not a program of the fragment.
fn line(source: &str) -> Option<String> {
    let lowered = lower(source).ok()?;
    if !lowered.errors.is_empty() {
        return None;
    }
    let mut reader = Reader {
        special: lowered
            .dot_calls
            .keys()
            .chain(lowered.takes.keys())
            .copied()
            .collect(),
        labels: Vec::new(),
        scope: Vec::new(),
        unary: true,
    };
    let core = reader.read(&lowered.root)?;
    let verdict = match check_with_prelude("", source) {
        Ok(checked) => {
            let mut canon = Canon {
                labels: &reader.labels,
                vars: Vec::new(),
            };
            let mut text = String::from("OK ");
            canon.ty(&checked.typed.root_ty, &mut text)?;
            text
        }
        Err(_) => "ERR".to_string(),
    };
    let mut sexp = String::new();
    core.sexp(&mut sexp);
    let mode = if reader.unary { 'U' } else { 'N' };
    let text = source
        .replace('\\', "\\\\")
        .replace('\n', "\\n")
        .replace('\t', "\\t");
    Some(format!("{mode}\t{sexp}\t{verdict}\t{text}"))
}

/// Every string literal of a Rust source: ordinary and raw, comments skipped.
fn string_literals(source: &str) -> Vec<String> {
    let bytes = source.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'/' if bytes.get(i + 1) == Some(&b'/') => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'/' if bytes.get(i + 1) == Some(&b'*') => {
                i += 2;
                while i + 1 < bytes.len() && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
                    i += 1;
                }
                i += 2;
            }
            b'\'' => {
                // A character literal such as '"' or '\'', not a lifetime.
                if bytes.get(i + 2) == Some(&b'\'') {
                    i += 3;
                } else if bytes.get(i + 1) == Some(&b'\\') && bytes.get(i + 3) == Some(&b'\'') {
                    i += 4;
                } else {
                    i += 1;
                }
            }
            b'r' if matches!(bytes.get(i + 1), Some(b'"' | b'#'))
                && (i == 0 || !bytes[i - 1].is_ascii_alphanumeric() && bytes[i - 1] != b'_') =>
            {
                let mut j = i + 1;
                while bytes.get(j) == Some(&b'#') {
                    j += 1;
                }
                if bytes.get(j) != Some(&b'"') {
                    i += 1;
                    continue;
                }
                let hashes = j - (i + 1);
                let start = j + 1;
                let closing = format!("\"{}", "#".repeat(hashes));
                match source[start..].find(&closing) {
                    Some(len) => {
                        out.push(source[start..start + len].to_string());
                        i = start + len + closing.len();
                    }
                    None => break,
                }
            }
            b'"' => {
                let mut text = String::new();
                let mut j = i + 1;
                while j < bytes.len() && bytes[j] != b'"' {
                    if bytes[j] == b'\\' {
                        j += 1;
                        match bytes.get(j) {
                            Some(b'n') => text.push('\n'),
                            Some(b't') => text.push('\t'),
                            Some(b'"') => text.push('"'),
                            Some(b'\\') => text.push('\\'),
                            Some(b'\'') => text.push('\''),
                            Some(b'\n') => {
                                while matches!(bytes.get(j + 1), Some(b' ' | b'\t' | b'\n')) {
                                    j += 1;
                                }
                            }
                            _ => {}
                        }
                        j += 1;
                    } else {
                        let ch = source[j..].chars().next().unwrap();
                        text.push(ch);
                        j += ch.len_utf8();
                    }
                }
                out.push(text);
                i = j + 1;
            }
            _ => i += 1,
        }
    }
    out
}

fn rust_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            rust_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

fn markdown_blocks(text: &str) -> Vec<String> {
    let mut blocks = Vec::new();
    let mut current: Option<String> = None;
    for l in text.lines() {
        match (&mut current, l.trim_end()) {
            (None, "```goat") => current = Some(String::new()),
            (Some(_), "```") => blocks.extend(current.take()),
            (Some(block), _) => {
                block.push_str(l);
                block.push('\n');
            }
            _ => {}
        }
    }
    blocks
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// How a generated expression must be wrapped where it is an operand.
#[derive(Clone, Copy, PartialEq)]
enum Shape {
    Plain,
    Let,
    Num,
    Proj,
}

/// Writes closed curried programs: unary functions, one argument per call. A
/// function binding gets a name used nowhere else, since goat lets a function
/// see itself and the functions of its block, which the core's `let` does not.
struct Gen {
    rng: Rng,
    scope: Vec<String>,
    functions: u32,
}

impl Gen {
    fn wrap(text: String, shape: Shape, parenthesise: &[Shape]) -> String {
        if parenthesise.contains(&shape) {
            format!("({text})")
        } else {
            text
        }
    }

    fn leaf(&mut self) -> (String, Shape) {
        match self.rng.below(3) {
            0 if !self.scope.is_empty() => (
                self.scope[self.rng.below(self.scope.len())].clone(),
                Shape::Plain,
            ),
            1 => (
                if self.rng.below(2) == 0 {
                    "true"
                } else {
                    "false"
                }
                .to_string(),
                Shape::Plain,
            ),
            _ => (self.rng.below(1000).to_string(), Shape::Num),
        }
    }

    fn term(&mut self, depth: u32) -> (String, Shape) {
        if depth >= MAX_DEPTH {
            return self.leaf();
        }
        let depth = depth + 1;
        match self.rng.below(10) {
            0..=2 => self.leaf(),
            3 | 4 => {
                let name = format!("v{}", self.rng.below(3));
                self.scope.push(name.clone());
                let (body, _) = self.term(depth);
                self.scope.pop();
                (format!("program({name}) do {body} done"), Shape::Plain)
            }
            5 | 6 => {
                let (callee, shape) = self.term(depth);
                let (arg, _) = self.term(depth);
                let callee = Self::wrap(callee, shape, &[Shape::Let, Shape::Num, Shape::Proj]);
                (format!("{callee}({arg})"), Shape::Plain)
            }
            7 => {
                let (value, shape) = self.term(depth);
                let is_function = value.starts_with("program(") && shape == Shape::Plain;
                let name = if is_function {
                    self.functions += 1;
                    format!("fun{}", self.functions)
                } else {
                    format!("v{}", self.rng.below(3))
                };
                self.scope.push(name.clone());
                let (body, _) = self.term(depth);
                self.scope.pop();
                let value = Self::wrap(value, shape, &[Shape::Let]);
                (format!("{name} = {value}; {body}"), Shape::Let)
            }
            8 => {
                let mut labels: Vec<u64> = Vec::new();
                for _ in 0..self.rng.below(4) {
                    let label = self.rng.next() % 5;
                    if !labels.contains(&label) {
                        labels.push(label);
                    }
                }
                let fields: Vec<String> = labels
                    .iter()
                    .map(|l| format!("lab{l}: {}", self.term(depth).0))
                    .collect();
                (format!("{{{}}}", fields.join(", ")), Shape::Plain)
            }
            _ => {
                let (base, shape) = self.term(depth);
                let base = Self::wrap(base, shape, &[Shape::Let, Shape::Num]);
                (format!("{base}.lab{}", self.rng.next() % 5), Shape::Proj)
            }
        }
    }
}

/// Programs the repository's sources may not hold: let-polymorphism, row
/// polymorphism, rejections, and calls with several arguments.
const HANDWRITTEN: &[&str] = &[
    "id = program(x) do x done\n{a: id(1), b: id(true)}",
    "get = program(r) do r.x done\n{a: get({x: 1, y: true}), b: get({x: false})}",
    "add = program(a, b) do {x: a, y: b} done\nadd(1, true)",
    "f = program(a, b) do a done\nf(1)",
    "program(r) do {a: r.x, b: r.y} done",
    "program(x) do x(x) done",
    "r = {x: 1}\nr.y",
    "twice = program(f) do program(x) do f(f(x)) done done\ntwice(program(n) do n done)(3)",
    "compose = program(f) do program(g) do program(x) do f(g(x)) done done done\ncompose",
    "k = program(x) do program(y) do x done done\nk(1)(true)",
    "program(f) do f(1) done",
    "program(f) do {a: f(1), b: f(true)} done",
    "p = {x: {y: 1}}\np.x.y",
    "program(r) do r.x.y done",
    "program(a) do {x: a, y: a} done",
    "pair = program(a, b) do {first: a, second: b} done\npair(1, true).second",
    "swap = program(p) do {first: p.second, second: p.first} done\nswap",
    "choose = program(a, b) do a done\nchoose(1, 2)",
    "apply = program(f, x) do f(x) done\napply(program(n) do n done, 1)",
];

fn main() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut sources: Vec<String> = Vec::new();

    let mut examples: Vec<_> = std::fs::read_dir(root.join("examples"))
        .expect("examples/")
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|e| e == "goat"))
        .collect();
    examples.sort();
    for path in examples {
        sources.push(std::fs::read_to_string(path).expect("an example"));
    }

    sources.extend(markdown_blocks(
        &std::fs::read_to_string(root.join("docs/llm.md")).expect("docs/llm.md"),
    ));

    let mut files = Vec::new();
    rust_files(&root.join("checker"), &mut files);
    rust_files(&root.join("parser"), &mut files);
    for path in files {
        if path.ends_with("examples/core_corpus.rs") {
            continue;
        }
        let text = std::fs::read_to_string(&path).expect("a Rust source");
        sources.extend(string_literals(&text));
    }

    sources.extend(HANDWRITTEN.iter().map(|s| s.to_string()));

    let mut gen_ = Gen {
        rng: Rng(SEED),
        scope: Vec::new(),
        functions: 0,
    };
    for _ in 0..GENERATED {
        gen_.functions = 0;
        sources.push(gen_.term(0).0);
    }

    let mut seen = HashSet::new();
    for source in sources {
        if let Some(line) = line(&source)
            && seen.insert(
                line.rsplit_once('\t')
                    .expect("a source column")
                    .0
                    .to_string(),
            )
        {
            println!("{line}");
        }
    }
}
