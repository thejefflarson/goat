//! The core fragment (ADR 0030): print a term of `proofs/goat_ln.ott` as goat
//! source, parse and lower it with the real front end, and read the result
//! back as the same term. A fixed-seed generator keeps CI deterministic.

use goat_checker::hir::{Expr, ExprKind, Symbol};
use goat_checker::lower::lower;

const CASES: usize = 10_000;
const SEED: u64 = 0x9E37_79B9_7F4A_7C15;
const MAX_DEPTH: u32 = 6;

/// A term of the Ott core: single-binder abstraction and application, a `let`
/// binding its name in the body only, records over interned labels.
#[derive(Clone, Debug, PartialEq)]
enum Term {
    Var(String),
    Num(u32),
    Bool(bool),
    Abs(String, Box<Term>),
    App(Box<Term>, Box<Term>),
    Let(String, Box<Term>, Box<Term>),
    Rec(Vec<(u32, Term)>),
    Proj(Box<Term>, u32),
}

#[derive(Clone, Copy)]
enum Style {
    /// `f(a)(b)` and `program(x) do program(y) do e done done`.
    Curried,
    /// `f(a, b)` and `program(x, y) do e done`.
    Grouped,
}

fn label_name(label: u32) -> String {
    format!("lab{label}")
}

/// A postfix chain (`.l` and calls) applies to a primary. These forms are not
/// primaries: a `let` would take the rest of the text as its scope, and a
/// number before `.` reads as a decimal point.
fn needs_parens_as_operand(term: &Term) -> bool {
    matches!(term, Term::Let(..) | Term::Num(_))
}

/// A `let`'s value is a single operand: a nested `let` there would take the
/// rest of the text as its scope.
fn needs_parens_as_value(term: &Term) -> bool {
    matches!(term, Term::Let(..))
}

fn parenthesise(term: &Term, style: Style, wrap: bool) -> String {
    let text = print(term, style);
    if wrap { format!("({text})") } else { text }
}

fn print(term: &Term, style: Style) -> String {
    match term {
        Term::Var(name) => name.clone(),
        Term::Num(n) => n.to_string(),
        Term::Bool(b) => b.to_string(),
        Term::Abs(..) => {
            let (params, body) = abstraction_group(term, style);
            format!(
                "program({}) do {} done",
                params.join(", "),
                print(body, style)
            )
        }
        Term::App(..) => {
            let (callee, args) = application_group(term, style);
            let args: Vec<String> = args.iter().map(|arg| print(arg, style)).collect();
            let callee = parenthesise(callee, style, needs_parens_as_operand(callee));
            format!("{callee}({})", args.join(", "))
        }
        Term::Let(name, value, body) => {
            let value = parenthesise(value, style, needs_parens_as_value(value));
            format!("{name} = {value}; {}", print(body, style))
        }
        Term::Rec(fields) => {
            let fields: Vec<String> = fields
                .iter()
                .map(|(label, value)| format!("{}: {}", label_name(*label), print(value, style)))
                .collect();
            format!("{{{}}}", fields.join(", "))
        }
        Term::Proj(base, label) => {
            let base = parenthesise(base, style, needs_parens_as_operand(base));
            format!("{base}.{}", label_name(*label))
        }
    }
}

/// The parameters written in one `program(...)`, outermost first, and the body
/// after them. A repeated name starts a new group: a duplicate parameter is a
/// lowering error that the curried form does not have.
fn abstraction_group(term: &Term, style: Style) -> (Vec<&str>, &Term) {
    let mut params: Vec<&str> = Vec::new();
    let mut at = term;
    while let Term::Abs(name, body) = at {
        if !params.is_empty()
            && (matches!(style, Style::Curried) || params.contains(&name.as_str()))
        {
            break;
        }
        params.push(name);
        at = body;
    }
    (params, at)
}

/// The arguments written in one call, first applied first, and the callee
/// before them.
fn application_group(term: &Term, style: Style) -> (&Term, Vec<&Term>) {
    let mut args = Vec::new();
    let mut at = term;
    while let Term::App(callee, arg) = at {
        args.push(&**arg);
        at = callee;
        if matches!(style, Style::Curried) {
            break;
        }
    }
    args.reverse();
    (at, args)
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

const VALUE_NAMES: usize = 3;
const LABELS: u32 = 5;

/// Builds closed terms. A binding whose value is a function gets a name used
/// nowhere else: goat lets a function see itself and every function of its
/// block (ADR 0003), which the Ott `let` does not (see the pinned tests).
struct Gen {
    rng: Rng,
    scope: Vec<String>,
    functions: u32,
}

impl Gen {
    fn leaf(&mut self) -> Term {
        match self.rng.below(3) {
            0 if !self.scope.is_empty() => {
                Term::Var(self.scope[self.rng.below(self.scope.len())].clone())
            }
            1 => Term::Bool(self.rng.below(2) == 0),
            _ => Term::Num(self.rng.below(1000) as u32),
        }
    }

    fn value_name(&mut self) -> String {
        format!("v{}", self.rng.below(VALUE_NAMES))
    }

    fn term(&mut self, depth: u32) -> Term {
        if depth >= MAX_DEPTH {
            return self.leaf();
        }
        let depth = depth + 1;
        match self.rng.below(10) {
            0..=2 => self.leaf(),
            3 | 4 => {
                let name = self.value_name();
                self.scope.push(name.clone());
                let body = self.term(depth);
                self.scope.pop();
                Term::Abs(name, Box::new(body))
            }
            5 | 6 => Term::App(Box::new(self.term(depth)), Box::new(self.term(depth))),
            7 => self.binding(depth),
            8 => {
                let mut labels: Vec<u32> = Vec::new();
                for _ in 0..self.rng.below(4) {
                    let label = self.rng.next() as u32 % LABELS;
                    if !labels.contains(&label) {
                        labels.push(label);
                    }
                }
                Term::Rec(labels.into_iter().map(|l| (l, self.term(depth))).collect())
            }
            _ => {
                let base = self.term(depth);
                Term::Proj(Box::new(base), self.rng.next() as u32 % LABELS)
            }
        }
    }

    fn binding(&mut self, depth: u32) -> Term {
        let value = self.term(depth);
        let name = if matches!(value, Term::Abs(..)) {
            self.functions += 1;
            format!("fun{}", self.functions)
        } else {
            self.value_name()
        };
        self.scope.push(name.clone());
        let body = self.term(depth);
        self.scope.pop();
        Term::Let(name, Box::new(value), Box::new(body))
    }
}

/// Renames the labels to 0, 1, 2, ... in the order the printed text mentions
/// them, which is the order lowering interns them.
fn intern_labels(term: &mut Term, seen: &mut Vec<u32>) {
    fn intern(label: &mut u32, seen: &mut Vec<u32>) {
        let at = seen.iter().position(|l| l == label).unwrap_or_else(|| {
            seen.push(*label);
            seen.len() - 1
        });
        *label = at as u32;
    }
    match term {
        Term::Var(_) | Term::Num(_) | Term::Bool(_) => {}
        Term::Abs(_, body) => intern_labels(body, seen),
        Term::App(callee, arg) => {
            intern_labels(callee, seen);
            intern_labels(arg, seen);
        }
        Term::Let(_, value, body) => {
            intern_labels(value, seen);
            intern_labels(body, seen);
        }
        Term::Rec(fields) => {
            for (label, value) in fields {
                intern(label, seen);
                intern_labels(value, seen);
            }
        }
        Term::Proj(base, label) => {
            intern_labels(base, seen);
            intern(label, seen);
        }
    }
}

/// Reads lowered HIR as a core term: n-ary functions and calls curried, labels
/// interned in first-occurrence order, and every variable resolved to the
/// innermost binder of its name.
struct Reader {
    labels: Vec<String>,
    scope: Vec<(String, Symbol)>,
}

impl Reader {
    fn label(&mut self, name: &str) -> u32 {
        let at = self
            .labels
            .iter()
            .position(|l| l == name)
            .unwrap_or_else(|| {
                self.labels.push(name.to_string());
                self.labels.len() - 1
            });
        at as u32
    }

    fn read(&mut self, expr: &Expr) -> Term {
        match &expr.kind {
            ExprKind::Int(n) => Term::Num(u32::try_from(*n).expect("generated numbers fit")),
            ExprKind::Bool(b) => Term::Bool(*b),
            ExprKind::Var { symbol, name } => {
                let innermost = self.scope.iter().rev().find(|(n, _)| n == name);
                assert_eq!(
                    innermost.map(|(_, s)| *s),
                    Some(*symbol),
                    "`{name}` resolves"
                );
                Term::Var(name.clone())
            }
            ExprKind::Func { params, body } => {
                let mark = self.scope.len();
                self.scope
                    .extend(params.iter().map(|p| (p.name.clone(), p.symbol)));
                let body = self.read(body);
                self.scope.truncate(mark);
                params
                    .iter()
                    .rev()
                    .fold(body, |body, p| Term::Abs(p.name.clone(), Box::new(body)))
            }
            ExprKind::App { callee, args } => {
                let callee = self.read(callee);
                args.iter().fold(callee, |callee, arg| {
                    Term::App(Box::new(callee), Box::new(self.read(arg)))
                })
            }
            ExprKind::Let {
                symbol,
                name,
                value,
                rest: Some(rest),
            } => {
                let is_function = matches!(value.kind, ExprKind::Func { .. });
                if is_function {
                    self.scope.push((name.clone(), *symbol));
                }
                let value = self.read(value);
                if !is_function {
                    self.scope.push((name.clone(), *symbol));
                }
                let body = self.read(rest);
                self.scope.pop();
                Term::Let(name.clone(), Box::new(value), Box::new(body))
            }
            ExprKind::Record { fields } => Term::Rec(
                fields
                    .iter()
                    .map(|(label, value)| {
                        let label = self.label(label);
                        (label, self.read(value))
                    })
                    .collect(),
            ),
            ExprKind::Field { record, label } => {
                let base = self.read(record);
                Term::Proj(Box::new(base), self.label(label))
            }
            other => panic!("outside the core fragment: {other:?}"),
        }
    }
}

fn lower_to_term(source: &str) -> Term {
    let lowered = lower(source).unwrap_or_else(|e| panic!("{source:?} does not parse: {e:?}"));
    assert!(
        lowered.errors.is_empty(),
        "{source:?} lowers with errors: {:?}",
        lowered.errors
    );
    Reader {
        labels: Vec::new(),
        scope: Vec::new(),
    }
    .read(&lowered.root)
}

#[test]
fn printed_core_terms_parse_back_as_the_same_term() {
    let mut builder = Gen {
        rng: Rng(SEED),
        scope: Vec::new(),
        functions: 0,
    };
    for case in 0..CASES {
        builder.functions = 0;
        let mut term = builder.term(0);
        intern_labels(&mut term, &mut Vec::new());
        for style in [Style::Curried, Style::Grouped] {
            let source = print(&term, style);
            assert_eq!(
                lower_to_term(&source),
                term,
                "case {case}, source {source:?}"
            );
        }
    }
}

#[test]
fn a_function_binding_sees_itself_unlike_the_ott_let() {
    let Term::Let(_, value, _) = lower_to_term("x = program(y) do x done; x") else {
        panic!("a let")
    };
    assert_eq!(
        *value,
        Term::Abs("y".into(), Box::new(Term::Var("x".into())))
    );
}

#[test]
fn a_function_sees_a_later_function_of_its_block_unlike_the_ott_let() {
    let source = "g = 1; f = program(y) do g done; g = program(z) do z done; f";
    let root = lower(source).expect("parses").root;
    let ExprKind::Let {
        symbol: first_g,
        rest: Some(rest),
        ..
    } = &root.kind
    else {
        panic!("a let")
    };
    let ExprKind::Let { value, .. } = &rest.kind else {
        panic!("a let")
    };
    let ExprKind::Func { body, .. } = &value.kind else {
        panic!("a function")
    };
    let ExprKind::Var { symbol, .. } = &body.kind else {
        panic!("a variable")
    };
    assert_ne!(
        symbol, first_g,
        "the body of `f` does not read the earlier `g`"
    );
}

#[test]
fn lowering_rejects_a_record_the_core_allows() {
    let errors = lower("{a: 1, a: 2}").expect("parses").errors;
    assert!(errors.iter().any(|e| e.message.contains("duplicate field")));
}
