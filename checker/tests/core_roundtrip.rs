//! The core fragment (ADR 0030): print a term of `proofs/goat_ln.ott` as goat
//! source, parse and lower it with the real front end, and read the result
//! back as the same term. The terms cover strings, `Float` literals, `if` with
//! and without an `else`, one operator between two operands, and recursive
//! groups of functions, the spread `{...(base), l: v}`, and a dot call on a name
//! or a path of field accesses. A fixed-seed
//! generator keeps CI deterministic.

use goat_checker::hir::{BinOp, Expr, ExprKind, Symbol};
use goat_checker::lower::{RECEIVER_NAME, lower};

const CASES: usize = 10_000;
const SEED: u64 = 0x9E37_79B9_7F4A_7C15;
const MAX_DEPTH: u32 = 6;

/// A term of the Ott core: single-binder abstraction and application, a `let`
/// binding its name in the body only, records over interned labels, and a
/// recursive group (`Letrec`): its members are functions that see every member
/// of the group and the body sees them too.
#[derive(Clone, Debug, PartialEq)]
enum Term {
    Var(String),
    Num(u32),
    /// A `Float` literal `d.5`: the payload is the part before the point.
    Dec(u32),
    Bool(bool),
    Str(&'static str),
    Abs(String, Box<Term>),
    App(Box<Term>, Box<Term>),
    Let(String, Box<Term>, Box<Term>),
    Rec(Vec<(u32, Term)>),
    /// `{...(base), l: v}`: the base is parenthesised so that a name there is
    /// not the rest binding of a record pattern.
    Spread(Box<Term>, u32, Box<Term>),
    Proj(Box<Term>, u32),
    If(Box<Term>, Box<Term>, Box<Term>),
    /// `if c then t done`: the missing branch is the unit value.
    When(Box<Term>, Box<Term>),
    Bin(Box<Term>, BinOp, Box<Term>),
    Letrec(Vec<(String, Term)>, Box<Term>),
}

const STRINGS: [&str; 3] = ["", "hi", "a # b"];

const OPERATORS: [BinOp; 12] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::Div,
    BinOp::FloorDiv,
    BinOp::Mod,
    BinOp::Lt,
    BinOp::Lte,
    BinOp::Gt,
    BinOp::Gte,
    BinOp::Eq,
    BinOp::Ne,
];

fn operator_text(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::FloorDiv => "//",
        BinOp::Mod => "%",
        BinOp::Lt => "<",
        BinOp::Lte => "<=",
        BinOp::Gt => ">",
        BinOp::Gte => ">=",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
    }
}

fn operator_constructor(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "bop_add",
        BinOp::Sub => "bop_sub",
        BinOp::Mul => "bop_mul",
        BinOp::Div => "bop_div",
        BinOp::FloorDiv => "bop_fdiv",
        BinOp::Mod => "bop_rem",
        BinOp::Lt => "bop_lt",
        BinOp::Lte => "bop_lte",
        BinOp::Gt => "bop_gt",
        BinOp::Gte => "bop_gte",
        BinOp::Eq => "bop_eq",
        BinOp::Ne => "bop_ne",
    }
}

#[derive(Clone, Copy)]
enum Style {
    /// `f(a)(b)` and `program(x) do program(y) do e done done`.
    Curried,
    /// `f(a, b)` and `program(x, y) do e done`.
    Grouped,
    /// `Grouped`, writing `p.l(a)` for `(p.l)(p, a)` when `p` is a name or a
    /// path of field accesses.
    Dot,
}

impl Style {
    fn curried(self) -> bool {
        matches!(self, Style::Curried)
    }
}

fn label_name(label: u32) -> String {
    format!("lab{label}")
}

/// A postfix chain (`.l` and calls) applies to a primary. These forms are not
/// primaries: a `let` would take the rest of the text as its scope, a number
/// before `.` reads as a decimal point, and an operation would take the call
/// or the field as the operand of its own right-hand side.
fn needs_parens_as_operand(term: &Term) -> bool {
    matches!(
        term,
        Term::Let(..) | Term::Letrec(..) | Term::Num(_) | Term::Dec(_) | Term::Bin(..)
    )
}

/// An operand of an operator is a chain: a `let` or another operation is
/// parenthesised, because a run of operators is outside the fragment.
fn needs_parens_as_operator_operand(term: &Term) -> bool {
    matches!(term, Term::Let(..) | Term::Letrec(..) | Term::Bin(..))
}

/// A `let`'s value is a single operand: a nested `let` there would take the
/// rest of the text as its scope, and a bare function would make the binding a
/// member of the block's recursive group (ADR 0003) instead of a plain `let`.
fn needs_parens_as_value(term: &Term) -> bool {
    matches!(term, Term::Let(..) | Term::Letrec(..) | Term::Abs(..))
}

/// A name or a path of field accesses: the receivers a dot call repeats.
fn is_path(term: &Term) -> bool {
    match term {
        Term::Var(_) => true,
        Term::Proj(base, _) => is_path(base),
        _ => false,
    }
}

/// A projection in callee position is parenthesised: `r.f(x)` passes `r`.
fn needs_parens_as_callee(term: &Term) -> bool {
    needs_parens_as_operand(term) || matches!(term, Term::Proj(..))
}

fn parenthesise(term: &Term, style: Style, wrap: bool) -> String {
    let text = print(term, style);
    if wrap { format!("({text})") } else { text }
}

fn print(term: &Term, style: Style) -> String {
    match term {
        Term::Var(name) => name.clone(),
        Term::Num(n) => n.to_string(),
        Term::Dec(d) => format!("{d}.5"),
        Term::Bool(b) => b.to_string(),
        Term::Str(text) => format!("\"{text}\""),
        Term::When(cond, then_branch) => format!(
            "if {} then {} done",
            print(cond, style),
            print(then_branch, style)
        ),
        Term::Letrec(members, body) => {
            let members: String = members
                .iter()
                .map(|(name, function)| format!("{name} = {}; ", print(function, style)))
                .collect();
            format!("{members}{}", print(body, style))
        }
        Term::If(cond, then_branch, else_branch) => format!(
            "if {} then {} else {} done",
            print(cond, style),
            print(then_branch, style),
            print(else_branch, style)
        ),
        Term::Bin(lhs, op, rhs) => {
            let lhs = parenthesise(lhs, style, needs_parens_as_operator_operand(lhs));
            let rhs = parenthesise(rhs, style, needs_parens_as_operator_operand(rhs));
            format!("{lhs} {} {rhs}", operator_text(*op))
        }
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
            if let (Style::Dot, Term::Proj(base, label), Some((first, rest))) =
                (style, callee, args.split_first())
                && is_path(base)
                && **base == **first
                && !rest.is_empty()
            {
                let rest: Vec<String> = rest.iter().map(|arg| print(arg, style)).collect();
                return format!(
                    "{}.{}({})",
                    print(base, style),
                    label_name(*label),
                    rest.join(", ")
                );
            }
            let args: Vec<String> = args.iter().map(|arg| print(arg, style)).collect();
            let callee = parenthesise(callee, style, needs_parens_as_callee(callee));
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
        Term::Spread(base, label, value) => format!(
            "{{...({}), {}: {}}}",
            print(base, style),
            label_name(*label),
            print(value, style)
        ),
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
        if !params.is_empty() && (style.curried() || params.contains(&name.as_str())) {
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
        if style.curried() {
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
    /// Whether to generate recursive groups. The Coq printer does not write
    /// them, so the printer table is built without.
    groups: bool,
}

impl Gen {
    fn leaf(&mut self) -> Term {
        match self.rng.below(5) {
            0 if !self.scope.is_empty() => {
                Term::Var(self.scope[self.rng.below(self.scope.len())].clone())
            }
            1 => Term::Bool(self.rng.below(2) == 0),
            2 => Term::Str(STRINGS[self.rng.below(STRINGS.len())]),
            3 => Term::Dec(self.rng.below(1000) as u32),
            _ => Term::Num(self.rng.below(1000) as u32),
        }
    }

    /// A name in scope with up to two field accesses after it, or a number
    /// when nothing is in scope.
    fn path(&mut self) -> Term {
        if self.scope.is_empty() {
            return Term::Num(self.rng.below(1000) as u32);
        }
        let mut path = Term::Var(self.scope[self.rng.below(self.scope.len())].clone());
        for _ in 0..self.rng.below(3) {
            path = Term::Proj(Box::new(path), self.rng.next() as u32 % LABELS);
        }
        path
    }

    fn value_name(&mut self) -> String {
        format!("v{}", self.rng.below(VALUE_NAMES))
    }

    fn term(&mut self, depth: u32) -> Term {
        if depth >= MAX_DEPTH {
            return self.leaf();
        }
        let depth = depth + 1;
        match self.rng.below(16) {
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
            9 => {
                let base = self.term(depth);
                Term::Proj(Box::new(base), self.rng.next() as u32 % LABELS)
            }
            15 => {
                let receiver = self.path();
                let method =
                    Term::Proj(Box::new(receiver.clone()), self.rng.next() as u32 % LABELS);
                let called = Term::App(Box::new(method), Box::new(receiver));
                Term::App(Box::new(called), Box::new(self.term(depth)))
            }
            13 => {
                let base = self.term(depth);
                let label = self.rng.next() as u32 % LABELS;
                Term::Spread(Box::new(base), label, Box::new(self.term(depth)))
            }
            10 => Term::If(
                Box::new(self.term(depth)),
                Box::new(self.term(depth)),
                Box::new(self.term(depth)),
            ),
            11 => Term::When(Box::new(self.term(depth)), Box::new(self.term(depth))),
            12 if self.groups => self.group(depth),
            _ => {
                let op = OPERATORS[self.rng.below(OPERATORS.len())];
                Term::Bin(Box::new(self.term(depth)), op, Box::new(self.term(depth)))
            }
        }
    }

    /// Members named `g<n>` (a name used nowhere else), each a function over
    /// one parameter that may call any member, itself included.
    fn group(&mut self, depth: u32) -> Term {
        let mark = self.scope.len();
        let names: Vec<String> = (0..1 + self.rng.below(3))
            .map(|_| {
                self.functions += 1;
                format!("g{}", self.functions)
            })
            .collect();
        self.scope.extend(names.iter().cloned());
        let members = names
            .into_iter()
            .map(|name| {
                let param = self.value_name();
                self.scope.push(param.clone());
                let body = self.term(depth);
                self.scope.pop();
                (name, Term::Abs(param, Box::new(body)))
            })
            .collect();
        let body = self.term(depth);
        self.scope.truncate(mark);
        Term::Letrec(members, Box::new(body))
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
        Term::Var(_) | Term::Num(_) | Term::Dec(_) | Term::Bool(_) | Term::Str(_) => {}
        Term::If(cond, then_branch, else_branch) => {
            intern_labels(cond, seen);
            intern_labels(then_branch, seen);
            intern_labels(else_branch, seen);
        }
        Term::When(cond, then_branch) => {
            intern_labels(cond, seen);
            intern_labels(then_branch, seen);
        }
        Term::Letrec(members, body) => {
            for (_, function) in members {
                intern_labels(function, seen);
            }
            intern_labels(body, seen);
        }
        Term::Bin(lhs, _, rhs) => {
            intern_labels(lhs, seen);
            intern_labels(rhs, seen);
        }
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
        Term::Spread(base, label, value) => {
            intern_labels(base, seen);
            intern(label, seen);
            intern_labels(value, seen);
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

    /// A function binding opens its block's recursive group: the function
    /// bindings that follow it in a run are in scope before any body is read,
    /// itself included (ADR 0003).
    fn bind_group(&mut self, first: &Expr) {
        let mut at = first;
        while let ExprKind::Let {
            symbol,
            name,
            value,
            rest: Some(rest),
        } = &at.kind
        {
            if !matches!(value.kind, ExprKind::Func { .. }) {
                break;
            }
            self.scope.push((name.clone(), *symbol));
            at = rest;
        }
    }

    fn read(&mut self, expr: &Expr) -> Term {
        match &expr.kind {
            ExprKind::Int(n) => Term::Num(u32::try_from(*n).expect("generated numbers fit")),
            ExprKind::Float(f) => Term::Dec((*f - 0.5) as u32),
            ExprKind::Bool(b) => Term::Bool(*b),
            ExprKind::Str(text) => Term::Str(
                STRINGS
                    .into_iter()
                    .find(|s| s == text)
                    .expect("generated strings come from the table"),
            ),
            ExprKind::If {
                cond,
                then_branch,
                else_branch: Some(else_branch),
            } => Term::If(
                Box::new(self.read(cond)),
                Box::new(self.read(then_branch)),
                Box::new(self.read(else_branch)),
            ),
            ExprKind::If {
                cond,
                then_branch,
                else_branch: None,
            } => Term::When(Box::new(self.read(cond)), Box::new(self.read(then_branch))),
            ExprKind::Bin { op, lhs, rhs } => {
                Term::Bin(Box::new(self.read(lhs)), *op, Box::new(self.read(rhs)))
            }
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
                let mark = self.scope.len();
                let is_function = matches!(value.kind, ExprKind::Func { .. });
                if is_function && !self.scope.iter().any(|(_, bound)| bound == symbol) {
                    self.bind_group(expr);
                }
                let value = self.read(value);
                if !is_function {
                    self.scope.push((name.clone(), *symbol));
                }
                let body = self.read(rest);
                self.scope.truncate(mark);
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
            ExprKind::Spread { base, fields } => {
                let base = self.read(base);
                fields.iter().fold(base, |nest, (label, value)| {
                    let label = self.label(label);
                    Term::Spread(Box::new(nest), label, Box::new(self.read(value)))
                })
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
        groups: true,
    };
    for case in 0..CASES {
        builder.functions = 0;
        let mut term = builder.term(0);
        intern_labels(&mut term, &mut Vec::new());
        let expected = ungroup(&term);
        for style in [Style::Curried, Style::Grouped, Style::Dot] {
            let source = print(&term, style);
            assert_eq!(
                lower_to_term(&source),
                expected,
                "case {case}, source {source:?}"
            );
        }
    }
}

/// A recursive group lowers to the chain of its function bindings: the group is
/// name resolution, so the read-back is the `let` chain, with every name read
/// as the member it names (`Reader` checks the resolution).
fn ungroup(term: &Term) -> Term {
    let boxed = |t: &Term| Box::new(ungroup(t));
    match term {
        Term::Var(_) | Term::Num(_) | Term::Dec(_) | Term::Bool(_) | Term::Str(_) => term.clone(),
        Term::Abs(name, body) => Term::Abs(name.clone(), boxed(body)),
        Term::App(f, a) => Term::App(boxed(f), boxed(a)),
        Term::Let(name, v, b) => Term::Let(name.clone(), boxed(v), boxed(b)),
        Term::Rec(fields) => Term::Rec(fields.iter().map(|(l, t)| (*l, ungroup(t))).collect()),
        Term::Proj(base, label) => Term::Proj(boxed(base), *label),
        Term::Spread(base, label, value) => Term::Spread(boxed(base), *label, boxed(value)),
        Term::If(c, t, e) => Term::If(boxed(c), boxed(t), boxed(e)),
        Term::When(c, t) => Term::When(boxed(c), boxed(t)),
        Term::Bin(a, op, b) => Term::Bin(boxed(a), *op, boxed(b)),
        Term::Letrec(members, body) => members.iter().rev().fold(ungroup(body), |rest, (n, f)| {
            Term::Let(n.clone(), boxed(f), Box::new(rest))
        }),
    }
}

#[test]
fn a_dot_call_reads_back_as_the_application_that_passes_the_record() {
    let var = |name: &str| Term::Var(name.to_string());
    let id = Term::Abs("s".into(), Box::new(var("s")));
    let call = |args: Vec<Term>| {
        let method = Term::Proj(Box::new(var("x")), 0);
        let applied = args
            .into_iter()
            .fold(method, |f, a| Term::App(Box::new(f), Box::new(a)));
        Term::Let(
            "x".into(),
            Box::new(Term::Rec(vec![(0, id.clone())])),
            Box::new(applied),
        )
    };
    let dotted = call(vec![var("x"), Term::Num(1)]);
    assert_eq!(
        print(&dotted, Style::Dot),
        "x = {lab0: program(s) do s done}; x.lab0(1)"
    );
    assert_eq!(lower_to_term(&print(&dotted, Style::Dot)), dotted);
    let stored = call(vec![Term::Num(1)]);
    assert_eq!(
        print(&stored, Style::Dot),
        "x = {lab0: program(s) do s done}; (x.lab0)(1)"
    );
    assert_eq!(lower_to_term(&print(&stored, Style::Dot)), stored);
}

#[test]
fn a_dot_call_repeats_a_path_receiver_and_binds_any_other_once() {
    let var = |name: &str| Term::Var(name.to_string());
    let proj = |base: Term, label: u32| Term::Proj(Box::new(base), label);
    let app = |f: Term, a: Term| Term::App(Box::new(f), Box::new(a));
    let id = || Term::Abs("s".into(), Box::new(var("s")));
    let bind = |name: &str, value: Term, body: Term| {
        Term::Let(name.into(), Box::new(value), Box::new(body))
    };

    let on_path = bind(
        "x",
        Term::Rec(vec![(0, Term::Rec(vec![(1, id())]))]),
        app(
            app(proj(proj(var("x"), 0), 1), proj(var("x"), 0)),
            Term::Num(1),
        ),
    );
    assert_eq!(
        lower_to_term("x = {lab0: {lab1: program(s) do s done}}; x.lab0.lab1(1)"),
        on_path
    );

    let hidden = || var(RECEIVER_NAME);
    let on_record = bind(
        RECEIVER_NAME,
        Term::Rec(vec![(0, id())]),
        app(app(proj(hidden(), 0), hidden()), Term::Num(1)),
    );
    assert_eq!(
        lower_to_term("{lab0: program(s) do s done}.lab0(1)"),
        on_record
    );

    let on_call = bind(
        "f",
        Term::Abs("a".into(), Box::new(var("a"))),
        bind(
            RECEIVER_NAME,
            app(var("f"), Term::Num(1)),
            app(app(proj(hidden(), 0), hidden()), Term::Num(2)),
        ),
    );
    assert_eq!(
        lower_to_term("f = program(a) do a done; f(1).lab0(2)"),
        on_call
    );

    let taken = bind(
        "x",
        Term::Rec(vec![(0, id())]),
        app(proj(var("x"), 0), Term::Num(1)),
    );
    assert_eq!(
        lower_to_term("x = {lab0: program(s) do s done}; x::lab0(1)"),
        taken
    );
}

/// The terms the Coq printer is checked against (proofs/GoatPrinterTable.v).
const TABLE_CASES: usize = 200;
const TABLE_PATH: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../proofs/GoatPrinterTable.v");

/// Renames every binder to `v<depth>`, depth counting the binders around it:
/// the names the Coq printer gives them.
fn canonical(term: &Term, scope: &mut Vec<(String, String)>) -> Term {
    match term {
        Term::Var(name) => {
            let (_, canon) = scope
                .iter()
                .rev()
                .find(|(orig, _)| orig == name)
                .expect("generated terms are closed");
            Term::Var(canon.clone())
        }
        Term::Num(_) | Term::Dec(_) | Term::Bool(_) | Term::Str(_) => term.clone(),
        Term::If(cond, then_branch, else_branch) => Term::If(
            Box::new(canonical(cond, scope)),
            Box::new(canonical(then_branch, scope)),
            Box::new(canonical(else_branch, scope)),
        ),
        Term::When(cond, then_branch) => Term::When(
            Box::new(canonical(cond, scope)),
            Box::new(canonical(then_branch, scope)),
        ),
        Term::Letrec(..) => unreachable!("the printer table has no recursive group"),
        Term::Bin(lhs, op, rhs) => Term::Bin(
            Box::new(canonical(lhs, scope)),
            *op,
            Box::new(canonical(rhs, scope)),
        ),
        Term::Abs(name, body) => {
            let canon = format!("v{}", scope.len());
            scope.push((name.clone(), canon.clone()));
            let body = canonical(body, scope);
            scope.pop();
            Term::Abs(canon, Box::new(body))
        }
        Term::App(callee, arg) => Term::App(
            Box::new(canonical(callee, scope)),
            Box::new(canonical(arg, scope)),
        ),
        Term::Let(name, value, body) => {
            let value = canonical(value, scope);
            let canon = format!("v{}", scope.len());
            scope.push((name.clone(), canon.clone()));
            let body = canonical(body, scope);
            scope.pop();
            Term::Let(canon, Box::new(value), Box::new(body))
        }
        Term::Rec(fields) => Term::Rec(
            fields
                .iter()
                .map(|(label, value)| (*label, canonical(value, scope)))
                .collect(),
        ),
        Term::Spread(base, label, value) => Term::Spread(
            Box::new(canonical(base, scope)),
            *label,
            Box::new(canonical(value, scope)),
        ),
        Term::Proj(base, label) => Term::Proj(Box::new(canonical(base, scope)), *label),
    }
}

/// The term as a locally nameless Coq `exp`: a variable is the number of
/// binders between it and its own.
fn coq_term(term: &Term, scope: &mut Vec<String>) -> String {
    match term {
        Term::Var(name) => {
            let index = scope
                .iter()
                .rev()
                .position(|n| n == name)
                .expect("generated terms are closed");
            format!("(e_fvar_b {index})")
        }
        Term::Num(n) => format!("(e_num {n})"),
        Term::Dec(d) => format!("(e_dec {d})"),
        Term::Bool(true) => "e_true".into(),
        Term::Bool(false) => "e_false".into(),
        Term::Str(_) => "(e_str [])".into(),
        Term::If(cond, then_branch, else_branch) => format!(
            "(e_ite {} {} {})",
            coq_term(cond, scope),
            coq_term(then_branch, scope),
            coq_term(else_branch, scope)
        ),
        Term::When(cond, then_branch) => format!(
            "(e_ite {} {} e_unit)",
            coq_term(cond, scope),
            coq_term(then_branch, scope)
        ),
        Term::Letrec(..) => unreachable!("the printer table has no recursive group"),
        Term::Bin(lhs, op, rhs) => format!(
            "(e_bin {} {} {})",
            coq_term(lhs, scope),
            operator_constructor(*op),
            coq_term(rhs, scope)
        ),
        Term::Abs(name, body) => {
            scope.push(name.clone());
            let body = coq_term(body, scope);
            scope.pop();
            format!("(e_abs {body})")
        }
        Term::App(callee, arg) => {
            format!(
                "(e_app {} {})",
                coq_term(callee, scope),
                coq_term(arg, scope)
            )
        }
        Term::Let(name, value, body) => {
            let value = coq_term(value, scope);
            scope.push(name.clone());
            let body = coq_term(body, scope);
            scope.pop();
            format!("(e_let {value} {body})")
        }
        Term::Rec(fields) => {
            let mut list = String::from("fs_nil");
            for (label, value) in fields.iter().rev() {
                list = format!("(fs_cons {label} {} {list})", coq_term(value, scope));
            }
            format!("(e_rec {list})")
        }
        Term::Spread(base, label, value) => format!(
            "(e_spread {} {label} {})",
            coq_term(base, scope),
            coq_term(value, scope)
        ),
        Term::Proj(base, label) => format!("(e_proj {} {label})", coq_term(base, scope)),
    }
}

/// The printed source as the Coq token stream the real lexer produces.
fn coq_tokens(source: &str) -> String {
    use goat_parser::lexer::{TokenKind, tokenize};
    let tokens: Vec<String> = tokenize(source)
        .iter()
        .map(|token| {
            let text = &source[token.start..token.end];
            match token.kind {
                TokenKind::Name => format!("TName \"{text}\""),
                TokenKind::Number => match text.split_once('.') {
                    Some((whole, _)) => format!("TDec {whole}"),
                    None => format!("TNum {text}"),
                },
                TokenKind::String => "TStr".into(),
                TokenKind::Keyword
                | TokenKind::Literal
                | TokenKind::Operator
                | TokenKind::Punct => format!("TSym \"{text}\""),
                other => panic!("{other:?} in printed source {source:?}"),
            }
        })
        .collect();
    format!("[{}]", tokens.join("; "))
}

fn printer_table() -> String {
    let mut builder = Gen {
        rng: Rng(SEED),
        scope: Vec::new(),
        functions: 0,
        groups: false,
    };
    let mut rows = Vec::new();
    for _ in 0..TABLE_CASES {
        builder.functions = 0;
        let mut term = builder.term(0);
        intern_labels(&mut term, &mut Vec::new());
        let source = print(&canonical(&term, &mut Vec::new()), Style::Curried);
        rows.push(format!(
            "  ({}, {})",
            coq_term(&term, &mut Vec::new()),
            coq_tokens(&source)
        ));
    }
    format!(
        "(* Generated by checker/tests/core_roundtrip.rs; do not edit. Each row is a\n   \
         closed core term and the token stream the Rust printer writes for it (the\n   \
         curried style, binders named by depth). The Coq printer must agree. *)\n\n\
         From Stdlib Require Import String List.\n\
         Import ListNotations.\n\
         Require Import Goat.Goat_ott.\n\
         Require Import Goat.GoatPeg.\n\
         Require Import Goat.GoatPrint.\n\
         Open Scope string_scope.\n\
         Open Scope list_scope.\n\n\
         Definition printer_table : list (exp * list tok) := [\n{}\n].\n\n\
         Lemma printer_agrees :\n  \
         List.map (fun row => print (fst row)) printer_table = List.map snd printer_table.\n\
         Proof. vm_compute. reflexivity. Qed.\n",
        rows.join(";\n")
    )
}

/// `UPDATE_PRINTER_TABLE=1 cargo test -p goat_checker --test core_roundtrip`
/// rewrites the table after a change to the printer.
#[test]
fn the_coq_printer_table_matches_the_rust_printer() {
    let generated = printer_table();
    if std::env::var_os("UPDATE_PRINTER_TABLE").is_some() {
        std::fs::write(TABLE_PATH, &generated).expect("write the table");
    }
    let committed = std::fs::read_to_string(TABLE_PATH).expect("proofs/GoatPrinterTable.v exists");
    assert!(
        committed == generated,
        "proofs/GoatPrinterTable.v is stale; run with UPDATE_PRINTER_TABLE=1 and commit"
    );
}

/// The symbol of the variable a function body reads, and the symbols the
/// block's bindings bind, in order.
fn symbols_of_chain(source: &str) -> (Vec<Symbol>, Symbol) {
    let root = lower(source).expect("parses").root;
    let mut at = &root;
    let mut bound = Vec::new();
    let mut read = None;
    while let ExprKind::Let {
        symbol,
        value,
        rest: Some(rest),
        ..
    } = &at.kind
    {
        bound.push(*symbol);
        if let (ExprKind::Func { body, .. }, None) = (&value.kind, &read)
            && let ExprKind::Var { symbol, .. } = &body.kind
        {
            read = Some(*symbol);
        }
        at = rest;
    }
    (bound, read.expect("a function reads a variable"))
}

#[test]
fn a_function_binding_is_a_one_member_group_that_reads_itself() {
    let (bound, read) = symbols_of_chain("x = program(y) do x done; x");
    assert_eq!(read, bound[0]);
}

#[test]
fn a_parenthesised_function_binding_is_a_plain_let_that_does_not_read_itself() {
    let source = "x = 1; x = (program(y) do x done); x";
    let (bound, read) = symbols_of_chain(source);
    assert_eq!(read, bound[0], "the body reads the earlier `x`");
    assert_ne!(read, bound[1]);
}

#[test]
fn a_group_member_reads_a_later_member() {
    let (bound, read) = symbols_of_chain("f = program(y) do g done; g = program(z) do z done; f");
    assert_eq!(read, bound[1]);
}

#[test]
fn a_function_sees_a_later_function_of_its_block_not_a_later_value() {
    let source = "g = 1; f = program(y) do g done; g = program(z) do z done; f";
    let (bound, read) = symbols_of_chain(source);
    assert_ne!(
        read, bound[0],
        "the body of `f` does not read the earlier `g`"
    );
    assert_eq!(read, bound[2]);
}

#[test]
fn lowering_rejects_a_record_the_core_allows() {
    let errors = lower("{a: 1, a: 2}").expect("parses").errors;
    assert!(errors.iter().any(|e| e.message.contains("duplicate field")));
}

#[test]
fn the_generated_terms_use_every_operator_string_and_conditional() {
    #[derive(Default)]
    struct Seen {
        ops: Vec<BinOp>,
        strings: Vec<&'static str>,
        ifs: usize,
        whens: usize,
        decs: usize,
        groups: usize,
        members: usize,
        spreads: usize,
        dot_calls: usize,
    }
    fn visit(term: &Term, seen: &mut Seen) {
        match term {
            Term::Str(text) => {
                if !seen.strings.contains(text) {
                    seen.strings.push(text);
                }
            }
            Term::Dec(_) => seen.decs += 1,
            Term::If(a, b, c) => {
                seen.ifs += 1;
                for t in [a, b, c] {
                    visit(t, seen);
                }
            }
            Term::When(a, b) => {
                seen.whens += 1;
                visit(a, seen);
                visit(b, seen);
            }
            Term::Bin(a, op, b) => {
                if !seen.ops.contains(op) {
                    seen.ops.push(*op);
                }
                visit(a, seen);
                visit(b, seen);
            }
            Term::Spread(base, _, value) => {
                seen.spreads += 1;
                visit(base, seen);
                visit(value, seen);
            }
            Term::Abs(_, body) | Term::Proj(body, _) => visit(body, seen),
            Term::App(a, b) | Term::Let(_, a, b) => {
                if let (Term::App(callee, first), Term::App(..)) = (&**a, term)
                    && matches!(&**callee, Term::Proj(base, _) if is_path(base) && **base == **first)
                {
                    seen.dot_calls += 1;
                }
                visit(a, seen);
                visit(b, seen);
            }
            Term::Letrec(members, body) => {
                seen.groups += 1;
                seen.members += members.len();
                members.iter().for_each(|(_, f)| visit(f, seen));
                visit(body, seen);
            }
            Term::Rec(fields) => fields.iter().for_each(|(_, t)| visit(t, seen)),
            Term::Var(_) | Term::Num(_) | Term::Bool(_) => {}
        }
    }
    let mut builder = Gen {
        rng: Rng(SEED),
        scope: Vec::new(),
        functions: 0,
        groups: true,
    };
    let mut seen = Seen::default();
    for _ in 0..CASES {
        builder.functions = 0;
        visit(&builder.term(0), &mut seen);
    }
    assert_eq!(seen.ops.len(), OPERATORS.len());
    assert_eq!(seen.strings.len(), STRINGS.len());
    assert!(seen.ifs > 100, "{} conditionals", seen.ifs);
    assert!(
        seen.whens > 100,
        "{} conditionals without an else",
        seen.whens
    );
    assert!(seen.decs > 100, "{} Float literals", seen.decs);
    assert!(seen.groups > 100, "{} groups", seen.groups);
    assert!(seen.members > seen.groups, "{} members", seen.members);
    assert!(seen.spreads > 100, "{} spreads", seen.spreads);
    assert!(seen.dot_calls > 100, "{} dot calls", seen.dot_calls);
}

/// A multi-field spread is the nest of single ones, the first field innermost.
#[test]
fn a_multi_field_spread_reads_back_as_the_nest_of_single_spreads() {
    let var = |name: &str| Box::new(Term::Var(name.to_string()));
    let nest = Term::Spread(
        Box::new(Term::Spread(var("p"), 0, Box::new(Term::Num(1)))),
        1,
        Box::new(Term::Num(2)),
    );
    let source = "p = {}; {...(p), lab0: 1, lab1: 2}";
    let expected = Term::Let("p".into(), Box::new(Term::Rec(vec![])), Box::new(nest));
    assert_eq!(lower_to_term(source), expected);
}

#[test]
fn lowering_rejects_a_spread_the_core_leaves_out() {
    for (source, message) in [
        ("p = {}; {a: 1, ...p}", "must come first"),
        ("p = {}; q = {}; {...p, ...q}", "can't merge two records"),
    ] {
        let errors = lower(source).expect("parses").errors;
        let error = errors
            .iter()
            .find(|e| e.message.contains(message))
            .unwrap_or_else(|| panic!("{source:?}: {errors:?}"));
        assert!(
            source[error.span.start..error.span.end].starts_with("..."),
            "{source:?}: the error is spanned at the spread, not {:?}",
            &source[error.span.start..error.span.end]
        );
    }
}

/// The counterpart of the rejection: `Reject` in `proofs/GoatShape.v` is exactly
/// a spread that is not first or a second one, so a spread first with fields
/// after it lowers without an error.
#[test]
fn lowering_accepts_a_spread_first_in_its_record() {
    for source in ["p = {}; {...p}", "p = {}; {...p, a: 1, b: 2}"] {
        let errors = lower(source).expect("parses").errors;
        assert!(errors.is_empty(), "{source:?}: {errors:?}");
    }
}

/// `{x, y, ...r} = p` reads `p` once, binds each name to its field, and binds
/// `r` to the source without those labels: the rest pattern with k labels is k
/// restricts of one source (proofs/GoatDen.v, `unpack`).
#[test]
fn a_rest_pattern_unpacks_one_source_and_restricts_every_label() {
    let root = lower("p = {a: 1, b: 2, c: 3}; {a, b, ...r} = p r")
        .expect("parses")
        .root;
    let ExprKind::Let { rest: Some(at), .. } = &root.kind else {
        panic!("`p` is bound first: {root:?}");
    };
    let ExprKind::Let {
        symbol: source,
        value,
        rest: Some(inner),
        ..
    } = &at.kind
    else {
        panic!("the pattern binds its source: {at:?}");
    };
    let mut at: &Expr = inner;
    assert!(matches!(&value.kind, ExprKind::Var { name, .. } if name == "p"));
    let mut fields = Vec::new();
    let mut restricted = None;
    while let ExprKind::Let {
        name,
        value,
        rest: Some(rest),
        ..
    } = &at.kind
    {
        match &value.kind {
            ExprKind::Field { record, label } => {
                assert!(
                    matches!(&record.kind, ExprKind::Var { symbol, .. } if symbol == source),
                    "`{name}` reads the source"
                );
                fields.push((name.as_str(), label.as_str()));
            }
            ExprKind::Restrict { record, labels } => {
                assert!(
                    matches!(&record.kind, ExprKind::Var { symbol, .. } if symbol == source),
                    "`{name}` restricts the source"
                );
                restricted = Some((name.as_str(), labels.clone()));
            }
            other => panic!("unexpected binding {other:?}"),
        }
        at = rest;
    }
    assert_eq!(fields, [("a", "a"), ("b", "b")]);
    assert_eq!(
        restricted,
        Some(("r", vec!["a".to_string(), "b".to_string()]))
    );
}

#[test]
fn a_recursive_group_reads_back_with_each_name_resolved_to_its_member() {
    let var = |name: &str| Box::new(Term::Var(name.to_string()));
    let group = Term::Letrec(
        vec![
            (
                "even".into(),
                Term::Abs("n".into(), Box::new(Term::App(var("odd"), var("n")))),
            ),
            (
                "odd".into(),
                Term::Abs("n".into(), Box::new(Term::App(var("even"), var("n")))),
            ),
        ],
        Box::new(Term::App(var("even"), Box::new(Term::Num(2)))),
    );
    assert_eq!(
        print(&group, Style::Curried),
        "even = program(n) do odd(n) done; odd = program(n) do even(n) done; even(2)"
    );
    assert_eq!(
        lower_to_term(&print(&group, Style::Curried)),
        ungroup(&group)
    );
}

#[test]
fn an_operand_that_is_a_binding_or_an_operation_is_parenthesised() {
    let num = |n| Box::new(Term::Num(n));
    let sum = Term::Bin(num(1), BinOp::Add, num(2));
    let nested = Term::Bin(Box::new(sum.clone()), BinOp::Mul, num(3));
    assert_eq!(print(&nested, Style::Curried), "(1 + 2) * 3");
    assert_eq!(lower_to_term(&print(&nested, Style::Curried)), nested);
    let field = Term::Proj(Box::new(sum), 0);
    assert_eq!(print(&field, Style::Curried), "(1 + 2).lab0");
}
