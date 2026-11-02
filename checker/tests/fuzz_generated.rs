//! Structure-aware generation: bytes steer a grammar-directed program builder,
//! so most inputs parse and reach name resolution and type checking instead of
//! bouncing off the lexer. Exhausted input yields zeros, which selects the
//! leaf cases and ends recursion, so shrinking the bytes shrinks the program.

use bolero::check;
use std::fmt::{self, Display};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::Duration;

const ITERATIONS: usize = 2_000;
const MAX_DEPTH: u8 = 5;

enum Expr {
    Number(u8),
    Bool(bool),
    Var(String),
    Neg(Box<Expr>),
    Binary(Box<Expr>, &'static str, Box<Expr>),
    Let(String, Box<Expr>, Option<Box<Expr>>),
    Function(Vec<String>, Option<Box<Expr>>),
    Call(Box<Expr>, Vec<Expr>),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    Record(Vec<(String, Expr)>),
    Access(Box<Expr>, String),
}

impl Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Number(n) => write!(f, "{n}"),
            Expr::Bool(b) => write!(f, "{b}"),
            Expr::Var(name) => write!(f, "{name}"),
            Expr::Neg(e) => write!(f, "-({e})"),
            Expr::Binary(l, op, r) => write!(f, "({l}) {op} ({r})"),
            Expr::Let(name, value, None) => write!(f, "{name} = ({value})"),
            Expr::Let(name, value, Some(rest)) => write!(f, "{name} = ({value})\n{rest}"),
            Expr::Function(params, body) => {
                write!(f, "program({}) do ", params.join(", "))?;
                if let Some(body) = body {
                    write!(f, "{body} ")?;
                }
                write!(f, "done")
            }
            Expr::Call(callee, args) => {
                write!(f, "({callee})(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            Expr::If(cond, then, None) => write!(f, "if {cond} then {then} done"),
            Expr::If(cond, then, Some(other)) => {
                write!(f, "if {cond} then {then} else {other} done")
            }
            Expr::Record(fields) => {
                write!(f, "{{")?;
                for (i, (name, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name}: {value}")?;
                }
                write!(f, "}}")
            }
            Expr::Access(e, field) => write!(f, "({e}).{field}"),
        }
    }
}

const NAMES: [&str; 6] = ["a", "b", "c", "f", "g", "x"];
const OPS: [&str; 8] = ["+", "-", "*", "/", "<", "<=", ">", ">="];

struct Gen<'a> {
    data: &'a [u8],
    scope: Vec<String>,
}

impl Gen<'_> {
    fn byte(&mut self) -> u8 {
        let (first, rest) = self
            .data
            .split_first()
            .map_or((0, self.data), |(b, r)| (*b, r));
        self.data = rest;
        first
    }

    fn name(&mut self) -> String {
        NAMES[self.byte() as usize % NAMES.len()].to_string()
    }

    fn var(&mut self) -> Expr {
        if self.scope.is_empty() {
            return Expr::Number(self.byte());
        }
        let i = self.byte() as usize % self.scope.len();
        Expr::Var(self.scope[i].clone())
    }

    fn boxed(&mut self, depth: u8) -> Box<Expr> {
        Box::new(self.expr(depth))
    }

    fn expr(&mut self, depth: u8) -> Expr {
        let choice = if depth >= MAX_DEPTH {
            self.byte() % 3
        } else {
            self.byte() % 12
        };
        let depth = depth + 1;
        match choice {
            0 => Expr::Number(self.byte()),
            1 => Expr::Bool(self.byte().is_multiple_of(2)),
            2 => self.var(),
            3 => Expr::Neg(self.boxed(depth)),
            4 | 5 => {
                let op = OPS[self.byte() as usize % OPS.len()];
                Expr::Binary(self.boxed(depth), op, self.boxed(depth))
            }
            6 => {
                let name = self.name();
                let value = self.boxed(depth);
                self.scope.push(name.clone());
                let rest = (!self.byte().is_multiple_of(4)).then(|| self.boxed(depth));
                Expr::Let(name, value, rest)
            }
            7 => {
                let count = self.byte() % 3;
                let params: Vec<String> = (0..count).map(|_| self.name()).collect();
                let mark = self.scope.len();
                self.scope.extend(params.iter().cloned());
                let body = (!self.byte().is_multiple_of(4)).then(|| self.boxed(depth));
                self.scope.truncate(mark);
                Expr::Function(params, body)
            }
            8 => {
                let callee = self.var();
                let count = self.byte() % 3;
                let args = (0..count).map(|_| self.expr(depth)).collect();
                Expr::Call(Box::new(callee), args)
            }
            9 => {
                let cond = self.boxed(depth);
                let then = self.boxed(depth);
                let other = (!self.byte().is_multiple_of(3)).then(|| self.boxed(depth));
                Expr::If(cond, then, other)
            }
            10 => {
                let count = self.byte() % 3;
                let fields = (0..count)
                    .map(|_| (self.name(), self.expr(depth)))
                    .collect();
                Expr::Record(fields)
            }
            _ => {
                let record = self.boxed(depth);
                Expr::Access(record, self.name())
            }
        }
    }
}

fn program(data: &[u8]) -> String {
    Gen {
        data,
        scope: Vec::new(),
    }
    .expr(0)
    .to_string()
}

#[test]
fn generated_programs_never_panic() {
    check!()
        .with_iterations(ITERATIONS)
        .with_max_len(256)
        .for_each(|data: &[u8]| {
            let _ = goat_checker::check(&program(data));
        });
}

#[test]
fn generated_programs_mostly_parse_and_some_type_check() {
    let (mut checked, mut parse_failures, mut total) = (0, 0, 0);
    check!()
        .with_iterations(ITERATIONS)
        .with_max_len(256)
        .for_each(|data: &[u8]| {
            total += 1;
            match goat_checker::check(&program(data)) {
                Ok(_) => checked += 1,
                Err(errors) => {
                    if errors[0].message.starts_with("parse error") {
                        parse_failures += 1;
                    }
                }
            }
        });
    assert!(
        parse_failures * 100 <= total,
        "{parse_failures}/{total} failed to parse"
    );
    assert!(checked * 10 >= total, "only {checked}/{total} type-checked");
}

#[test]
fn zeroed_input_yields_the_minimal_program() {
    assert_eq!(program(&[]), "0");
    assert_eq!(program(&[7]), "program() do done");
    assert_eq!(program(&[9, 1, 1]), "if false then 0 done");
}

#[test]
fn a_seeded_bug_is_found_and_shrunk() {
    let failure = catch_unwind(AssertUnwindSafe(|| {
        check!()
            .with_iterations(ITERATIONS)
            .with_shrink_time(Duration::from_secs(1))
            .with_max_len(256)
            .for_each(|data: &[u8]| {
                let source = program(data);
                assert!(!source.contains("program("), "seeded bug: {source}");
            });
    }));
    assert!(failure.is_err(), "the seeded bug must be found");
}
