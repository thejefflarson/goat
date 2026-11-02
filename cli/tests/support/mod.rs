//! Shared by the differential tests and the fuzz target: run a program through
//! the interpreter and wasm, and generate terminating, well-typed programs.

use goat_mir::interp::{self, Value};

/// What the interpreter says the program prints, and its live allocations.
pub fn interpret(src: &str) -> (Vec<String>, usize) {
    let checked = goat_checker::check(src).expect("program type-checks");
    let program = goat_mir::mono(&checked).expect("program monomorphizes");
    let outcome = interp::run(&program).expect("interpreter runs");
    let printed = match outcome.value {
        Value::Int(n) => vec![goat::format_number(n as f64)],
        Value::Float(x) => vec![goat::format_number(x)],
        Value::Bool(b) => vec![goat::format_bool(b).to_string()],
        Value::Unit => Vec::new(),
        Value::Ptr(_) => panic!("heap-valued root"),
    };
    (printed, outcome.live_allocations)
}

pub fn compiled(src: &str) -> Vec<String> {
    let wasm = goat::compile(src).expect("program compiles");
    goat_cli::execute(&wasm).expect("wasm runs")
}

/// Run `src` both ways, assert they agree and the interpreter leaks nothing,
/// and return the printed output joined by newlines.
pub fn run(src: &str) -> String {
    run_with(src, |printed| printed)
}

/// Like `run`, but `tamper` rewrites the wasm output before comparison, so a
/// test can plant a divergence.
pub fn run_with(src: &str, tamper: impl FnOnce(Vec<String>) -> Vec<String>) -> String {
    let (expected, live) = interpret(src);
    assert_eq!(live, 0, "interpreter leaked allocations for: {src}");
    assert_eq!(
        tamper(compiled(src)),
        expected,
        "wasm differs from interp: {src}"
    );
    expected.join("\n")
}

/// Closed, well-typed programs built from bytes. Names are unique and a
/// function only calls earlier ones, so every program terminates.
struct Gen<'a> {
    data: &'a [u8],
    next_name: usize,
    numbers: Vec<String>,
    functions: Vec<(String, usize)>,
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

    fn fresh(&mut self) -> String {
        self.next_name += 1;
        format!("v{}", self.next_name)
    }

    fn number(&mut self, depth: u8) -> String {
        let choice = if depth >= 4 {
            self.byte() % 2
        } else {
            self.byte() % 6
        };
        match choice {
            0 => self.byte().to_string(),
            1 if !self.numbers.is_empty() => {
                let i = self.byte() as usize % self.numbers.len();
                self.numbers[i].clone()
            }
            1 => self.byte().to_string(),
            2 => {
                let op = ["+", "-", "*", "/"][self.byte() as usize % 4];
                format!(
                    "({}) {op} ({})",
                    self.number(depth + 1),
                    self.number(depth + 1)
                )
            }
            3 => {
                let cond = self.boolean(depth + 1);
                format!(
                    "if {cond} then {} else {} done",
                    self.number(depth + 1),
                    self.number(depth + 1)
                )
            }
            4 => {
                let name = self.fresh();
                let value = self.number(depth + 1);
                self.numbers.push(name.clone());
                let rest = self.number(depth + 1);
                self.numbers.pop();
                format!("{name} = ({value})\n0 + ({rest})")
            }
            _ if !self.functions.is_empty() => {
                let i = self.byte() as usize % self.functions.len();
                let (name, arity) = self.functions[i].clone();
                let args: Vec<String> = (0..arity).map(|_| self.number(depth + 1)).collect();
                format!("{name}({})", args.join(", "))
            }
            _ => format!("-({})", self.number(depth + 1)),
        }
    }

    fn boolean(&mut self, depth: u8) -> String {
        if self.byte().is_multiple_of(4) {
            return self.byte().is_multiple_of(2).to_string();
        }
        let op = ["<", "<=", ">", ">="][self.byte() as usize % 4];
        format!(
            "({}) {op} ({})",
            self.number(depth + 1),
            self.number(depth + 1)
        )
    }

    fn program(&mut self) -> String {
        let mut source = String::new();
        for _ in 0..self.byte() % 3 {
            let name = self.fresh();
            let arity = self.byte() as usize % 3;
            let params: Vec<String> = (0..arity).map(|_| self.fresh()).collect();
            let outer = std::mem::replace(&mut self.numbers, params.clone());
            let body = self.number(2);
            self.numbers = outer;
            source += &format!("{name} = program({}) do {body} done\n", params.join(", "));
            self.functions.push((name, arity));
        }
        source += &if self.byte().is_multiple_of(3) {
            format!("if true then {} else false done", self.boolean(0))
        } else {
            format!("0 + ({})", self.number(0))
        };
        source
    }
}

/// The program `data` encodes.
pub fn generate(data: &[u8]) -> String {
    Gen {
        data,
        next_name: 0,
        numbers: Vec::new(),
        functions: Vec::new(),
    }
    .program()
}
