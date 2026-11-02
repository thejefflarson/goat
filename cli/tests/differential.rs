//! Differential tests: every program runs through the MIR interpreter (the
//! oracle) and through the compiled wasm under wasmtime, and both must print
//! the same thing. The interpreter must also leave no heap object live.

use std::fs;

use bolero::check;
use goat_mir::interp::{self, Value};

/// What the interpreter says the program prints, and its live allocations.
fn interpret(src: &str) -> (Vec<String>, usize) {
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

fn compiled(src: &str) -> Vec<String> {
    let wasm = goat::compile(src).expect("program compiles");
    goat_cli::execute(&wasm).expect("wasm runs")
}

/// Run `src` both ways, assert they agree and the interpreter leaks nothing,
/// and return the printed output joined by newlines.
fn run(src: &str) -> String {
    let (expected, live) = interpret(src);
    assert_eq!(live, 0, "interpreter leaked allocations for: {src}");
    assert_eq!(compiled(src), expected, "wasm differs from interp: {src}");
    expected.join("\n")
}

#[test]
fn arithmetic() {
    assert_eq!(run("1 + 2 * 3"), "7");
    assert_eq!(run("(1 + 2) * 3"), "9");
    assert_eq!(run("10 / 4"), "2.5");
}

#[test]
fn numbers_print_without_exponent() {
    assert_eq!(run("1000000"), "1000000");
    assert_eq!(run("123456789"), "123456789");
    assert_eq!(run("0.5"), "0.5");
    assert_eq!(run("0.1 + 0.2"), "0.3");
}

#[test]
fn booleans() {
    assert_eq!(run("1 < 2"), "true");
    assert_eq!(run("3 < 2"), "false");
    assert_eq!(run("x = 5  x < 10"), "true");
}

#[test]
fn let_bindings() {
    assert_eq!(run("a = 2  b = 3  a + b"), "5");
}

#[test]
fn functions_and_recursion() {
    assert_eq!(run("add = program(a, b) do a + b done  add(20, 22)"), "42");
    let fib = "fib = program(n) do if n < 2 then n else fib(n - 1) + fib(n - 2) done done fib(10)";
    assert_eq!(run(fib), "55");
}

#[test]
fn higher_order_functions() {
    let src = "apply = program(f, x) do f(x) done \
               double = program(n) do n * 2 done \
               apply(double, 21)";
    assert_eq!(run(src), "42");
}

#[test]
fn identifier_may_start_with_a_keyword() {
    assert_eq!(run("double = program(n) do n * 2 done  double(21)"), "42");
}

#[test]
fn mutual_recursion_either_order() {
    let even_first = "is_even = program(n) do if n < 1 then true else is_odd(n - 1) done done \
                      is_odd = program(n) do if n < 1 then false else is_even(n - 1) done done \
                      is_even(10)";
    let odd_first = "is_odd = program(n) do if n < 1 then false else is_even(n - 1) done done \
                     is_even = program(n) do if n < 1 then true else is_odd(n - 1) done done \
                     is_even(7)";
    assert_eq!(run(even_first), "true");
    assert_eq!(run(odd_first), "false");
}

#[test]
fn shadowing_value_binding() {
    assert_eq!(run("score = 1  score = score + 1  score"), "2");
}

#[test]
fn long_operator_chain() {
    assert_eq!(run(&vec!["1"; 200].join(" + ")), "200");
}

#[test]
fn deep_tail_recursion_runs_in_constant_stack() {
    let src = "sum = program(n, acc) do if n < 1 then acc else sum(n - 1, acc + n) done done \
               sum(1000000, 0)";
    assert_eq!(run(src), "500000500000");
}

#[test]
fn examples_print_the_expected_output() {
    for (file, expected) in [("fib.goat", "55"), ("higher_order.goat", "42")] {
        let path = format!("{}/../examples/{file}", env!("CARGO_MANIFEST_DIR"));
        let src = fs::read_to_string(&path).unwrap();
        assert_eq!(run(&src), expected, "{file}");
    }
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

#[test]
fn generated_programs_agree_between_interp_and_wasm() {
    check!()
        .with_iterations(300)
        .with_max_len(256)
        .for_each(|data: &[u8]| {
            let src = Gen {
                data,
                next_name: 0,
                numbers: Vec::new(),
                functions: Vec::new(),
            }
            .program();
            run(&src);
        });
}
