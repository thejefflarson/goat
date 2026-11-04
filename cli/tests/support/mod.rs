//! Shared by the differential tests and the fuzz target: run a program through
//! the interpreter and wasm, and generate terminating, well-typed programs.

use goat_mir::interp::{self, Piece, Value};

/// What the interpreter says the program prints, and its live allocations.
pub fn interpret(src: &str) -> (Vec<String>, usize) {
    interpret_with_prelude(goat_checker::PRELUDE, src)
}

pub fn interpret_with_prelude(prelude: &str, src: &str) -> (Vec<String>, usize) {
    let checked = goat_checker::check_with_prelude(prelude, src).expect("program type-checks");
    let program = goat_mir::mono(&checked).expect("program monomorphizes");
    assert_eq!(
        goat_mir::verify(&program),
        Ok(()),
        "MIR verifies for: {src}"
    );
    let outcome = interp::run(&program).expect("interpreter runs");
    let mut printed: Vec<String> = outcome
        .printed
        .iter()
        .map(|line| {
            line.iter()
                .map(|piece| match piece {
                    Piece::Number(x) => goat::format_number(*x),
                    Piece::Text(bytes) => String::from_utf8_lossy(bytes).into_owned(),
                })
                .collect()
        })
        .collect();
    match outcome.value {
        Value::Int(n) => printed.push(goat::format_number(n as f64)),
        Value::Float(x) => printed.push(goat::format_number(x)),
        Value::Bool(b) => printed.push(goat::format_bool(b).to_string()),
        Value::Unit => {}
        Value::Ptr(_) => {
            let bytes = outcome
                .root_string
                .expect("only string roots are supported");
            printed.push(String::from_utf8(bytes).expect("string root is UTF-8"));
        }
    }
    (printed, outcome.live_allocations)
}

/// What the compiled wasm prints, and its live allocations after `goat_entry`.
pub fn compiled(src: &str) -> (Vec<String>, u32) {
    compiled_with_prelude(goat_checker::PRELUDE, src)
}

pub fn compiled_with_prelude(prelude: &str, src: &str) -> (Vec<String>, u32) {
    let wasm = goat::compile_with_prelude(prelude, src).expect("program compiles");
    let run = goat_cli::run(&wasm).expect("wasm runs");
    (run.printed, run.live_allocs)
}

/// Run `src` both ways, assert they agree and neither side leaks, and return
/// the printed output joined by newlines.
pub fn run(src: &str) -> String {
    run_with(src, |printed| printed)
}

/// Like `run`, with `prelude` in scope in place of the built-in one.
pub fn run_with_prelude(prelude: &str, src: &str) -> String {
    let (expected, live) = interpret_with_prelude(prelude, src);
    assert_eq!(live, 0, "interpreter leaked allocations for: {src}");
    let (printed, wasm_live) = compiled_with_prelude(prelude, src);
    assert_eq!(wasm_live, 0, "wasm leaked allocations for: {src}");
    assert_eq!(printed, expected, "wasm differs from interp: {src}");
    expected.join("\n")
}

/// Like `run`, but `tamper` rewrites the wasm output before comparison, so a
/// test can plant a divergence.
pub fn run_with(src: &str, tamper: impl FnOnce(Vec<String>) -> Vec<String>) -> String {
    run_observed(src, |(printed, live)| (tamper(printed), live))
}

/// Like `run_with`, but `tamper` sees the wasm output and live-allocation
/// count, so a test can plant a leak the oracle must report.
pub fn run_observed(
    src: &str,
    tamper: impl FnOnce((Vec<String>, u32)) -> (Vec<String>, u32),
) -> String {
    let (expected, live) = interpret(src);
    assert_eq!(live, 0, "interpreter leaked allocations for: {src}");
    let (printed, wasm_live) = tamper(compiled(src));
    assert_eq!(wasm_live, 0, "wasm leaked allocations for: {src}");
    assert_eq!(printed, expected, "wasm differs from interp: {src}");
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
            self.byte() % 8
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
            6 => self.closure(depth),
            7 => self.curried_closure(depth),
            _ if !self.functions.is_empty() => {
                let i = self.byte() as usize % self.functions.len();
                let (name, arity) = self.functions[i].clone();
                let args: Vec<String> = (0..arity).map(|_| self.number(depth + 1)).collect();
                format!("{name}({})", args.join(", "))
            }
            _ => format!("-({})", self.number(depth + 1)),
        }
    }

    /// A local `program` whose body sees every number in scope, so it may
    /// capture, and may ignore its own parameter.
    fn closure(&mut self, depth: u8) -> String {
        let name = self.fresh();
        let param = self.fresh();
        self.numbers.push(param.clone());
        let body = self.number(depth + 1);
        self.numbers.pop();
        let arg = self.number(depth + 1);
        format!("{name} = program({param}) do {body} done\n0 + ({name}({arg}))")
    }

    /// A function returning a function: the inner body may capture the outer
    /// parameter, and the returned closure outlives the call that made it.
    fn curried_closure(&mut self, depth: u8) -> String {
        let (make, made) = (self.fresh(), self.fresh());
        let (outer, inner) = (self.fresh(), self.fresh());
        self.numbers.push(outer.clone());
        self.numbers.push(inner.clone());
        let body = self.number(depth + 1);
        self.numbers.pop();
        self.numbers.pop();
        let (first, second) = (self.number(depth + 1), self.number(depth + 1));
        format!(
            "{make} = program({outer}) do program({inner}) do {body} done done\n\
             {made} = {make}({first})\n0 + ({made}({second}))"
        )
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generator_emits_nested_capturing_closures() {
        let nested = (0u8..=255)
            .map(|seed| generate(&[seed, 0, 7, 3, 7, 1, 7, 4, 6, 2, 6, 5, 6, 9]))
            .filter(|src| src.contains("do program("))
            .count();
        assert!(nested > 0, "no curried closure generated");
    }
}
