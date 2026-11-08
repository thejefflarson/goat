//! Chains of operators far longer than the checker admits, built as MIR by
//! hand: the interpreter and the wasm lowering walk them in a loop, so a chain
//! thousands of links long runs on a default test thread, and both drivers
//! still agree on the answer, the short-circuiting, and where a trap lands.

#[path = "../../mir/tests/common/mod.rs"]
mod common;

use common::*;
use goat_mir::interp::{self, Piece, Value};
use goat_mir::*;

const DEPTH: usize = 2000;

/// `leaf` with `link` applied `len` times, each wrapping the one before it,
/// so the chain leans left the way `a op b op c` parses.
fn chain(len: usize, leaf: Expr, link: impl Fn(Expr, usize) -> Expr) -> Expr {
    (0..len).fold(leaf, link)
}

/// A link of an `Int` chain the way mono lowers it: the chain so far is the
/// right-hand side of a `Let`, and the operator reads locals.
fn bound_link(op: IntOp, acc: Expr, i: usize, by: i64) -> Expr {
    let base = 3 * i as u32;
    let operator = Expr::BinInt(op, Box::new(local(base)), Box::new(local(base + 1)));
    let site = let_(base + 2, Expr::Site(0, 1), operator);
    let_(base, acc, let_(base + 1, int(by), site))
}

/// What each driver prints for `p`, one entry per line, ending with the root
/// value; a trap comes back as `trap: message` in both.
fn both(p: &Program) -> (Vec<String>, Vec<String>) {
    let oracle = match interp::run(p) {
        Ok(out) => {
            let mut lines: Vec<String> = out.printed.iter().map(|line| render(line)).collect();
            lines.push(match out.value {
                Value::Int(n) => n.to_string(),
                Value::Float(x) => goat::format_number(x),
                Value::Bool(b) => goat::format_bool(b).to_string(),
                other => panic!("unexpected root {other:?}"),
            });
            lines
        }
        Err(interp::InterpError::Trap(message)) => vec![format!("trap: {message}")],
        Err(other) => panic!("interpreter error {other:?}"),
    };
    let bytes = goat_wasm::emit(p).expect("program emits");
    let compiled = match goat_cli::run(&bytes) {
        Ok(run) => run.printed,
        Err(trap) => vec![trap],
    };
    (oracle, compiled)
}

fn render(line: &[Piece]) -> String {
    line.iter()
        .map(|piece| match piece {
            Piece::Int(n) => n.to_string(),
            Piece::Number(x) => goat::format_number(*x),
            Piece::Text(bytes) => String::from_utf8_lossy(bytes).into_owned(),
        })
        .collect()
}

fn agree(p: &Program) -> Vec<String> {
    let (oracle, compiled) = both(p);
    assert_eq!(compiled, oracle, "wasm differs from interp");
    oracle
}

fn entry(ret: MTy, body: Expr) -> Program {
    program(vec![func(ret, body)])
}

/// A function of `n` that prints `n` on its own line and returns `n op limit`.
fn printing(op: CmpOp, limit: i64) -> Func {
    let print = Expr::Write(Write::Number(Box::new(local(0))));
    let body = let_(
        1,
        print,
        let_(2, Expr::Write(Write::End), cmp(op, local(0), int(limit))),
    );
    func_with(vec![(0, MTy::Int)], MTy::Bool, body)
}

fn show(n: usize) -> Expr {
    call(1, vec![int(n as i64)])
}

#[test]
fn a_sum_of_thousands_of_terms_runs() {
    let body = chain(DEPTH, int(0), |acc, _| add(acc, int(1)));
    assert_eq!(agree(&entry(MTy::Int, body)), [DEPTH.to_string()]);
}

#[test]
fn a_chain_of_bound_links_runs() {
    let sum = chain(DEPTH, int(0), |acc, i| bound_link(IntOp::Add, acc, i, 2));
    assert_eq!(agree(&entry(MTy::Int, sum)), [(2 * DEPTH).to_string()]);
    let difference = chain(DEPTH, int(0), |acc, i| bound_link(IntOp::Sub, acc, i, 2));
    assert_eq!(
        agree(&entry(MTy::Int, difference)),
        [(-2 * DEPTH as i64).to_string()]
    );
    let overflow = chain(DEPTH, int(i64::MAX - 1), |acc, i| {
        bound_link(IntOp::Add, acc, i, 1)
    });
    assert_eq!(
        agree(&entry(MTy::Int, overflow)),
        [format!("trap: {INT_OVERFLOW}")]
    );
}

#[test]
fn a_difference_is_left_associative() {
    let body = chain(DEPTH, int(0), |acc, i| sub(acc, int(i as i64)));
    let expected = -(DEPTH as i64 * (DEPTH as i64 - 1) / 2);
    assert_eq!(agree(&entry(MTy::Int, body)), [expected.to_string()]);
}

#[test]
fn a_comparison_over_a_long_sum_runs() {
    let sum = chain(DEPTH, int(0), |acc, _| add(acc, int(1)));
    let body = cmp(CmpOp::Eq, sum, int(DEPTH as i64));
    assert_eq!(agree(&entry(MTy::Bool, body)), ["true"]);
}

#[test]
fn float_chains_and_conversions_run() {
    let sum = chain(DEPTH, float(0.0), |acc, _| {
        bin_float(FloatOp::Add, acc, Expr::IntToFloat(Box::new(int(1))))
    });
    assert_eq!(agree(&entry(MTy::Float, sum)), [DEPTH.to_string()]);
    let roots = chain(DEPTH, float(16.0), |acc, _| {
        Expr::FloatFn(FloatFn::Sqrt, Box::new(acc))
    });
    assert_eq!(agree(&entry(MTy::Float, roots)), ["1"]);
}

#[test]
fn an_and_chain_stops_at_the_first_false() {
    let stop = 100;
    let body = chain(DEPTH, show(0), |acc, i| {
        if_(acc, show(i + 1), boolean(false))
    });
    let p = program(vec![
        func(MTy::Bool, body),
        printing(CmpOp::Lt, stop as i64),
    ]);
    let mut expected: Vec<String> = (0..=stop).map(|n| n.to_string()).collect();
    expected.push("false".into());
    assert_eq!(agree(&p), expected);
}

#[test]
fn an_or_chain_stops_at_the_first_true() {
    let stop = 100;
    let body = chain(DEPTH, show(0), |acc, i| {
        if_(acc, boolean(true), show(i + 1))
    });
    let p = program(vec![
        func(MTy::Bool, body),
        printing(CmpOp::Ge, stop as i64),
    ]);
    let mut expected: Vec<String> = (0..=stop).map(|n| n.to_string()).collect();
    expected.push("true".into());
    assert_eq!(agree(&p), expected);
}

#[test]
fn a_long_and_chain_of_trues_runs_every_term() {
    let body = chain(DEPTH, show(0), |acc, i| {
        if_(acc, show(i + 1), boolean(false))
    });
    let p = program(vec![func(MTy::Bool, body), printing(CmpOp::Lt, i64::MAX)]);
    let lines = agree(&p);
    assert_eq!(lines.len(), DEPTH + 2);
    assert_eq!(lines.last().map(String::as_str), Some("true"));
}

#[test]
fn a_pile_of_nots_runs() {
    let body = chain(DEPTH, boolean(true), |acc, _| {
        if_(acc, boolean(false), boolean(true))
    });
    assert_eq!(agree(&entry(MTy::Bool, body)), ["true"]);
}

#[test]
fn a_trap_lands_on_the_link_that_overflows() {
    let fits = chain(DEPTH, int(i64::MAX - DEPTH as i64), |acc, _| {
        add(acc, int(1))
    });
    assert_eq!(agree(&entry(MTy::Int, fits)), [i64::MAX.to_string()]);
    let overflows = chain(DEPTH + 1, int(i64::MAX - DEPTH as i64), |acc, _| {
        add(acc, int(1))
    });
    assert_eq!(
        agree(&entry(MTy::Int, overflows)),
        [format!("trap: {INT_OVERFLOW}")]
    );
}

#[test]
fn a_trap_in_the_last_link_of_a_division_chain() {
    let divide = |len, by| {
        let link = |acc, _| Expr::BinInt(IntOp::FloorDiv, Box::new(acc), Box::new(int(1)));
        let ones = chain(len, int(7), link);
        Expr::BinInt(IntOp::FloorDiv, Box::new(ones), Box::new(int(by)))
    };
    assert_eq!(agree(&entry(MTy::Int, divide(DEPTH, 7))), ["1"]);
    assert_eq!(
        agree(&entry(MTy::Int, divide(DEPTH, 0))),
        [format!("trap: {DIVISION_BY_ZERO}")]
    );
}
