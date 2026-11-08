//! The Int/Float split end to end (ADR 0017): every program runs through the
//! interpreter and through wasm under wasmtime, which must print the same
//! lines, make the same host calls, and leave no heap object live. An `Int` is
//! an `i64` that traps instead of wrapping.

use goat_mir::interp::{self, InterpError};

#[allow(dead_code)]
mod support;

use support::{run, run_foreign};

const OVERFLOW: &str = "this number got too big";

fn interp_error(src: &str) -> InterpError {
    let checked = goat_checker::check(src).expect("type-checks");
    let program = goat_mir::mono(&checked).expect("monomorphizes");
    assert_eq!(goat_mir::verify(&program), Ok(()), "{src}");
    interp::run(&program).expect_err("the program should trap")
}

fn wasm_error(src: &str) -> String {
    let wasm = goat::compile_turtle(src).expect("compiles");
    match goat_cli::run(&wasm) {
        Ok(_) => panic!("the program should trap: {src}"),
        Err(error) => error,
    }
}

fn assert_traps(src: &str, message: &str) {
    assert_eq!(
        interp_error(src),
        InterpError::Trap(message.into()),
        "{src}"
    );
    assert_eq!(wasm_error(src), format!("trap: {message}"), "{src}");
}

#[test]
fn an_int_is_a_64_bit_integer() {
    assert_eq!(run("print(3000000000 * 3)"), "9000000000");
    // 2^53 + 1 is the first whole number a float cannot hold.
    assert_eq!(run("print(9007199254740993 - 9007199254740992)"), "1");
    assert_eq!(run("print(7 * 6)"), "42");
    assert_eq!(run("print(2 + 3 - 10)"), "-5");
}

#[test]
fn division_is_a_float() {
    assert_eq!(run("print(7 / 2)"), "3.5");
    assert_eq!(run("print(4 / 2)"), "2");
    assert_eq!(run("print(1 / 4 + 1)"), "1.25");
    assert_eq!(run("print(1 / 0 > 1000)"), "true");
}

#[test]
fn an_int_beside_a_float_widens() {
    assert_eq!(run("print(3 + 1.5)"), "4.5");
    assert_eq!(run("n = 3\nprint(n + 1.5)"), "4.5");
    assert_eq!(run("print(3 < 3.5)"), "true");
    assert_eq!(run("print(2 == 2.0)"), "true");
    assert_eq!(run("print(2 * 0.25)"), "0.5");
}

#[test]
fn an_int_in_a_division_is_converted_first() {
    let half = "half = program(n) do n / 2 done\n";
    assert_eq!(run(&format!("{half}print(half(5))")), "2.5");
    assert_eq!(run(&format!("{half}print(half(5.0))")), "2.5");
    assert_eq!(
        run("ratio = program(a, b) do a / b done\nprint(ratio(1, 4))"),
        "0.25"
    );
}

#[test]
fn a_numeric_function_runs_at_both_types() {
    let add = "add = program(a, b) do a + b done\n";
    assert_eq!(
        run(&format!("{add}print(add(1, 2));\nprint(add(1.5, 2))")),
        "3\n3.5"
    );
    let scale = "scale = program(x) do x * 2 done\nprint(scale(21));\nprint(scale(0.25))";
    assert_eq!(run(scale), "42\n0.5");
}

#[test]
fn numbers_inside_values_keep_their_type() {
    assert_eq!(run("print([1, 2, 3])"), "[1, 2, 3]");
    assert_eq!(run("print({x: 1, y: 2.5})"), "{x: 1, y: 2.5}");
    assert_eq!(
        run("print({x: 1, y: 2} + {x: 10, y: 20})"),
        "{x: 11, y: 22}"
    );
    assert_eq!(run("print({x: 9, y: 8} / {x: 3, y: 2})"), "{x: 3, y: 4}");
    let adder = "adder = program(n) do program(x) do x + n done done\nprint(adder(1)(2))";
    assert_eq!(run(adder), "3");
    assert_eq!(run("print(sum([1, 2, 3]) + sum([0.5, 0.25]))"), "6.75");
}

#[test]
fn a_loop_counts_in_whole_numbers() {
    assert_eq!(run("for i from 1 to 3 do print(i * i) done"), "1\n4\n9");
    assert_eq!(run("for i from 1 to 2 do print(i / 2) done"), "0.5\n1");
}

#[test]
fn a_host_int_widens_beside_a_float() {
    let count = "count = foreign \"test\" \"count\" () -> Int\n";
    let bump = "bump = foreign \"test\" \"bump\" (Int) -> Int\n";
    let (printed, log) = run_foreign(&format!("{count}print(count() + 1.5)"));
    assert_eq!(
        (printed.as_str(), log),
        ("8.5", vec!["count()".to_string()])
    );
    let (printed, log) = run_foreign(&format!("{count}{bump}print(bump(count()) * 2)"));
    assert_eq!(printed, "16");
    assert_eq!(log, ["count()", "bump(7)"]);
    let (printed, _) = run_foreign(&format!("{count}print(count() / 2)"));
    assert_eq!(printed, "3.5");
}

#[test]
fn an_int_that_overflows_traps_in_both_backends() {
    assert_traps("9223372036854775807 + 1", OVERFLOW);
    assert_traps("x = 0 - 9223372036854775807\nx - 2", OVERFLOW);
    assert_traps("4611686018427387904 * 2", OVERFLOW);
    assert_traps("3037000500 * 3037000500", OVERFLOW);
    assert_traps("3037000500 * (0 - 3037000500) * 4", OVERFLOW);
    // MIN * -1 and 0 - MIN are one past the largest Int.
    let min = "min = 0 - 9223372036854775807 - 1\n";
    assert_traps(&format!("{min}min * (0 - 1)"), OVERFLOW);
    assert_traps(&format!("{min}0 - min"), OVERFLOW);
    assert_traps(
        "add = program(a, b) do a + b done\nadd(9223372036854775807, 1)",
        OVERFLOW,
    );
    assert_traps("sum([9223372036854775807, 1])", OVERFLOW);
}

#[test]
fn an_int_at_the_edge_does_not_trap() {
    assert_eq!(
        run("print(9223372036854775806 + 1 == 9223372036854775807)"),
        "true"
    );
    assert_eq!(
        run("print(4611686018427387903 * 2 == 9223372036854775806)"),
        "true"
    );
    let min = "min = 0 - 9223372036854775807 - 1\n";
    assert_eq!(run(&format!("{min}print(min * 1 == min)")), "true");
    assert_eq!(run(&format!("{min}print(min + 1 < 0)")), "true");
    assert_eq!(run("print(0 * 9223372036854775807)"), "0");
}

#[test]
fn a_float_follows_ieee_and_never_traps() {
    assert_eq!(run("print(1e300 * 1e300 > 1e308)"), "true");
    assert_eq!(run("x = 9223372036854775807.0\nprint(x + x > x)"), "true");
    assert_eq!(run("print(0.0 / 0.0 == 0.0 / 0.0)"), "false");
}
