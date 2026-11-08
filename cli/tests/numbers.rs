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

const DIVISION_BY_ZERO: &str = "division by zero";
const NOT_WHOLE: &str = "this number can't be made a whole number";

#[test]
fn floor_division_rounds_toward_negative_infinity() {
    for (sum, expected) in [
        ("7 // 2", "3"),
        ("-7 // 2", "-4"),
        ("7 // -2", "-4"),
        ("-7 // -2", "3"),
        ("6 // 3", "2"),
        ("-6 // 3", "-2"),
        ("0 // 5", "0"),
        ("1 // 5", "0"),
        ("-1 // 5", "-1"),
    ] {
        assert_eq!(run(&format!("print({sum})")), expected, "{sum}");
    }
}

#[test]
fn remainder_takes_the_sign_of_the_divisor() {
    for (sum, expected) in [
        ("7 % 3", "1"),
        ("-7 % 3", "2"),
        ("7 % -3", "-2"),
        ("-7 % -3", "-1"),
        ("6 % 3", "0"),
        ("-6 % 3", "0"),
        ("0 % 5", "0"),
        ("-1 % 360", "359"),
    ] {
        assert_eq!(run(&format!("print({sum})")), expected, "{sum}");
    }
}

#[test]
fn floor_division_and_remainder_rebuild_the_dividend() {
    let program = "check = program(a, b) do (a // b) * b + a % b == a done
for a from -9 to 9 do
  for b from 1 to 4 do print(check(a, b) and check(a, 0 - b)) done
done";
    let printed = run(program);
    assert!(printed.lines().all(|line| line == "true"), "{printed}");
    assert_eq!(printed.lines().count(), 19 * 4);
}

#[test]
fn floor_division_and_remainder_work_through_functions_and_loops() {
    let digits = "digit = program(n, place) do n // place % 10 done
print(digit(4096, 1));
print(digit(4096, 10));
print(digit(4096, 100));
print(digit(4096, 1000))";
    assert_eq!(run(digits), "6\n9\n0\n4");
    assert_eq!(
        run("for i from 1 to 6 do print(i % 3 == 0) done"),
        "false\nfalse\ntrue\nfalse\nfalse\ntrue"
    );
    assert_eq!(run("print(7 // 2 + 0.5)"), "3.5");
}

#[test]
fn floor_division_and_remainder_trap_on_a_zero_divisor() {
    assert_traps("1 // 0", DIVISION_BY_ZERO);
    assert_traps("1 % 0", DIVISION_BY_ZERO);
    assert_traps("zero = 3 - 3\n5 // zero", DIVISION_BY_ZERO);
    assert_traps("zero = 3 - 3\n0 - 5 % zero", DIVISION_BY_ZERO);
    assert_traps(
        "split = program(a, b) do a // b done\nsplit(10, 0)",
        DIVISION_BY_ZERO,
    );
}

#[test]
fn the_most_negative_int_floor_divides_by_minus_one_only_as_a_remainder() {
    let min = "min = 0 - 9223372036854775807 - 1\n";
    assert_traps(&format!("{min}min // (0 - 1)"), OVERFLOW);
    assert_eq!(run(&format!("{min}print(min % (0 - 1))")), "0");
    assert_eq!(run(&format!("{min}print(min // 1 == min)")), "true");
    assert_eq!(run(&format!("{min}print(min % 2)")), "0");
    assert_eq!(
        run(&format!(
            "{min}print((min + 1) // 2 == 0 - 4611686018427387904)"
        )),
        "true"
    );
}

#[test]
fn round_floor_ceil_and_truncate_turn_a_float_into_an_int() {
    for (call, expected) in [
        ("round(2.4)", "2"),
        ("round(2.5)", "3"),
        ("round(-2.4)", "-2"),
        ("round(-2.5)", "-3"),
        ("round(0.49999999999999994)", "0"),
        ("round(7)", "7"),
        ("floor(2.7)", "2"),
        ("floor(-2.1)", "-3"),
        ("floor(-2.0)", "-2"),
        ("floor(5)", "5"),
        ("ceil(2.1)", "3"),
        ("ceil(-2.7)", "-2"),
        ("ceil(2.0)", "2"),
        ("truncate(2.9)", "2"),
        ("truncate(-2.9)", "-2"),
        ("truncate(1e15)", "1000000000000000"),
        ("round(-0.4) == 0", "true"),
    ] {
        assert_eq!(run(&format!("print({call})")), expected, "{call}");
    }
}

#[test]
fn the_result_of_a_rounding_function_is_an_int() {
    let whole = "n = round(9007199254740993 / 1)\nprint(n // 2)";
    assert_eq!(run(whole), "4503599627370496");
    assert_eq!(run("print(round(7.6) // 2 + round(1.4))"), "5");
    assert_eq!(
        run("print(change_each([1.5, 2.5, -2.5], round))"),
        "[2, 3, -3]"
    );
    assert_eq!(run("print(change_each([1.5, 2.5], floor))"), "[1, 2]");
}

#[test]
fn rounding_a_float_with_no_int_traps() {
    assert_traps("round(1 / 0)", NOT_WHOLE);
    assert_traps("floor(0.0 / 0.0)", NOT_WHOLE);
    assert_traps("truncate(1e19)", NOT_WHOLE);
    assert_traps("ceil(0 - 1e19)", NOT_WHOLE);
    assert_eq!(
        run("print(truncate(9223372036854774784.0) == 9223372036854774784)"),
        "true"
    );
}

#[test]
fn sqrt_is_exact_where_it_can_be() {
    assert_eq!(run("print(sqrt(16))"), "4");
    assert_eq!(run("print(sqrt(2.25))"), "1.5");
    assert_eq!(run("print(sqrt(0))"), "0");
    assert_eq!(run("print(sqrt(2) * sqrt(2) > 1.99999)"), "true");
    assert_eq!(run("print(sqrt(0 - 1) == sqrt(0 - 1))"), "false");
    assert_eq!(run("n = 49 // 1\nprint(sqrt(n))"), "7");
}

#[test]
fn trig_takes_degrees_and_is_exact_at_the_quarter_turns() {
    for (call, expected) in [
        ("sin(0)", "0"),
        ("sin(90)", "1"),
        ("sin(180)", "0"),
        ("sin(270)", "-1"),
        ("sin(360)", "0"),
        ("sin(-90)", "-1"),
        ("cos(0)", "1"),
        ("cos(90)", "0"),
        ("cos(180)", "-1"),
        ("cos(270)", "0"),
        ("cos(-180)", "-1"),
        ("sin(30)", "0.5"),
        ("cos(60)", "0.5"),
        ("sin(-30)", "-0.5"),
        ("sin(1000)", "-0.984807753012208"),
        ("tan(45)", "1"),
        ("tan(0)", "0"),
    ] {
        assert_eq!(run(&format!("print({call})")), expected, "{call}");
    }
}

#[test]
fn trig_keeps_the_pythagorean_identity_all_the_way_round() {
    let program = "wobble = program(d) do sin(d) * sin(d) + cos(d) * cos(d) - 1 done
for d from -400 to 400 do
  print(wobble(d) < 0.000000000001 and wobble(d) > -0.000000000001)
done";
    let printed = run(program);
    assert_eq!(printed.lines().count(), 801);
    assert!(printed.lines().all(|line| line == "true"), "{printed}");
}

#[test]
fn an_int_counter_feeds_trig_and_sqrt() {
    let program = "for i from 0 to 4 do print(round(100 * sin(i * 90)) + round(sqrt(i * i))) done";
    assert_eq!(run(program), "0\n101\n2\n-97\n4");
}

#[test]
fn an_int_widens_at_a_call_to_a_float_parameter() {
    let note = "note = foreign \"test\" \"note\" (Number) -> Unit\n";
    let (_, log) = run_foreign(&format!("{note}note(7 // 2)"));
    assert_eq!(log, ["note(3)"]);
    let scale = "scale = program(x) do x * 1.5 done\nprint(scale(7 // 2))";
    assert_eq!(run(scale), "4.5");
}
