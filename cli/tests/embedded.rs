//! The embedded profile (ADR 0017): `Int` is an `i32` and `Float` an `f32`.
//! Every program runs on the MIR interpreter and as wasm under wasmtime on
//! both profiles. The two backends must agree on each profile, and the two
//! profiles must print the same lines except where a width makes them differ.
//! Each legitimate difference is a test below that names what changed:
//!
//! - an `Int` result past 2^31 traps (it fits until 2^63 on desktop), and so
//!   does an `Int` literal past 2^31, when it is evaluated;
//! - a `Float` carries 24 bits of mantissa, not 53, and prints that way: the
//!   host formats the `f32` widened to `f64`, so `0.1 + 0.2` shows its noise;
//! - a `Float` past about 3.4e38 is infinity;
//! - `round`, `floor`, `ceil` and `truncate` give an `i32` `Int`, so a value
//!   past 2^31 is "can't be made a whole number";
//! - `sin`, `cos`, `tan` and `sqrt` return `f32`s, so they agree with desktop
//!   to about 7 digits rather than 15.
//!
//! The whole differential suite also runs on the embedded profile with
//! `GOAT_PROFILE=embedded cargo test -p goat_cli --test differential --test
//! stdlib --test foreign --test groups --test constraints --test prelude
//! --test numbers --test turtle`. Each failure there is one of the differences above:
//! `numbers_print_without_exponent` (`0.1 + 0.2`);
//! `a_tail_call_in_an_arm_runs_in_constant_stack`,
//! `deep_tail_recursion_runs_in_constant_stack`,
//! `long_lists_do_not_overflow_the_stack` and `prelude_definitions_run` (sums
//! past 2^31); the tests that build a million-link structure
//! (`equality_on_long_lists_uses_constant_stack`, `a_loop_runs_in_constant_stack`,
//! `a_million_link_list_is_counted_and_then_dropped` and the dropped-chain tests),
//! which trap on the embedded heap budget (ADR 0026);
//! `the_circle_example_renders_to_its_golden` (f32 `sin` moves the
//! SVG coordinates); and nine in `numbers`, which pins 64-bit and 15-digit answers
//! (`an_int_is_a_64_bit_integer`, `an_int_at_the_edge_does_not_trap`,
//! `the_most_negative_int_floor_divides_by_minus_one_only_as_a_remainder`,
//! `a_float_follows_ieee_and_never_traps`, `rounding_a_float_with_no_int_traps`,
//! `round_floor_ceil_and_truncate_turn_a_float_into_an_int`,
//! `the_result_of_a_rounding_function_is_an_int`,
//! `trig_takes_degrees_and_is_exact_at_the_quarter_turns` and
//! `trig_keeps_the_pythagorean_identity_all_the_way_round`). The cases of those
//! tests that fit in 32 bits are repeated below on both profiles.

use std::fs;

use goat::Profile::{self, Desktop, Embedded};
use goat_cli::turtle::Command;
use goat_mir::interp::{self, InterpError};

#[allow(dead_code)]
mod support;

use support::{TestHost, compiled_on, interpret_on};

const OVERFLOW: &str = "this number got too big";

/// The printed lines of `src` on `profile`, which the interpreter and wasm
/// must agree on, with nothing left allocated by either.
fn run_on(profile: Profile, src: &str) -> String {
    let (expected, live) = interpret_on(profile, goat_checker::PRELUDE, src, &mut goat::NoHost);
    assert_eq!(live, 0, "interpreter leaked on {profile:?}: {src}");
    let (printed, wasm_live) = compiled_on(profile, goat_checker::PRELUDE, src);
    assert_eq!(wasm_live, 0, "wasm leaked on {profile:?}: {src}");
    assert_eq!(
        printed, expected,
        "wasm differs from interp on {profile:?}: {src}"
    );
    expected.join("\n")
}

/// The message `src` traps with on `profile`, the same in both backends.
fn trap_on(profile: Profile, src: &str) -> String {
    let checked = goat_checker::check(src).expect("type-checks");
    let program = goat_mir::mono_for(&checked, profile).expect("monomorphizes");
    assert_eq!(goat_mir::verify(&program), Ok(()), "{src}");
    let Err(InterpError::Trap(message)) = interp::run(&program) else {
        panic!("the interpreter should trap on {profile:?}: {src}");
    };
    let (wasm, _) =
        goat::compile_for(profile, src, &goat::HostInterface::turtle()).expect("compiles");
    let error = goat_cli::run(&wasm).err().expect("wasm should trap");
    assert_eq!(error, format!("trap: {message}"), "{src}");
    message
}

fn same_on_both(src: &str) -> String {
    let desktop = run_on(Desktop, src);
    assert_eq!(run_on(Embedded, src), desktop, "profiles differ: {src}");
    desktop
}

fn differs(src: &str, desktop: &str, embedded: &str) {
    assert_eq!(run_on(Desktop, src), desktop, "desktop: {src}");
    assert_eq!(run_on(Embedded, src), embedded, "embedded: {src}");
}

fn example(file: &str) -> String {
    let path = format!("{}/../examples/{file}", env!("CARGO_MANIFEST_DIR"));
    fs::read_to_string(path).unwrap()
}

#[test]
fn every_example_prints_the_same_on_both_profiles() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../examples");
    let mut seen = 0;
    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        let driven_by_a_host = [
            "interactive.goat",
            "arrow_draw.goat",
            "shapes.goat",
            "spiral.goat",
            "circle.goat",
            "whole_numbers.goat",
        ]
        .iter()
        .any(|f| path.ends_with(f));
        if path.extension().is_some_and(|e| e == "goat") && !driven_by_a_host {
            same_on_both(&fs::read_to_string(&path).unwrap());
            seen += 1;
        }
    }
    assert!(seen >= 10, "found only {seen} examples");
}

#[test]
fn the_turtle_draws_the_same_spiral_on_both_profiles() {
    let commands = |profile| {
        let (wasm, _) = goat::compile_for(
            profile,
            &example("spiral.goat"),
            &goat::HostInterface::turtle(),
        )
        .unwrap();
        let (_, host) =
            goat_cli::run_with_host(&wasm, goat_cli::turtle::TurtleHost::default()).expect("runs");
        host.commands
    };
    let desktop = commands(Desktop);
    assert!(desktop.len() > 100);
    assert_eq!(commands(Embedded), desktop);
}

#[test]
fn the_turtle_draws_the_same_circle_to_f32_precision() {
    let commands = |profile| {
        let (wasm, _) = goat::compile_for(
            profile,
            &example("circle.goat"),
            &goat::HostInterface::turtle(),
        )
        .unwrap();
        let (_, host) =
            goat_cli::run_with_host(&wasm, goat_cli::turtle::TurtleHost::default()).expect("runs");
        host.commands
    };
    let (desktop, embedded) = (commands(Desktop), commands(Embedded));
    assert!(desktop.len() > 100);
    assert_eq!(desktop.len(), embedded.len());
    for (d, e) in desktop.iter().zip(&embedded) {
        match (d, e) {
            (Command::Forward(d), Command::Forward(e)) => assert!((d - e).abs() < 1e-4, "{d} {e}"),
            _ => assert_eq!(d, e),
        }
    }
}

#[test]
fn the_whole_numbers_example_agrees_where_it_is_exact() {
    let source = example("whole_numbers.goat");
    let (desktop, embedded) = (run_on(Desktop, &source), run_on(Embedded, &source));
    assert_eq!(desktop, embedded);
}

#[test]
fn floor_division_and_remainder_agree() {
    for (src, expected) in [
        ("7 // 2", "3"),
        ("-7 // 2", "-4"),
        ("7 // -2", "-4"),
        ("-7 // -2", "3"),
        ("-1 // 5", "-1"),
        ("7 % 3", "1"),
        ("-7 % 3", "2"),
        ("7 % -3", "-2"),
        ("-7 % -3", "-1"),
        ("-1 % 360", "359"),
        ("2147483647 // 2", "1073741823"),
        ("-2147483647 % 1000", "353"),
    ] {
        assert_eq!(same_on_both(&format!("print({src})")), expected, "{src}");
    }
    let rebuilds = "check = program(a, b) do (a // b) * b + a % b == a done
print(check(-2000000000, 7)); print(check(2000000000, -13)); print(check(-100, -9))";
    assert_eq!(same_on_both(rebuilds), "true\ntrue\ntrue");
}

#[test]
fn the_most_negative_embedded_int_floor_divides_by_minus_one_only_as_a_remainder() {
    let min = "min = 0 - 2147483647 - 1\n";
    assert_eq!(trap_on(Embedded, &format!("{min}min // (0 - 1)")), OVERFLOW);
    assert_eq!(run_on(Embedded, &format!("{min}print(min % (0 - 1))")), "0");
    assert_eq!(
        run_on(Embedded, &format!("{min}print(min // 1 == min)")),
        "true"
    );
    assert_eq!(
        run_on(Desktop, &format!("{min}print(min // (0 - 1))")),
        "2147483648"
    );
}

#[test]
fn division_by_zero_traps_on_both_profiles() {
    for src in ["1 // 0", "1 % 0", "zero = 3 - 3\n5 // zero"] {
        assert_eq!(trap_on(Desktop, src), "division by zero", "{src}");
        assert_eq!(trap_on(Embedded, src), "division by zero", "{src}");
    }
}

#[test]
fn rounding_gives_an_i32_int() {
    for (call, expected) in [
        ("round(2.4)", "2"),
        ("round(2.5)", "3"),
        ("round(-2.5)", "-3"),
        ("round(7)", "7"),
        ("floor(-2.1)", "-3"),
        ("ceil(2.1)", "3"),
        ("ceil(-2.7)", "-2"),
        ("truncate(-2.9)", "-2"),
        ("truncate(2147483520.0)", "2147483520"),
        ("truncate(0 - 2147483648.0)", "-2147483648"),
    ] {
        assert_eq!(same_on_both(&format!("print({call})")), expected, "{call}");
    }
    assert_eq!(
        same_on_both("print(change_each([1.5, 2.5, -2.5], round))"),
        "[2, 3, -3]"
    );
}

#[test]
fn rounding_a_float_past_i32_traps_only_on_embedded() {
    const NOT_WHOLE: &str = "this number can't be made a whole number";
    for call in [
        "truncate(2147483648.0)",
        "round(0 - 2147483904.0)",
        "floor(1e10)",
    ] {
        let src = format!("print({call})");
        assert_eq!(trap_on(Embedded, &src), NOT_WHOLE, "{call}");
        run_on(Desktop, &src);
    }
    assert_eq!(run_on(Desktop, "print(truncate(1e15))"), "1000000000000000");
    for call in ["round(1 / 0)", "floor(0.0 / 0.0)"] {
        let src = format!("print({call})");
        assert_eq!(trap_on(Desktop, &src), NOT_WHOLE, "{call}");
        assert_eq!(trap_on(Embedded, &src), NOT_WHOLE, "{call}");
    }
}

#[test]
fn round_sees_the_f32_it_is_given() {
    differs("print(round(0.49999999999999994))", "0", "1");
}

#[test]
fn sqrt_and_trig_are_exact_where_f32_can_be() {
    assert_eq!(same_on_both("print(sqrt(16))"), "4");
    assert_eq!(same_on_both("print(sqrt(2.25))"), "1.5");
    assert_eq!(same_on_both("print(sin(30)); print(cos(60))"), "0.5\n0.5");
    let quarter_turns = "for d from 0 to 4 do print(round(100 * sin(d * 90))) done";
    assert_eq!(same_on_both(quarter_turns), "0\n100\n0\n-100\n0");
}

#[test]
fn sqrt_and_trig_return_f32s_on_embedded() {
    differs("print(sqrt(2))", "1.4142135623731", "1.41421353816986");
    differs("print(tan(45))", "1", "0.999999940395355");
    differs(
        "print(sin(1000))",
        "-0.984807753012208",
        "-0.984807729721069",
    );
}

#[test]
fn an_int_counter_feeds_trig_and_sqrt_on_both() {
    let program = "for i from 0 to 4 do print(round(100 * sin(i * 90)) + round(sqrt(i * i))) done";
    assert_eq!(same_on_both(program), "0\n101\n2\n-97\n4");
}

#[test]
fn whole_number_and_decimal_arithmetic_agree() {
    assert_eq!(same_on_both("print(7 * 6 - 2)"), "40");
    assert_eq!(same_on_both("print(7 / 2)"), "3.5");
    assert_eq!(same_on_both("print(3 + 1.5)"), "4.5");
    assert_eq!(same_on_both("print(2 * 0.25)"), "0.5");
    assert_eq!(same_on_both("print(2147483647)"), "2147483647");
    assert_eq!(same_on_both("print(0 - 2147483647 - 1)"), "-2147483648");
    assert_eq!(same_on_both("print(46340 * 46340)"), "2147395600");
    assert_eq!(same_on_both("print(3 < 3.5)"), "true");
    assert_eq!(same_on_both("print(2147483647 > 2147483646)"), "true");
}

#[test]
fn numbers_survive_a_trip_through_records_closures_and_lists() {
    assert_eq!(
        same_on_both("print({x: 1, y: 2.5}); print([1, 2, 3])"),
        "{x: 1, y: 2.5}\n[1, 2, 3]"
    );
    let adder = "adder = program(n) do program(x) do x + n done done\nprint(adder(0.5)(2))";
    assert_eq!(same_on_both(adder), "2.5");
    assert_eq!(
        same_on_both("print(sum([0.5, 0.25]) + sum([1, 2]))"),
        "3.75"
    );
}

#[test]
fn an_int_traps_past_two_to_the_thirty_first() {
    assert_eq!(run_on(Desktop, "print(2147483647 + 1)"), "2147483648");
    for src in [
        "2147483647 + 1",
        "x = 0 - 2147483647\nx - 2",
        "46341 * 46341",
        "65536 * 32768",
        "min = 0 - 2147483647 - 1\nmin * (0 - 1)",
        "min = 0 - 2147483647 - 1\n0 - min",
        "add = program(a, b) do a + b done\nadd(2147483647, 1)",
        "sum([2147483647, 1])",
    ] {
        assert_eq!(trap_on(Embedded, src), OVERFLOW, "{src}");
    }
}

#[test]
fn the_largest_embedded_int_still_fits() {
    assert_eq!(run_on(Embedded, "print(0 - 2147483647 - 1)"), "-2147483648");
    assert_eq!(
        run_on(Embedded, "x = 0 - 2147483647\nprint(x - 1)"),
        "-2147483648"
    );
    assert_eq!(run_on(Embedded, "print(1073741823 * 2 + 1)"), "2147483647");
}

#[test]
fn an_int_literal_past_two_to_the_thirty_first_traps_only_when_it_runs() {
    assert_eq!(run_on(Desktop, "print(3000000000)"), "3000000000");
    assert_eq!(trap_on(Embedded, "print(3000000000)"), OVERFLOW);
    assert_eq!(trap_on(Embedded, "3000000000 - 1"), OVERFLOW);
    let skipped = "pick = program(b) do if b then 3000000000 else 1 done done\nprint(pick(false))";
    assert_eq!(same_on_both(skipped), "1");
}

#[test]
fn dividing_by_zero_is_infinity_on_both() {
    assert_eq!(same_on_both("zero = 0\nprint(1 / zero > 5)"), "true");
}

#[test]
fn a_float_keeps_24_bits_of_mantissa() {
    differs("print(16777216.0 + 1.0)", "16777217", "16777216");
    differs("print(16777217.0)", "16777217", "16777216");
    differs("print(16777217 + 0.5)", "16777217.5", "16777216");
    differs("print(0.1 + 0.2)", "0.3", "0.300000011920929");
    differs("print(1 / 3)", "0.333333333333333", "0.333333343267441");
    differs("print(0.1)", "0.1", "0.100000001490116");
}

#[test]
fn a_float_past_the_f32_range_is_infinity() {
    differs("print(1e39)", "1e+39", "inf");
    differs("print(1e38 * 10)", "1e+39", "inf");
}

#[test]
fn host_functions_cross_the_boundary_at_f64_and_i64() {
    let decls = "double = foreign \"test\" \"double\" (Number) -> Number\n\
                 count = foreign \"test\" \"count\" () -> Int\n\
                 bump = foreign \"test\" \"bump\" (Int) -> Int\n";
    for profile in [Desktop, Embedded] {
        let src =
            format!("{decls}print(double(21.5)); print(bump(count()) * 2); print(count() / 2)");
        let mut oracle = TestHost::default();
        let (expected, _) = interpret_hosted_on(profile, &src, &mut oracle);
        let (wasm, _) = goat::compile_for(profile, &src, &goat::HostInterface::turtle()).unwrap();
        let (run, compiled) = goat_cli::run_with_host(&wasm, TestHost::default()).unwrap();
        assert_eq!(run.printed, expected, "{profile:?}");
        assert_eq!(expected, ["43", "16", "3.5"], "{profile:?}");
        assert_eq!(compiled.log, oracle.log, "{profile:?}");
        assert_eq!(
            oracle.log,
            ["double(21.5)", "count()", "bump(7)", "count()"]
        );
    }
}

fn interpret_hosted_on(profile: Profile, src: &str, host: &mut TestHost) -> (Vec<String>, usize) {
    interpret_on(profile, goat_checker::PRELUDE, src, host)
}

#[test]
fn a_host_number_is_rounded_to_f32_on_the_way_in() {
    let src = "double = foreign \"test\" \"double\" (Number) -> Number\nprint(double(0.1))";
    let mut oracle = TestHost::default();
    let (expected, _) = interpret_hosted_on(Embedded, src, &mut oracle);
    assert_eq!(expected, ["0.200000002980232"]);
    assert_eq!(oracle.log, ["double(0.100000001490116)"]);
    let (wasm, _) = goat::compile_for(Embedded, src, &goat::HostInterface::turtle()).unwrap();
    let (run, compiled) = goat_cli::run_with_host(&wasm, TestHost::default()).unwrap();
    assert_eq!(run.printed, expected);
    assert_eq!(compiled.log, oracle.log);
}

#[test]
fn an_interactive_program_is_not_yet_supported_on_embedded() {
    let source = example("interactive.goat");
    assert!(goat::compile_for(Desktop, &source, &goat::HostInterface::turtle()).is_ok());
    let errors = goat::compile_for(Embedded, &source, &goat::HostInterface::turtle()).unwrap_err();
    assert!(errors[0].message.contains("embedded profile"), "{errors:?}");
}
