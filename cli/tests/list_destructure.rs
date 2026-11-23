//! `[a, b] = xs` and `program([a, b])` take apart any list. A length the
//! pattern doesn't fit stops the program at the pattern, with the same
//! message from the interpreter and from wasm.

use goat_mir::interp::{self, InterpError};

#[allow(dead_code)]
mod support;

use support::run;

fn interp_error(src: &str) -> InterpError {
    let checked = goat_checker::check(src).expect("type-checks");
    let program = goat_mir::mono(&checked).expect("monomorphizes");
    assert_eq!(goat_mir::verify(&program), Ok(()), "{src}");
    interp::run(&program).expect_err("the program should trap")
}

fn wasm_error(src: &str) -> String {
    support::trap_text(src)
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
fn a_list_of_the_right_length_is_taken_apart() {
    assert_eq!(run("xs = [3, 4]\n[a, b] = xs\nprint(a * b)"), "12");
    assert_eq!(
        run("xs = [1, 2, 3, 4]\n[first, ...rest] = xs\nprint(first);\nprint(rest)"),
        "1\n[2, 3, 4]"
    );
    assert_eq!(run("xs = [1]\n[a, ...r] = xs\nprint(r)"), "[]");
    assert_eq!(run("xs = reverse([1, 2])\n[a, b] = xs\nprint(a)"), "2");
}

#[test]
fn a_list_parameter_pattern_is_taken_apart() {
    assert_eq!(
        run("f = program([x, y]) do x - y done\nprint(f([9, 4]))"),
        "5"
    );
    assert_eq!(
        run("f = program([x], [y, ...r]) do x + y done\nprint(f([1], [2, 3]))"),
        "3"
    );
}

#[test]
fn a_list_that_is_too_long_stops_the_program() {
    assert_traps(
        "xs = [1, 2, 3]\n[a, b] = xs\nprint(a)",
        "this list has more than 2 items but the pattern takes 2",
    );
}

#[test]
fn a_list_that_is_too_short_stops_the_program() {
    assert_traps(
        "xs = [1]\n[a, b] = xs\nprint(a)",
        "this list has 1 item but the pattern takes 2",
    );
    assert_traps(
        "xs = [1, 2]\n[a, b, c, ...r] = xs\nprint(a)",
        "this list has 2 items but the pattern takes at least 3",
    );
}

#[test]
fn an_empty_list_stops_the_program() {
    assert_traps(
        "xs = keep([1], program(n) do n > 5 done)\n[a, b] = xs\nprint(a)",
        "this list is empty but the pattern takes 2",
    );
    assert_traps(
        "xs = keep([1], program(n) do n > 5 done)\n[a, ...r] = xs\nprint(a)",
        "this list is empty but the pattern takes at least 1",
    );
}

#[test]
fn a_list_parameter_pattern_stops_the_program_on_a_wrong_length() {
    assert_traps(
        "f = program([x, y]) do x done\nprint(f([1, 2, 3]))",
        "this list has more than 2 items but the pattern takes 2",
    );
    assert_traps(
        "f = program([x, y]) do x done\nprint(f([1]))",
        "this list has 1 item but the pattern takes 2",
    );
}
