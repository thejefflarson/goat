//! Comparing two values nested too deeply to compare stops the program with a
//! message and the span of the comparison, the same on every backend. The suite
//! also runs under WAMR (`tests/wamr.rs`).

#![allow(clippy::duplicate_mod)]

#[allow(dead_code)]
mod support;

use goat::Profile;
use goat_mir::interp::{self, InterpError};
use goat_mir::{STACK_OVERFLOW, mono_for};

const NEST: &str =
    "nest = program(n, acc) do if n < 1 then acc else nest(n - 1, [acc]) done done\n";

fn program(comparison: &str) -> String {
    format!("{NEST}a = nest(300000, [])\nb = nest(300000, [])\nprint({comparison})")
}

fn wasm_of(src: &str) -> Vec<u8> {
    goat::compile(src, &goat::HostInterface::turtle()).expect("compiles")
}

fn stopped(src: &str) -> goat::native::Stopped {
    let wasm = wasm_of(src);
    let finished = if support::uses_wamr() {
        goat_wamr::run_to_end(&wasm, goat::NoHost).expect("loads")
    } else {
        goat::native::run_to_end(&wasm, goat::NoHost).expect("loads")
    };
    finished.result.expect_err("traps")
}

fn text_at(src: &str, (start, end): (usize, usize)) -> &str {
    &src[start..end]
}

#[test]
fn comparing_values_nested_too_deeply_says_so_and_names_the_comparison() {
    for comparison in ["a == b", "a != b", "a < b", "a >= b"] {
        let src = program(comparison);
        let stopped = stopped(&src);
        assert_eq!(stopped.message, STACK_OVERFLOW, "{comparison}");
        let site = stopped.site.expect("the stop names a range of the source");
        assert_eq!(text_at(&src, site), comparison);
    }
}

#[test]
fn the_interpreter_stops_with_the_same_message() {
    let checked = goat_checker::check(&program("a == b")).expect("type-checks");
    let mir = mono_for(&checked, Profile::Desktop).expect("monomorphizes");
    assert_eq!(
        interp::run(&mir),
        Err(InterpError::Trap(STACK_OVERFLOW.into()))
    );
}

#[test]
fn a_comparison_that_fits_still_answers() {
    let src = format!("{NEST}a = nest(50, [])\nb = nest(50, [])\nprint(a == b)");
    let run = support::execute(&wasm_of(&src)).expect("runs");
    assert_eq!(run.printed, ["true"]);
}
