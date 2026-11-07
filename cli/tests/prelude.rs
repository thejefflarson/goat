//! Programs run the same with a prelude wrapped around them, and prelude
//! definitions run through the interpreter and wasm alike.

use std::fs;

#[allow(dead_code)]
mod support;

use support::{run, run_with_prelude};

const PRELUDE: &str = "double = program(n) do n * 2 done\n\
                       apply = program(f, x) do f(x) done\n\
                       fib = program(n) do if n < 2 then n else fib(n - 1) + fib(n - 2) done done\n\
                       sum_to = program(n, acc) do if n < 1 then acc else sum_to(n - 1, acc + n) done done\n\
                       pair = program(a, b) do {first: a, second: b} done\n\
                       wrap = program(x) do Wrapped(x) done\n";

#[test]
fn prelude_definitions_run() {
    assert_eq!(run_with_prelude(PRELUDE, "double(21)"), "42");
    assert_eq!(run_with_prelude(PRELUDE, "apply(double, 4)"), "8");
    assert_eq!(run_with_prelude(PRELUDE, "fib(10)"), "55");
    assert_eq!(
        run_with_prelude(PRELUDE, "sum_to(1000000, 0)"),
        "500000500000"
    );
    assert_eq!(run_with_prelude(PRELUDE, "pair(1, true).second"), "true");
    let src = "match wrap(3) do Wrapped(n) then n + 1 done";
    assert_eq!(run_with_prelude(PRELUDE, src), "4");
}

#[test]
fn a_user_definition_shadows_a_prelude_one() {
    let src = "double = program(n) do n * 3 done  double(5)";
    assert_eq!(run_with_prelude(PRELUDE, src), "15");
}

#[test]
fn every_example_behaves_the_same_with_a_prelude_around_it() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../examples");
    let mut seen = 0;
    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        let uses_built_in_prelude = path.ends_with("stdlib.goat") || path.ends_with("spiral.goat");
        let driven_by_a_host =
            path.ends_with("interactive.goat") || path.ends_with("arrow_draw.goat");
        if path.extension().is_some_and(|e| e == "goat")
            && !uses_built_in_prelude
            && !driven_by_a_host
        {
            let src = fs::read_to_string(&path).unwrap();
            assert_eq!(
                run_with_prelude(PRELUDE, &src),
                run(&src),
                "{}",
                path.display()
            );
            seen += 1;
        }
    }
    assert!(seen >= 8, "found only {seen} examples");
}

#[test]
fn the_built_in_prelude_is_transparent() {
    assert_eq!(run("1 + 2"), run_with_prelude("", "1 + 2"));
}
