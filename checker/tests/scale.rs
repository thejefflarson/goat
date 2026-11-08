//! Checking time grows linearly with the number of statements in a block, so a
//! generated program of many thousands of them cannot hang the checker.

use goat_checker::check;
use std::time::{Duration, Instant};

const SMALL: usize = 2_000;
const LARGE: usize = 8_000;

/// Time to check `source`, on a stack big enough for the parser's nesting.
fn time_to_check(source: String) -> (Duration, Result<(), usize>) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || {
            let start = Instant::now();
            let result = check(&source).map(|_| ()).map_err(|errors| errors.len());
            (start.elapsed(), result)
        })
        .unwrap()
        .join()
        .unwrap()
}

fn repeated(count: usize, statement: impl Fn(usize) -> String) -> String {
    (0..count).map(statement).collect::<Vec<_>>().join("\n")
}

/// Quadratic growth would multiply the time by `(LARGE / SMALL)^2 = 16`;
/// linear growth by 4. The bound sits between, with room for a loaded machine.
fn assert_scales_linearly(shape: impl Fn(usize) -> String, one_error_per_statement: bool) {
    let expected = |n| {
        if one_error_per_statement {
            Err(n)
        } else {
            Ok(())
        }
    };
    let (small, result) = time_to_check(shape(SMALL));
    assert_eq!(result, expected(SMALL));
    let (large, result) = time_to_check(shape(LARGE));
    assert_eq!(result, expected(LARGE));
    assert!(
        large < small.max(Duration::from_millis(50)) * 10,
        "{SMALL} statements took {small:?}, {LARGE} took {large:?}"
    );
}

#[test]
fn a_chain_of_bindings_scales_linearly() {
    assert_scales_linearly(
        |n| {
            let chain = repeated(n, |i| format!("a{} = a{i} + 1", i + 1));
            format!("a0 = 0\n{chain}\na{n}")
        },
        false,
    );
}

#[test]
fn a_run_of_statements_scales_linearly() {
    assert_scales_linearly(|n| format!("{}1", "print(1); ".repeat(n)), false);
}

#[test]
fn a_run_of_functions_scales_linearly() {
    assert_scales_linearly(
        |n| {
            format!(
                "{}\n1",
                repeated(n, |i| format!("f{i} = program(x) do x + 1 done"))
            )
        },
        false,
    );
}

#[test]
fn far_away_names_resolve_in_constant_time() {
    assert_scales_linearly(
        |n| {
            let uses = repeated(n, |i| format!("a{i} = r.x\nprint(a{i});"));
            format!("r = {{x: 1}}\n{uses}\n1")
        },
        false,
    );
}

#[test]
fn a_run_of_erroring_field_reads_scales_linearly() {
    assert_scales_linearly(|n| format!("r = {{x: 1}}\n{}1", "r.y; ".repeat(n)), true);
}
