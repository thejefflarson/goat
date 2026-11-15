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

/// Each binding wraps the one before it, so its type nests one level deeper
/// until it passes the depth limit and the binding fails; the next binding then
/// nests again from nothing. Every binding stays open (its literals are still
/// undecided), which made generalizing each one rescan every binding before it.
fn nested_bindings(count: usize) -> String {
    let chain = repeated(count, |i| format!("a{} = {{w: a{i}, v: {i}}}", i + 1));
    format!("a0 = 0\n{chain}\n1")
}

#[test]
fn bindings_that_keep_failing_scale_linearly() {
    const FEW: usize = 500;
    const MANY: usize = 2_000;
    let (few, few_errors) = time_to_check(nested_bindings(FEW));
    let (many, many_errors) = time_to_check(nested_bindings(MANY));
    assert!(matches!(few_errors, Err(n) if n > 0));
    assert!(matches!(many_errors, Err(n) if n > 0));
    assert!(
        many < few.max(Duration::from_millis(50)) * 10,
        "{FEW} bindings took {few:?}, {MANY} took {many:?}"
    );
}

#[test]
fn every_error_of_a_run_of_failing_bindings_is_spanned() {
    let source = nested_bindings(1_000);
    let errors = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn({
            let source = source.clone();
            move || goat_checker::check(&source).err().expect("errors")
        })
        .unwrap()
        .join()
        .unwrap();
    assert!(!errors.is_empty());
    for error in &errors {
        assert!(error.span.start < error.span.end && error.span.end <= source.len());
        assert!(error.message.starts_with("program too complex"));
    }
}

#[test]
fn a_run_of_erroring_field_reads_scales_linearly() {
    assert_scales_linearly(|n| format!("r = {{x: 1}}\n{}1", "r.y; ".repeat(n)), true);
}

/// `count` functions that each call the next, the last calling the first: one
/// group the checker generalizes after all of them are inferred.
fn cyclic_functions(count: usize) -> String {
    let functions = repeated(count, |i| {
        format!("f{i} = program(x) do f{}(x) done", (i + 1) % count)
    });
    format!("{functions}\nf0(true)")
}

/// A group in which each function mentions three others, spread across it.
fn dense_group(count: usize) -> String {
    let functions = repeated(count, |i| {
        let [a, b, c] = [1, 7, 13].map(|step| (i + step) % count);
        format!(
            "f{i} = program(x) do if true then f{a}(x) else if true then f{b}(x) else f{c}(x) done done done"
        )
    });
    format!("{functions}\nf0(true)")
}

#[test]
fn a_cyclic_group_scales_linearly() {
    assert_scales_linearly(cyclic_functions, false);
}

#[test]
fn a_dense_group_scales_linearly() {
    assert_scales_linearly(dense_group, false);
}

#[test]
fn a_group_of_two_thousand_functions_checks_quickly() {
    for source in [cyclic_functions(SMALL), dense_group(SMALL)] {
        let (time, result) = time_to_check(source);
        assert_eq!(result, Ok(()));
        assert!(time < Duration::from_secs(5), "took {time:?}");
    }
}
