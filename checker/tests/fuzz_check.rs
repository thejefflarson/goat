//! Property tests for the frontend. `bolero::check!` runs as an ordinary
//! randomized test under `cargo test`; the same targets run coverage-guided
//! via `cargo bolero` (see fuzz/README.md).

use bolero::check;

const ITERATIONS: usize = 2_000;
const MAX_STRING_BYTES: usize = 4_096;

#[test]
fn check_never_panics_on_utf8() {
    check!()
        .with_iterations(ITERATIONS)
        .with_max_len(256)
        .for_each(|data: &[u8]| {
            if let Ok(source) = std::str::from_utf8(data) {
                let _ = goat_checker::check(source);
            }
        });
}

#[test]
fn check_never_panics_on_strings() {
    check!()
        .with_iterations(ITERATIONS)
        .with_max_len(MAX_STRING_BYTES)
        .with_type::<String>()
        .for_each(|source| {
            let _ = goat_checker::check(source);
        });
}

fn assert_clean_error(source: &str) {
    let errors = goat_checker::check(source)
        .err()
        .expect("deeply nested input must be rejected");
    assert!(!errors.is_empty());
}

#[test]
fn deep_nesting_is_a_clean_error() {
    let depth = 100_000;
    assert_clean_error(&format!("{}1{}", "(".repeat(depth), ")".repeat(depth)));
    assert_clean_error(&format!("{}1", "-".repeat(depth)));
    assert_clean_error(&"f(".repeat(depth));
}

#[test]
fn a_long_block_is_checked_and_dropped_without_overflowing_the_stack() {
    let length = 30_000;
    let statements = format!("{}1", "1; ".repeat(length));
    assert!(goat_checker::check(&statements).is_ok());
    let bindings = (0..length)
        .map(|i| format!("a{i} = 1\n"))
        .collect::<String>();
    assert!(goat_checker::check(&format!("{bindings}a0")).is_ok());
    assert_clean_error(&format!("{bindings}missing"));
}
