//! Fuzz target: generated programs must print the same under the interpreter
//! and wasm, and leave nothing live on either. Runs as a bounded test under `cargo test`
//! and coverage-guided via `cargo bolero` (see fuzz/README.md).

#[allow(dead_code)]
mod support;

use bolero::check;

#[test]
fn generated_programs_agree_between_interp_and_wasm() {
    check!()
        .with_iterations(300)
        .with_max_len(256)
        .for_each(|data: &[u8]| {
            support::run(&support::generate(data));
        });
}

/// Wasm output that is wrong for any result of 10 or more.
fn planted_bug(printed: Vec<String>) -> Vec<String> {
    printed
        .into_iter()
        .map(|line| match line.parse::<f64>() {
            Ok(n) if n >= 10.0 => format!("{}", n + 1.0),
            _ => line,
        })
        .collect()
}

/// The differential harness must catch a wrong wasm result. If this passed with
/// a no-op tamper it would prove nothing, so it plants a real divergence (the
/// result is 20, which `planted_bug` rewrites to 21) and asserts the comparison
/// fires. This is the oracle's self-check: a silent miscompile cannot slip past
/// `generated_programs_agree_between_interp_and_wasm`.
#[test]
#[should_panic(expected = "wasm differs from interp")]
fn planted_divergence_is_caught() {
    support::run_with("0 + (20)", planted_bug);
}
