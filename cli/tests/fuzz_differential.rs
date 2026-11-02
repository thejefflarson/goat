//! Fuzz target: generated programs must print the same under the interpreter
//! and wasm, and leave nothing live. Runs as a bounded test under `cargo test`
//! and coverage-guided via `cargo bolero` (see fuzz/README.md).

#[allow(dead_code)]
mod support;

use std::panic::{self, AssertUnwindSafe};
use std::sync::Mutex;
use std::time::Duration;

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

#[test]
fn planted_divergence_is_caught_and_shrunk_to_a_minimal_program() {
    let shortest_failure = Mutex::new(String::new());
    let hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));
    let caught = panic::catch_unwind(AssertUnwindSafe(|| {
        check!()
            .with_shrink_time(Duration::from_secs(5))
            .with_iterations(2_000)
            .with_type::<Vec<u8>>()
            .for_each(|data| {
                let src = support::generate(data);
                let outcome = panic::catch_unwind(|| support::run_with(&src, planted_bug));
                if let Err(panic) = outcome {
                    let mut shortest = shortest_failure.lock().unwrap();
                    if shortest.is_empty() || src.len() < shortest.len() {
                        *shortest = src;
                    }
                    drop(shortest);
                    panic::resume_unwind(panic);
                }
            });
    }));
    panic::set_hook(hook);
    assert!(caught.is_err(), "planted divergence must be caught");
    let minimal = shortest_failure.into_inner().unwrap();
    assert!(minimal.len() < 100, "not shrunk: {minimal}");
}
