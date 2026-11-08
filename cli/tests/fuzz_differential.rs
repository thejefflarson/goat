//! Fuzz target: generated programs must print the same under the interpreter
//! and wasm, and leave nothing live on either. Runs as a bounded test under `cargo test`
//! and coverage-guided via `cargo bolero` (see fuzz/README.md).

#[path = "../../mir/tests/common/mod.rs"]
mod common;
#[allow(dead_code)]
mod support;

use bolero::check;
use goat_mir::{Expr, MTy, Program};

#[test]
fn generated_programs_agree_between_interp_and_wasm() {
    check!()
        .with_iterations(300)
        .with_max_len(256)
        .for_each(|data: &[u8]| {
            support::agree_or_trap(&support::generate(data));
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

/// The leak half of the oracle: a wasm side that reports one live block must
/// fail the run. Without the `wasm_live == 0` assertion this passes silently.
#[test]
#[should_panic(expected = "wasm leaked allocations")]
fn planted_leak_is_caught() {
    support::run_observed("0 + (20)", |(printed, live)| (printed, live + 1));
}

fn run_wasm(program: &Program) -> Result<goat_cli::Run, String> {
    goat_cli::run(&goat_wasm::emit(program).expect("program emits"))
}

/// The same host path the harness reads (`goat_cli::run`) reports a block the
/// program allocated and never released, so the leak assertion has something
/// real to see.
#[test]
fn real_leak_reaches_the_harness_count() {
    let leak = common::program(vec![common::func(
        MTy::Int,
        common::let_(0, common::alloc_record(1), common::int(0)),
    )]);
    assert_eq!(run_wasm(&leak).expect("leaky program runs").live_allocs, 1);
}

/// A double release must trap rather than corrupt the free list, and the host
/// surfaces the trap as an error the differential harness would panic on.
#[test]
fn real_double_free_traps_in_the_harness_host() {
    let body: Expr = common::let_(
        0,
        common::alloc_record(1),
        common::let_(
            1,
            common::drop_(0),
            common::let_(2, common::drop_(0), common::int(0)),
        ),
    );
    let error = run_wasm(&common::program(vec![common::func(MTy::Int, body)]))
        .err()
        .expect("second release must trap");
    assert!(error.contains("trap"), "expected a trap, got {error}");
}
