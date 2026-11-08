//! The conformance driver for WAMR's fast interpreter (ADR 0018, ADR 0019).
//! It adds no cases. It compiles in the suites that run compiled wasm, and
//! `support` sends that wasm to WAMR instead of wasmtime for every module
//! under this crate's `wamr` root, so each case that checks wasm against the
//! interpreter checks it here too: prints, host and `scene` calls, traps, and
//! `live == 0`.

// Each suite declares its own `mod support`; loading them again here is the point.
#![allow(clippy::duplicate_mod)]

#[path = "constraints.rs"]
mod constraints;
#[path = "differential.rs"]
mod differential;
#[path = "foreign.rs"]
mod foreign;
#[path = "groups.rs"]
mod groups;
#[path = "numbers.rs"]
mod numbers;
#[path = "prelude.rs"]
mod prelude;
#[path = "stdlib.rs"]
mod stdlib;
#[path = "turtle.rs"]
mod turtle;

#[allow(dead_code)]
mod support;

#[test]
fn the_suites_above_run_their_wasm_under_wamr() {
    assert!(support::uses_wamr());
}
