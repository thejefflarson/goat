# Fuzzing

Two tiers drive two targets. `check_never_panics` runs `goat_checker::check` on
arbitrary input and requires that nothing panics. `differential_interp_vs_wasm`
runs generated terminating, well-typed programs through the MIR interpreter and
through wasm under wasmtime, and requires equal output and zero live
allocations.

## CI tier (no nightly, no extra tools)

`checker/tests/fuzz_check.rs` uses `bolero::check!` as a bounded randomized
test. It runs under plain `cargo test` in the main workspace and also holds the
regression for deeply nested input. `cli/tests/fuzz_differential.rs` does the
same for the differential target (300 programs), and also plants a divergence
to check that bolero catches it and shrinks it to a short program.

The no-leak and no-double-free check on the wasm side (`goat_live_allocs() == 0`
after `goat_entry`; a double free traps with `unreachable`) rides on every
generated program, since the generator emits records, capturing closures and
curried closures that allocate and free. Three deterministic tests guard it
against going vacuous: `planted_leak_is_caught` makes the harness report a
leaked block and requires the run to fail; `real_leak_reaches_the_harness_count`
and `real_double_free_traps_in_the_harness_host` drive hand-built MIR that
really leaks or double-frees through the same `goat_cli::run` host. The
generator and runner live in `cli/tests/support/mod.rs`.

## Coverage-guided tier (manual or nightly)

Needs the `cargo-bolero` tool and a nightly toolchain:

    cargo install cargo-bolero
    cd fuzz
    cargo +nightly bolero test check_never_panics --engine libfuzzer
    cargo +nightly bolero test differential_interp_vs_wasm --engine libfuzzer

`--engine afl` also works if AFL++ is installed. Corpora and crashes land under
`fuzz/tests/__fuzz__/` (the corpus is git-ignored). Once a crash is fixed, add
it as a `#[test]` in `checker/tests/fuzz_check.rs`. For a differential
mismatch, bolero prints the shrunk input; feed it to
`support::generate` to recover the program, and add that source as a case in
`cli/tests/differential.rs`.

`bolero` is pinned to 0.13.4: newer releases pin `indexmap =2.11.2`, which
conflicts with the version `cranelift-object` needs in the main workspace.
