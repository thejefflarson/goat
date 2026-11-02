# Fuzzing

Two tiers drive `goat_checker::check` with one invariant: no input panics.

## CI tier (no nightly, no extra tools)

`checker/tests/fuzz_check.rs` uses `bolero::check!` as a bounded randomized
test. It runs under plain `cargo test` in the main workspace and also holds the
regression for deeply nested input.

## Coverage-guided tier (manual or nightly)

Needs the `cargo-bolero` tool and a nightly toolchain:

    cargo install cargo-bolero
    cd fuzz
    cargo +nightly bolero test check_never_panics --engine libfuzzer

`--engine afl` also works if AFL++ is installed. Corpora and crashes land under
`fuzz/tests/__fuzz__/` (the corpus is git-ignored). Once a crash is fixed, add
it as a `#[test]` in `checker/tests/fuzz_check.rs`.

`bolero` is pinned to 0.13.4: newer releases pin `indexmap =2.11.2`, which
conflicts with the version `cranelift-object` needs in the main workspace.
