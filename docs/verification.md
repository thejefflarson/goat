# Verification

Kani is a bounded model checker for Rust. It explores every input up to a
stated bound symbolically and proves that no assertion or arithmetic check
fires, which a fuzzer can only sample.

The harnesses are native `#[kani::proof]` functions in a `#[cfg(kani)] mod
proofs` beside the code they check, so ordinary `cargo build` and `cargo test`
never see them. They call the same pure functions the compiler uses. Bolero's
Kani backend is not used: the pure function is the contract, and a plain
harness avoids coupling the proofs to the bolero pin (see `fuzz/README.md`).

| Harness | Property | Bound |
| --- | --- | --- |
| `goat_wasm` `proofs::slot_never_overflows` | `layout::slot(HEADER, i)` does not overflow `u32` and is 8-byte aligned | `i <= (u32::MAX - HEADER) / SLOT` |
| `goat_wasm` `proofs::object_size_is_aligned_and_covers_slots` | `layout::object_size(HEADER, n)` does not overflow, is a multiple of 8, and is at least `HEADER` and `slot(HEADER, n)` | `n <= (u32::MAX - HEADER) / SLOT` |
| `goat` `proofs::format_bool_matches_spec` | `format_bool(b)` is `"true"` / `"false"` for both inputs | all `bool` |

## Running locally

    cargo install --locked kani-verifier --version 0.68.0
    cargo kani setup
    cargo kani -p goat_wasm -p goat

Run one harness with `cargo kani -p goat_wasm --harness slot_never_overflows`.

CI runs this nightly in `.github/workflows/verify.yml`. It is not a required
check.
