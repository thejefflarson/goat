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
| `goat_checker` `proofs::occurs_finds_its_own_variable` | `occurs` / `occurs_row` report a variable standing alone, and not a different one | all `TypeVar` pairs |
| `goat_checker` `proofs::occurs_ignores_closed_leaves` | `occurs` is false for `Number`, `Str`, `Bool`, `Unit` | all `TypeVar` |
| `goat_mir` `interp::proofs::int_op_is_total_and_traps_only_on_zero_division` | `int_op` returns `Ok(Int)` except `Div` by zero, which traps | all `i64` pairs |
| `goat_mir` `interp::proofs::int_add_and_sub_wrap_on_overflow` | `Add`/`Sub` equal `wrapping_add`/`wrapping_sub` | all `i64` pairs |
| `goat_mir` `interp::proofs::int_op_rejects_non_int_operands` | non-`Int` operands give `Malformed`, never a panic | all `i64` |
| `goat_mir` `interp::proofs::int_compare_matches_rust_operators` | `compare` on ints agrees with `==`, `!=`, `<`, `<=`, `>`, `>=` | all `i64` pairs |
| `goat_mir` `interp::proofs::float_compare_matches_ieee_including_nan` | `compare` on floats agrees with the IEEE operators, NaN included | all `f64` pairs |
| `goat_mir` `interp::proofs::compare_rejects_mixed_operands` | int/float operands give `Malformed` | all `i64`/`f64` |
| `goat` `proofs::format_bool_matches_spec` | `format_bool(b)` is `"true"` / `"false"` for both inputs | all `bool` |

## Running locally

    cargo install --locked kani-verifier --version 0.68.0
    cargo kani setup
    cargo kani -p goat_wasm -p goat -p goat_checker -p goat_mir

Run one harness with `cargo kani -p goat_wasm --harness slot_never_overflows`.

CI runs this nightly in `.github/workflows/verify.yml`. It is not a required
check.

## Not covered by Kani

- `format_number`: the integer fast path ends in `i64::to_string`, and the
  rest in `format!("{x:.14e}")`. Both run `core::fmt`'s float and integer
  formatters, which CBMC does not finish in a useful time. Fuzzing and the
  unit tests cover it.
- `subst_vars` / `subst_row`: they take a `HashMap`, whose SipHash and
  hashbrown probing, plus symbolic `Box`/`Vec`/`String` trees, did not finish
  under CBMC in local trials. The unit tests cover them.
- Any `occurs` proof over symbolic `Ty` trees, and the `&mut self`
  inferencer (stateful, built on `HashMap`s): the heap-allocated recursive
  `Ty`/`Row` values stalled the solver, so only the non-allocating cases above
  are proved.
