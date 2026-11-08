# ADR 0017 — Int/Float split: the surface rules

- Status: accepted (2026-11-08)
- Context: implements the split [ADR 0001](0001-number-representation.md) deferred;
  `docs/plan.md` "Known limitation"; [ADR 0012](0012-trap-builtin.md) (runtime traps); #83.

## Context

ADR 0001 built MIR to carry both a per-target integer and float but kept the
checker on a single `Ty::Number` lowering to float, deferring the surface split
as "a separate larger ticket … revisit before the turtle ships for real." That
time is now: the turtle leans on division and trig (float) and on loop
counters / indices (int), and the FPU-less MCU targets (RP2040, ESP32-f32) need
a real int + `f32`.

We considered making `Number` an arbitrary-precision (bignum) type instead and
rejected it: bignums need unbounded heap (against the embedded pooled-heap /
bounded-stack budget), allocate on every operation (against goat's GC-free RC
model), have no native wasm form, and don't help the inherently-irrational
turtle math (trig/`sqrt`) anyway. goat is meant to stay capable enough for
embedded and, eventually, production use, so the split is **fixed-width and
hardware-mapped**, made *safe* rather than *unbounded*.

## Decision

1. **Two machine number types, one kid-facing name.** The checker gains `Int`
   and `Float`. `Number` stays the umbrella word kids use; `Int`/`Float` surface
   in a diagnostic only when an operation forces one.
2. **Literals.** A numeric literal with a decimal point or exponent is `Float`;
   otherwise `Int`. `3` : Int; `3.0`, `3.5`, `1e3` : Float.
3. **Division.** `/` always yields `Float` (`7 / 2 == 3.5`). Integer
   floor-division is `//` and remainder is `%`, both Int-only. Trig, `sqrt`, and
   `/` all live in Float.
4. **Mixing.** Int widens to Float implicitly in a mixed numeric expression or
   comparison (`3 + 1.5 == 4.5`). Float→Int is **never** implicit — it needs an
   explicit `round` / `floor` / `truncate`.
5. **Overflow traps, never wraps.** Int arithmetic that overflows its target
   width is a runtime trap carrying a spanned message (the ADR-0012 mechanism),
   not silent wraparound: a kid gets "this number got too big," never a wrong
   answer. Float follows IEEE-754 (inf/NaN) as today.
6. **Per-target width** (from ADR 0001): Int = `i64` desktop/web, `i32`
   embedded; Float = `f64` desktop/web, `f32` embedded. Pointer size is likewise
   a target parameter.

## Consequences

- The `Numeric` constraint ranges over {Int, Float}: a generic numeric function
  stays polymorphic, and widening is inserted at mixed sites; `Eq` / comparison
  span both. Prelude math (trig, `sqrt`, `/`) is typed to Float; counters and
  indexing to Int.
- "Errors come only from the checker" holds: overflow is a *defined runtime
  trap* on a well-typed program — the same category as the list-bounds traps
  ADR 0012 ratified — not a checker error and not a mono/codegen panic.
- MIR already carries the Int/Float slots (ADR 0001), so no new MIR shape; mono
  lowers each to the target's width.
- Kid-facing: the common case (draw with `+ - * /`, freely mix whole and
  decimal numbers) just works; the split shows only where it must — a loop
  counter wants a whole number, and going Float→Int is an explicit `round`.

## Implementation notes (foundation)

- **A whole-number literal is an unknown `Int` or `Float`** that settles as
  `Int` unless its context needs a `Float` — Haskell's defaulting, in the
  checker as a `Literal` constraint on a type variable. This is what lets
  `forward(100)`, `3 + 1.5` and `scale = program(x) do x * 2 done` called at
  `1.5` work without a conversion at every call: the `3` simply *is* `3.0`
  there. A *concrete* `Int` (a host function declared `-> Int`) beside a
  `Float` widens at the operator instead, and mono converts it.
- A binding that is not a function (`n = 3`) keeps its literals' types shared
  rather than generalized, so `n` is one number, `Float` once anything needs a
  `Float`; a function's literals stay free for each call to decide.
- `/` types its operands separately and always yields `Float`; the `Int` side
  of a quotient is converted. A record of numbers divides field by field, and
  its fields must be `Float`.
- `Int` and `Float` print as `Number` in a diagnostic; only a clash between the
  two (`take(1.5)` where `take` wants an `Int`) names them.
- **Overflow.** MIR's `BinInt` traps (`this number got too big`) where the
  result does not fit, in both the interpreter and wasm; mono wraps each `Int`
  operation in user code in a `Site`, so the trap is blamed on the operation.
- **Printing.** The host's `print_number` reads an `f64`, so an `Int` beyond
  2^53 prints as the `Float` nearest it. An `i64` print import is the fix.

## Implementation notes (semantics)

- **`//` and `%` floor.** `//` rounds toward negative infinity and `%` takes the
  sign of the divisor, so `-7 // 2 == -4`, `-7 % 3 == 2`, and
  `(a // b) * b + a % b == a` for every `a` and `b`. A kid's `angle % 360` is
  never negative. Both are `Int` only: a `Float` operand is a spanned checker
  error that points at `round`, `floor` and `truncate`. A zero divisor traps
  (`division by zero`); `i64::MIN // -1` traps like any overflow; `i64::MIN % -1`
  is `0`.
- **Two compiler primitives, the rest in the prelude.** `sqrt` and `truncate`
  are `foreign "math"` bindings that mono lowers to MIR's `FloatFn` instead of
  importing, so no host has to provide them. `floor`, `ceil` and `round` (halves
  go away from zero) are goat code over `truncate`; `truncate` traps
  (`this number can't be made a whole number`) on NaN, infinity or a value an
  `Int` cannot hold, never saturating.
- **Trig is goat code, in degrees.** `sin`, `cos` and `tan` take degrees, like
  the turtle's `left` and `right`. They split an angle into whole quarter turns
  and at most 45 degrees, then sum a Taylor series, so the same code runs
  identically on every target and multiples of 90 degrees are exact. Radians
  and the inverse functions are not provided yet.
- **An `Int` argument widens at a call.** A concrete `Int` passed where the
  callee's parameter is `Float` is accepted and converted, so `forward(7 // 2)`
  and `sin(i)` in a counting loop work. A host function that takes `Int` still
  rejects a `Float`.

## Embedded profile

`Program.profile` (`Desktop` or `Embedded`) carries the per-target widths of
decision 6 through mono (`mono_for`), the interpreter, and wasm emit.
`goat build|run --target embedded` and `goat::compile_for` select it; the
default is `Desktop`. Pointers are 4 bytes on both (wasm32), and object slots
stay 8 bytes wide.

- **Int** is an `i32`. wasm runs the operation in `i64`, where two `i32`s
  cannot overflow, then traps (`this number got too big`) if the result does
  not fit back. An `Int` literal past 2^31 becomes a runtime trap at its
  site, so the checker stays profile-blind and a literal on a branch that does
  not run is harmless.
  `//` and `%` take the same path, so `-2^31 // -1` traps and `-2^31 % -1`
  is `0`.
- **Float** is an `f32`. The interpreter rounds each `+ - * /`, `sqrt`,
  literal, and `Int` widening to `f32`, which is exactly what `f32` hardware
  computes because an `f64` carries more than twice the bits. The goat-code
  trig therefore runs in `f32` and agrees with desktop to about 7 digits.
- **Float to Int.** `truncate`, and so `round`, `floor` and `ceil`, give an
  `i32`: a value outside `[-2^31, 2^31)` traps with the same "can't be made a
  whole number" message desktop uses past 2^63.
- **Host boundary.** `print_number`, `write_number`, and every foreign import
  keep `f64` and `i64` whatever the profile, so one host serves both; the
  module converts at the edge. A host `Int` past 2^31 traps on the way in.
- **Not yet supported:** interactive programs on the embedded profile (the
  event exports take `Float` payloads at the program's own width).
  The heap budget and bounded stack are separate decisions.

`GOAT_PROFILE=embedded cargo test -p goat_cli` runs the differential suites on
the embedded profile; the failures there are the differences listed in
`cli/tests/embedded.rs`.

Where the profiles legitimately differ, `cli/tests/embedded.rs` pins both
answers: `Int` overflow at 2^31 (desktop 2^63), `Float` precision (a
`0.1 + 0.2` prints `0.300000011920929`, since the host formats the widened
`f32`), and a `Float` past 3.4e38 is `inf`. Every other example program prints
the same on both.

## Deferred

- `i64` Int on a future 64-bit *native* target (MIR has room).
- Rationals / arbitrary-precision decimals — not planned (bignum rejected above).
- Inverse trig (`atan2`, `asin`, `acos`), radians, and a `pi` constant.
