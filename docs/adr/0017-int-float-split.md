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

## Deferred

- `i64` Int on a future 64-bit *native* target (MIR has room).
- Rationals / arbitrary-precision decimals — not planned (bignum rejected above).
- The exact spelling of `round`/`floor`/`truncate` and whether `//`/`%` ship in
  the first cut or follow — an implementation-ticket call, within these rules.
