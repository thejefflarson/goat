# ADR 0025 — Embedded profile: document WAMR's fast-interp cell limit; defer function splitting

- Status: accepted (2026-11-09)
- Decision: treat WAMR's fast-interpreter per-function limit — a function whose
  locals plus operand stack exceed **32767 cells** is refused at module load — as a
  **documented embedded-profile limit**, not a goat bug. goat keeps emitting the
  function it does today; the embedded conformance driver runs such programs under
  WAMR's **classic** interpreter (which has no such cap), and the limit is recorded
  for the embedded profile. We **defer** a codegen pass that would split an
  oversized function into smaller ones until a real program hits the cap.
- Context: Phase 12 (`docs/plan.md` "Microcontrollers"), #267. WAMR's fast interp
  encodes a function's frame size in a 16-bit field, so it rejects at load any
  function needing more than 32767 cells. goat accepts and compiles these functions;
  wasmtime and WAMR classic run them; only WAMR fast-interp refuses them. This is a
  desktop-vs-embedded **capability gap**, discovered via the `wamr` conformance
  driver (#266), not a miscompile. Builds on ADR 0019 (WAMR on-device now), ADR 0017
  (the i32/f32 embedded profile), and ADR 0018 (one Rust conformance suite, a thin
  driver per host).

## Why document-and-defer rather than split now

A splitting pass is real codegen work (extract a frame-heavy region into a called
helper, thread the live values across the call) with its own correctness burden, and
it buys nothing a kid will reach. The cap is 32767 **cells** in one function — a
single goat function would need thousands of simultaneous live bindings to approach
it. Nothing in the kid-facing surface (short turtle programs, `init`/`update`/`draw`
sketches) comes close. Spending a codegen pass on a limit no real program hits is
effort against a non-problem, and the pass would have to be carried and verified
forever after.

The classic interpreter removes the cap outright at a modest speed cost, so the
embedded conformance path stays green by selecting it for any program that would trip
the fast-interp limit. That keeps the differential suite honest (every well-typed
program still runs on the embedded oracle) without a codegen change.

## What this commits us to

- The embedded profile's documentation states the fast-interp 32767-cell limit and
  that the classic interpreter lifts it; `wamr`'s driver selects the interpreter
  accordingly.
- goat emits no error for an oversized function: this is a runtime/host capability
  fact, and per the project invariant errors come only from the checker. A program
  that cannot load on a given interpreter is a host limitation, surfaced by the host,
  not a goat diagnostic.
- If a future real program (plausibly machine-generated, not hand-written by a kid)
  hits the cap on the fast interp **and** needs fast-interp speed, that is the signal
  to build the splitting pass — and this ADR is where the deferral is recorded, so
  the reversal is deliberate.
