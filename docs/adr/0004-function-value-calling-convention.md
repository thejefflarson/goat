# ADR 0004 — Function-value calling convention under mono

- Status: accepted (2026-11-01)
- Context: Phase 2 (mono → MIR), `docs/plan.md`, `docs/mir.md`

## Context

Higher-order parity needs function *values* — a function passed as an argument,
stored in a record field, or returned — even though capturing closures stay
rejected until Phase 4. Mono must decide, per use, whether a function name
becomes a direct call or a materialized closure value, and how a
function-typed parameter is called. The old Cranelift backend split this by
representing every function as a raw code pointer; the typed MIR world needs an
explicit rule.

## Decision

- A `Var` naming a top-level function **in callee position, applied at a known
  arity → `CallDirect`** (no closure, no indirection).
- The same function **in value position** (argument, record field, returned) →
  **`MakeClosure` of a zero-capture wrapper**, backed by a **static immortal
  closure** (`rc = u32::MAX`, `drop_fn`, `code` = funcref-table index, no
  captures) placed in the `data` segment.
- A **function-typed parameter or local** (e.g. `apply`'s `f`) is
  `Ptr(Closure(sig))` and is called via **`CallClosure`** (load `code`,
  `call_indirect` with the closure as `env`).
- The funcref `table` holds one element per indirectly-callable function.
- Because static closures are immortal, mono **re-materializes** them at each
  value use instead of emitting `Dup`/`Drop`. This satisfies the verifier's
  "each owned pointer consumed exactly once" rule while keeping the general
  reference-counting insertion pass a Phase 6 concern.

## Consequences

- Direct recursion and ordinary calls stay zero-overhead (`CallDirect`).
- Function values and higher-order calls work at parity without a general RC
  pass, because the only closures Phase 2 creates are immortal statics.
- This is internal lowering (reversible), but it is the shape Phase 4 (real
  capturing closures) builds on, so it is recorded. The closure object layout
  and `env`-relative offsets follow `docs/mir.md`; offsets are computed per
  target, never hard-coded.
