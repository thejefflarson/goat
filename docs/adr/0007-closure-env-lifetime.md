# ADR 0007 — Closure environment lifetime in Phase 4

- Status: accepted (2026-11-02)
- Context: Phase 4 (closures), ADR 0002, ADR 0006, `cli/tests/support/mod.rs`

## Context

A capturing closure (ADR 0006) allocates a heap environment with `rc = 1`.
"Does Phase 4 free it?" has a misleading short answer. "Closures leak until
Phase 6 RC" is half true, and taken unqualified it would tell the implementer
to skip `Drop` insertion — which fails every closure test. The phrase conflates
two different things, so this ADR separates them.

## Decision

Two senses of "leak", two different obligations:

| Sense | Phase 4 obligation |
|---|---|
| **Physical reclamation** — returning a freed block to an allocator for reuse | **Deferred to Phase 6.** The wasm bump allocator never reclaims: at `rc == 0` it runs the object's drop function but does not return the block. This is the existing Phase 3 reality for records and is fine. |
| **Logical refcount balance** — the reference interpreter's live-object count returning to 0 at program exit | **Required now.** `cli/tests/support/mod.rs` asserts `live == 0` on every differential and end-to-end run, and Phase 3 records already satisfy it. A closure env that is never `Drop`ped leaves `live > 0` and fails every closure test. |

So Phase 4 keeps refcounts balanced by **extending mono's existing targeted
closure-drop discipline** (`cx.live` / `leaf` / `use_closure` / the per-closure
`drop_fn`) to the real `rc = 1` heap closures it now allocates. That discipline
already drops function-value locals and the root object; today it is vacuous
because every closure is an immortal static whose `drop_fn` is `Noop`, and
Phase 4 makes it do real work.

This is **not** pulling reference counting forward. The general Perceus
dup/drop-insertion and in-place-reuse pass (`Unpack` / `ReuseVariant` / `Free`,
`rc == 1` update) stays Phase 6.

## Consequences

- Every closure env mono allocates reaches `rc = 0` and runs its `drop_fn`
  before exit, so `live == 0` holds and the interpreter's double-free and
  use-after-free checks, plus the verifier's "each owned pointer consumed
  exactly once on every path", catch any imbalance loudly rather than letting
  it miscompile silently.
- Physical memory is not reused within a run until Phase 6; a long-running
  program still grows linear memory. Acceptable for Phase 4's test programs and
  examples.
- The record-of-closures case already drops correctly: `release` on a closure
  kind calls the closure's own `drop_fn`, and `RecordDrop` recurses into
  closure-typed fields.
