# ADR 0005 — Diagnostics for features that type-check but have no runtime yet

- Status: accepted (2026-11-01)
- Context: Phase 2 (staged backend), `CLAUDE.md`, `docs/plan.md`

## Context

CLAUDE.md states the invariant: *user-facing errors come only from the checker;
mono/MIR/codegen failing is an internal compiler bug.* But the backend ships in
phases, so a program can type-check yet use a runtime feature whose phase has
not landed — records and strings at runtime, variants — in Phase 2. Today's
Cranelift backend already returns a spanned "not supported yet" `CompileError`
for records/strings. We need a defined, consistent behavior that reconciles the
staged backend with the invariant, rather than a panic or silent wrong output.

## Decision

A program that type-checks but reaches a runtime feature whose phase has not
landed produces a **spanned, user-facing "… is not supported yet"
diagnostic** at the mono/lowering boundary, explicitly classified as a
**temporary known limitation**, not an internal-compiler-bug panic. It names
the feature and points at the offending span.

This narrows the invariant's wording: the checker remains the source of
*type* errors, and mono/codegen never panic on well-typed input; a
"not-supported-yet" limitation is a distinct, sanctioned, user-facing class
that disappears as later phases land.

## Consequences

- `examples/records.goat` and string-valued programs type-check and, under
  Phase 2, get a clear "records/strings not supported yet" notice — they are
  Phase 3/5 examples, not Phase 2 failures.
- No panic or silent miscompile for in-progress features; the message tells a
  user it is a staging gap, not their mistake.
- Each such diagnostic is removed by the phase that implements the feature.
  Phase 4 removes the mono capture and anonymous-literal diagnostics (ADR 0006);
  records landed in Phase 3; strings remain until Phase 5.
