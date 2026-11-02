# ADR 0001 — Number representation: MIR splits Int/Float, the checker keeps one `Number`

- Status: accepted (2026-11-01)
- Context: Phase 1.5 (MIR design), `docs/plan.md`

## Context

`docs/plan.md` leaves two things open about numbers: whether `Int` is `i32`
or `i64`, and whether the surface language exposes an `Int`/`Float` split or a
single kid-facing `Number`. The split matters for microcontroller targets
(RP2040 has no FPU; ESP32 is single-precision), so the plan requires a
per-target float width (`f64` desktop/web, `f32` embedded). Today the checker
has a single `Ty::Number` and the Cranelift backend treats every number as
`f64`. Introducing a surface `Int`/`Float` distinction now would pull Phase 8's
`numeric`-constraint machinery and literal-typing rules forward into this
sprint.

## Decision

- **MIR carries both** an integer type (`Int`, width a per-target parameter —
  `i32` on wasm32, room for `i64` on a future 64-bit native target) and a
  `Float` whose width is a per-target parameter (`f64` desktop/web, `f32`
  embedded). Pointer size is likewise a target parameter, never hard-coded.
- **The checker keeps a single `Ty::Number` this sprint.** The literal →
  `Int`/`Float` mapping and the `numeric` constraint stay a Phase 8 concern.
  For now a `Number` lowers to the target's float.

## Consequences

- Phase 1.5 stays a design/spec exercise; no checker change rides along, and
  Phase 8's constraint work is not dragged forward.
- MIR is ready for the embedded float story without the frontend committing to
  it yet.
- Deferred: the moment kids do integer-heavy work (indices, counts) or we
  target an FPU-less board, the checker will need the split. That is a separate,
  larger ticket, explicitly out of this sprint. A drawing language leans on
  division and trig, so revisit the split before the turtle ships for real.
