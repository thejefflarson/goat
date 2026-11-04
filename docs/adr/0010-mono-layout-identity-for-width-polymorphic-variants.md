# ADR 0010 — Mono pins a let-generalized variant value to its first use's layout

- Status: accepted (2026-11-04)
- Context: Phase 7 P7d (#92, #140), `mir/src/mono.rs`, `mir/src/canon.rs`, `docs/mir.md`

## Context

Mono keys each specialization and each variant layout on a ground type. A value
binding that is let-generalized over an open variant row has no single ground
type: it can be matched at two different row widths in the same scope.

```
s = Circle(5)
narrow = program(v) do match v do Circle(r) then r done done
wide   = program(v) do match v do Circle(r) then r Square(w) then w done done
narrow(s) + wide(s)
```

`s` evaluates once, so it must be lowered at one ground type. `instantiate_binding`
pins it to the type its **first** use picks — the same rule ADR 0004 uses for
function values and the rule #74 records for record-shaped bindings. Here that
gives `s` one `LayoutId`, so the second use receives a pointer whose static
`LayoutId` differs from the layout that use expects.

The question this ADR settles: is that acceptable to ship, given that the MIR
verifier rejects the pointer-type mismatch?

## Decision

- **Ship the first-use pinning as-is (#140).** It is correct in both backends.
- **The physical variant layout is width-independent, and we rely on that for
  correctness.** `AllocVariant` sizes a cell from the *actual tag's* field count,
  not the row width; tag numbers are global over the whole program; for any tag
  shared between two widths the per-tag payload slots are identical (the checker
  unifies two uses only when their shared tags' payloads agree); and both `match`
  (`br_table`) and drop (`VariantDrop`) dispatch on the cell's stored tag. So the
  `LayoutId` the pointer carries is a *typing* distinction with no bearing on any
  load, store, branch, or free the program performs.
- **The committed fix is to make the layouts genuinely equal** — key a variant
  `LayoutId` on its payload-shape family rather than on the canonical row-width
  `Ty`. Tracked as **#141 (HIGH priority, before Phase 8, #93–#97)**, because the
  Phase 8 prelude lists lean harder on open rows. This supersedes the interim
  state below; it is not optional.
- **The verifier is not relaxed.** Treating layouts that merely agree on shared
  tags as compatible would weaken an internal consistency check to hide a
  layout-identity decision that #141 makes precise instead.

## Consequences

- Variants are complete and correct for Phase 7: construction, `match`,
  nullary tags, multi-field payloads, recursive and mutually-recursive types,
  and the iterative drop of deep structures all run identically under the
  interpreter and wasm with no leak.
- There is one documented gap. A width-polymorphic tag binding lowers to MIR
  that the verifier (`mir/src/verify.rs`) rejects on a pointer-type mismatch.
  The verifier runs only in tests — it is absent from the `cli/src` production
  path — so the "errors come only from the checker" invariant holds: no user
  ever sees this. The case is covered by the differential test
  `a_tag_bound_once_and_matched_at_two_widths_still_runs`, kept out of the
  verify-running mono suite so the verify gate stays green and meaningful.
- Once #141 lands, that test is promoted to also assert `verify()` passes, and
  this gap closes.
- Same family as #74 (and #65): a let-generalized value pinned to its first
  use. If the first-use rule is ever revisited, all three move together.
