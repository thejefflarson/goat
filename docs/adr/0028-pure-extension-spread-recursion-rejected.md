# ADR 0028 — Recursion that only spreads and extends its parameter is rejected by design

- Status: accepted (2026-11-09)
- Context: `docs/plan.md` ("Known limitation"), ADR 0010 (mono layout identity),
  ADR 0011 (`lacks` constraints for record restriction). An unannotated function
  that recurses by spreading a parameter it never reads and adding a field is an
  infinite record type:

  ```
  go = program(s) do go({...s, stop: true}) done   # rejected
  ```

  Recursion is monomorphic inside its own group, so the call unifies the
  parameter row `ρ` with `{stop: Bool | ρ}`. Under Leijen scoped labels that
  equation has no finite solution, and records are deliberately non-recursive
  (only variant payloads tie a recursive knot).
- Decision: the checker keeps rejecting this program. The rejection is sound and
  intended, not a gap to close. The occurs-check failure for a record row that is
  only the row variable itself behind added labels reports a targeted spanned
  error: the recursive call spreads the parameter and adds the named fields, so
  the record grows without bound; read or constrain a field of the parameter, or
  drop the never-read spread. Every other record occurs-check failure keeps the
  generic "cannot construct an infinite record type" message.
- Consequences:
  - Accepting the program would mean replacing Leijen scoped labels with Rémy
    presence flags and update semantics. That reopens ADR 0010 (a shadowed field
    no longer has one layout slot by construction) and ADR 0011, and needs a
    near-total Coq re-model: recursion added to the proof core and the row
    metatheory rewritten. The programs it would rescue are degenerate (a spread
    whose base is never read), so the cost is not justified.
  - Presence/absence typing carried in schemes would not remove this limitation
    by itself; the regress comes from monomorphic recursion plus label
    extension, not from missing `lacks` information.
  - Reading a field of the parameter (`s.n`) pins its row and the program
    checks, as does a spread that overrides a field it read.
