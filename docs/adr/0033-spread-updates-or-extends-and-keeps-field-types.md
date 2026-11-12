# ADR 0033 — A spread updates a field it has, extends with a field it lacks, and never changes a field's type

- Status: proposed (2026-11-11). The owner decided the rule. A spike decides
  whether the typing below carries it, and then this ADR moves to accepted.
- Context: ADR 0011 (a shadowed field gets one layout slot; `lacks` constraints
  keep rest patterns sound), ADR 0028 (pure-extension spread recursion is
  rejected), ADR 0032 (methods on any receiver), PR #403 (two methods whose rows
  differ).

## Context

Today `{...r, x: e}` is typed as Leijen scoped-label extension: the new `x`
sits on top of `r`'s `x`, so the type is `{x: T_new, x: T_old | ρ}`. At run
time there is one `x` (ADR 0011), but the type remembers the shadowed one, and
the new `x` may have a different type.

Two consequences:

- A method that returns an updated copy of itself (`{...self, x: self.x + 1}`)
  returns a different type from the one it received. Every such method adds a
  shape that the recursive self type of ADR 0032 must cover. With three methods
  whose shapes differ, the nested knot of #403 grows past every budget.
- A kid can write `{...ball, x: "hi"}` when `x` is a number and get a record
  whose `x` changed type, which is never what they meant.

## Decision

1. **A spread over a field the record has is an update.** The new value must
   have the field's existing type, and the result has exactly the base's type.
2. **A spread with a field the record lacks is an extension.** The result is
   the base's type plus that field.
3. **A spread never changes a field's type.** `{...ball, x: "hi"}` when `x` is a
   Number is a type error that names the field and both types.
4. **Inference stays annotation-free with principal types.** When the base's
   type is not yet known (`set_x = program(r) do {...r, x: 1} done`), a field
   carries a presence variable, in the style of Rémy: in `r`, `x` is either
   absent or present at `Number`, and in the result it is present at `Number`.
   That is the single most general type, and it serves both an `r` with an `x`
   and one without.
5. **No record type ever holds two fields with one label.** Shadowing
   disappears from the type system and from layouts.

## Consequences

- ADR 0028 is superseded. `go = program(s) do go({...s, stop: true}) done` is
  an update or extension of `stop` at `Bool` and type-checks.
- ADR 0011 is simplified. With no shadowed fields, its one-slot rule is the only
  case, and the `lacks` constraint guarding rest patterns over a shadowed label
  has nothing left to guard. Rest patterns keep their meaning.
- ADR 0032's knot gets one shape per receiver: a method that updates `self`
  returns `self`'s type. #403's nested knots are expected to become unnecessary.
  The spike checks this on a three-method model.
- The Coq record model (`goat_ln.ott`, the row lemmas) changes from scoped
  labels to presence-annotated rows. This is the largest cost.
- Mono layouts get simpler: a record's labels are distinct.

## What the spike must show

- The typing rules and the unifier change for presence variables, and that the
  checker stays principal and annotation-free.
- A three-method model (`nudge` and `update` returning updated copies, `draw`
  reading `x`) type-checks and runs, through the interpreter and wasm, without
  #403's nested knots.
- `{...ball, x: "hi"}` is rejected with a message that names the field.
- Every existing spread, destructuring and rest-pattern test still passes, or is
  changed deliberately and listed.
- The cost of the change to the Coq records model, estimated (not done).
