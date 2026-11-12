# ADR 0011 — A shadowed record field gets one layout slot; a `lacks` constraint keeps rest-patterns sound

- Status: accepted (2026-11-03). Note (ADR 0033, 2026-11-11): the shadowed-slot
  case is gone. A spread updates or extends and no record type holds two fields
  with one label, so `layout_fields` and its first-of-label filter were deleted
  and a layout has one slot per label by construction. The `lacks` table stays:
  a rest pattern still must not let its rest regain the label it took out.
- Context: Phase 7 (record spread + destructuring + rest), ADR 0002, `docs/mir.md`
  ("Layouts"), `docs/plan.md` ("Record spread and destructuring"); ratified while
  integrating #145 (closes #91).

## Context

Spread `{...base, l: v}` types as Leijen scoped-label extension: the result row
is `{l: τ' | row(base)}`. When `base` already carries an `l` — known, or hidden
behind its row variable — the new field *shadows* the old one. Scoped labels
keep both `l`s in the type and only the outer is reachable by `.l`, so two
things must agree about the shadowed field or the compiler is unsound:

1. **Runtime layout** — how many slots does a record with a shadowed `l` get?
2. **Rest pattern** — `{l, ...rest} = m` takes the front `l` out; may `rest`
   re-expose the one behind it?

Keeping shadowed fields in the layout is the easy answer to (1), but it wastes a
slot per override and, worse, leaks the shadowed heap object (nothing ever reads
or frees it). Dropping them is the right answer — and it is exactly what forces
the question in (2).

## Decision

### One layout slot per label (mono)

A record layout and `field_index` use `canon::layout_fields` — the **first
occurrence** of each label — so a shadowed field gets no slot. `{...base, x: v}`
over a `base` that has an `x` produces one `x` in memory; the shadowed value is
never copied into the new record, so it is freed when `base` is.

`ground` (the type the mono matcher sees) deliberately **keeps** duplicate
labels. Deduping there would erase the structure `match_ty`/`match_row` use to
recover which row variable a specialization came from, regressing variant and
row-polymorphic record programs. Dedup is a layout concern, so it lives only in
`layout_fields`, not in `ground`.

### A `lacks` constraint makes restriction sound (checker)

Because mono drops the shadowed field, `{l, ...rest}` must not let `rest` regain
it — otherwise `rest.l` would read a slot that does not exist.
`Inferer.lacks: HashMap<TypeVar, BTreeSet<String>>` pins a row variable to never
(re)gain the restricted labels. It is carried through `instantiate`, propagated
when a row variable is bound or grown, and a violation is a spanned checker
error (`` `l` is in this record twice … ``). No `Scheme` change: the table is
keyed by the quantified row variables and copied on instantiation.

A `lacks` (absence) constraint is part of Leijen's scoped-label system, so this
is a principled, minimal addition rather than a bespoke guard. It rejects
exactly the unsound case — a rest pattern over a spread-shadowed label — and
leaves ordinary open-row rest patterns untouched; both directions are tested
(`rest_refuses_a_label_a_spread_override_hid` and the plain `rest_*` tests).

The alternative — keep shadowed fields in the layout so restriction is a plain
row operation — was rejected: it contradicts the single-slot decision above and
leaks heap.

## Consequences

- Soundness holds end to end: rest-after-shadow is a checker diagnostic with a
  span (users never see a mono/MIR error), and the runtime never reads a dropped
  slot. The differential test `spread_shadowing_a_field_hidden_behind_a_row_variable_frees_it`
  asserts `live == 0`, and every differential program is checked by the MIR
  verifier.
- `lacks` grows a side table keyed by row variable that is never pruned; its
  size is bounded by the program's type-variable count.
- `lacks` does not change the infinite-record-type rejection (`docs/plan.md`,
  "Known limitation"): recursion that only spreads and extends its parameter is
  rejected by design ([ADR 0028](0028-pure-extension-spread-recursion-rejected.md)).
