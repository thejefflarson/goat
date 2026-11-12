# ADR 0033 — A spread updates a field it has, extends with a field it lacks, and never changes a field's type

- Status: accepted (2026-11-11). The spike (see "Spike evidence") showed the
  typing carries the rule. It also showed that one knot per receiver is not
  enough for several methods; ADR 0034 addresses that by typing each method
  against its own record.
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
  returns `self`'s type. The spike showed that this does not make #403's nested
  knots unnecessary: each method still has its own open self row.
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

## Spike evidence (2026-11-11)

Branch `spike/404-spread-update`, cut from master `321103f`. A second branch,
`spike/404-on-403`, is the same change on top of #403's nested knots. Neither
is meant to merge.

**Verdict.** The typing rule carries. Presence rows give a principal,
annotation-free update-or-extend, a field-type change is a spanned error, and
#147 type-checks. The expectation that one knot per receiver then suffices does
**not** hold: the three-method model still does not finish checking, on master's
knot and on #403's. **Recommendation: accept the rule (items 1 to 5 of the
Decision), and drop the claim that #403 becomes unnecessary.** Rescope #403
rather than close it, and track the three-method blow-up as its own problem.

### What the spike built

- `Row::Maybe { label, pres, field, rest }` in `checker/src/ty.rs`: a field that
  is there or not, by a presence variable. The variable is an ordinary type
  variable id, bound in the same substitution to one of two constants,
  `PRESENT` or `ABSENT`. Generalization, instantiation and mono's `match_ty`
  therefore carry it with no second substitution. `resolve_row` turns a
  bound `Maybe` into an `Extend` (present) or drops it (absent).
- Spread typing, `infer_spread` and `override_field`: walk the base's row to
  the label. A present field is updated, and the new value must have its type. A
  presence-variable field is made present, by the same rule. A closed row
  without the label is extended. An open row (it ends in a row variable) that
  may have the label becomes `{l?: T | ρ'}` in the base and `{l: T | ρ'}` in
  the result. So `set_x = program(r) do {...r, x: 1} done` gets the one
  principal type `({x?: Number | ρ}) -> {x: Number | ρ}` and serves a record
  with an `x` and one without.
- Unifier: `surface` replaces `rewrite_row` and returns presence along with the
  field. A `Maybe` unified against a row that lacks the label has its flag bound
  to absent, and against a present field to present. The `lacks` table is
  Rémy's "this row variable never holds `l`" constraint. It now also records
  every label in front of a row variable, so no row gains a second `x`.
- Mono: `flatten_row` and `match_row` bind and read the presence constant. A
  spread already copied fields by label, so lowering is unchanged, and
  `layout_fields`' "first of each label" filter is now a no-op that could go.
- The error, spanned at the new value and free of type variables:
  `` `x` is `Number` in this record, and `...` keeps a field's type, so it can't become `String` ``.
  When either type still holds a variable it falls back to the plain mismatch.

### Findings

| # | Question | Result |
|---|----------|--------|
| 1 | Checker change, principal and annotation-free | Done. About 360 changed lines in `infer.rs`, 46 in `ty.rs`, 26 in `mono.rs`, 12 elsewhere. No annotation syntax. `set_x`, `go` (#147) and update methods each get one most-general type. One loss against full Rémy: an absent field's phantom type is still unified, so two absent `x?` fields at different types in one row force them equal. Dropping the type when the flag goes absent would fix it. |
| 2a | `{...ball, x: "hi"}` with a numeric `x` | Rejected with the message above. |
| 2b | #147 `go = program(s) do go({...s, stop: true}) done` | Checks (`pure_extension_spread_recursion_checks`). ADR 0028's remark that presence typing alone would not remove the regress holds only for stacking extension; with update-or-extend the equation `ρ = {stop: Bool \| ρ}` never arises, because the result shares `ρ` with the base. |
| 2c | Three-method model checks and runs on master's single knot | **No.** `m.nudge().update().draw()` over a record with `x, y, update, nudge, draw` does not finish. It is CPU-bound: 160 MB resident after 10 s in a debug build, still running at 30 s. Without `draw` it checks in milliseconds. The two-method model (`update`, `draw`) is rejected with master's "the type of `draw` would have to contain itself". Both are pinned as `#[ignore]`d tests in `checker/tests/spread_update.rs` and `cli/tests/spread_update.rs`. |
| 2d | The same on top of #403 (`spike/404-on-403`) | The two-method model checks. The three-method model still does not finish. |
| 2e | One-method update model, update-or-extend over an unknown record, recursive spread, run through interpreter and wasm | Pass: `cli/tests/spread_update.rs` (3 tests) and the `differential` and `wamr` suites. |
| 3 | Existing spread, destructuring and rest-pattern tests | 1552 pass, 0 fail, 2 ignored (the three-method pair; the two-method test, added after that run, makes 3). 12 tests changed on purpose; list below. |
| 4 | Cost | No measurable change (below). |
| 5 | Coq rework | Estimated below: 2 to 3 days to forbid duplicates in the current model, 3 to 5 weeks to model presence and spread. |

#### Why one knot is not enough

`update` is inferred as `({x: Number | ρa}) -> {x: Number | ρa}`, `nudge` as
`({y: Number | ρb}) -> {y: Number | ρb}`, and `draw` as `({x, y | ρc}) -> Number`.
Each method's self type is its own **open** row, with its own row variable and
its own label prefix. Calling a method on `m` binds that method's row variable to
the rest of `m`'s row, and the rest holds the other methods, whose types mention
*their* row variables. The knot for `ρa` then has a body with mentions of `ρb`
and `ρc` at other prefixes (`{x | ρa}`, `{y | ρb}`, `{x, y | ρc}`), and each
needs its own binder. ADR 0033 removes the duplicate-label prefixes: `{x, x | ρ}`
becomes `{x | ρ}`, so three update methods contribute three prefixes where they
contributed six. The prefixes still differ by method, and one knot needs every
mention of a variable to share one prefix, which a record of methods over
different fields never gives.

Separately, in the failing two-method case on master's knot, two mentions of one
row variable differ only in how an earlier knot is written (`update: μ497. …`
beside `update: 497` inside it). `find_mention` compares rows structurally, so
equal types count as different mentions. #403's unfolding comparison fixes this,
which is why `spike/404-on-403` checks that case.

What would fix the three-method case is not in this ADR: methods typed against
the record they live in (a receiver type fixed when the record literal is
built) instead of an open row per method, or a knot over several row variables
at once. Both belong to ADR 0032's follow-up.

#### Measurements

Debug builds (release not built), this machine, master `321103f` against the
spike:

| Measure | master | spike |
|---------|--------|-------|
| `goat check` on 25 `examples/*.goat`, mean of 20 runs each | 24.6 to 52.7 ms (process start dominates; median 26.0) | 25.4 to 52.0 ms (median 26.4) |
| `checker/tests/scale.rs` (5 tests, 2 000 and 8 000 statement programs) | 0.78, 0.78, 0.79, 0.78 s | 0.78, 0.79, 0.79, 0.90 s |

One example (`arrow_draw`) read 43.8 ms against 102.9 ms in the first sweep and
30 ms against 30 ms on three re-runs: a cold-cache outlier. Memory:
the recursion-heavy three-method program was run only under `timeout`
(10 s, then 30 s), because macOS refuses `ulimit -v`; its resident size stayed
under 200 MB. The full workspace suite ran twice, about 20 minutes each, in debug.

#### Existing tests that changed (all deliberate)

| Test | Change | Why |
|------|--------|-----|
| `checker/src/lib.rs` `spread_adds_a_field` | expects `{x: Number, y: Bool}` | An added field now sits behind the base's fields instead of in front. Display order only; mono sorts fields by label, so layouts are the same. |
| `lib.rs` `spread_override_replaces_the_field_even_at_a_new_type`, now `..._updates_the_field_and_keeps_its_type` | a type-changing override is an error | Decision rule 3. |
| `lib.rs` `spread_of_an_unknown_record_stays_polymorphic_in_the_rest` | `bump({x: "s", z: 2})` became `bump({x: 4, z: 2})` | The string `x` changed the field's type. |
| `lib.rs` `rest_refuses_a_label_a_spread_override_hid`, now `rest_after_a_spread_update_names_each_label_once` | the "`x` is in this record twice" error no longer arises | No record holds two fields with one label (rule 5). The type-changing inputs are now ordinary mismatches. The `lack` check that raised it is unreachable from spread; delete it with the shadowing code if accepted. |
| `checker/tests/constraints.rs` `spread_recursion_that_only_adds_a_field_gets_a_targeted_error`, now `..._checks` | the program type-checks | ADR 0028 superseded. `pure_extension` and `spread_regress_message` are now dead. |
| `constraints.rs` `other_infinite_record_types_keep_the_generic_message`, now `..._stay_rejected` | still rejected; the message now reads "cannot construct the infinite type …", not the record-specific wording | `f = program(s) do f({a: {...s, b: 1}}) done` fails on the type-variable path first. The message names type variables, a kid-wording gap that predates the spike. |
| `checker/tests/structural_recursion.rs` `pure_extension_spread_recursion_stays_rejected`, now `..._checks` | the program type-checks | ADR 0028 superseded. |
| `cli/tests/differential.rs` `spread_adds_overrides_and_retypes_fields`, now `spread_adds_and_overrides_fields` | two retyping assertions removed | Rule 3. |
| `differential.rs` `spread_shadowing_a_field_hidden_behind_a_row_variable_frees_it`, now `spread_over_an_unknown_record_updates_or_extends` | rewritten for update-or-extend | The shadowed layouts it covered no longer exist. |
| `mir/tests/mono.rs` `spread_update_and_override_values` | retyping assertion removed | Rule 3. |
| `mono.rs` `a_known_override_leaves_one_slot_for_the_label` | override at the same type; layouts have at most two slots | Rule 3. |
| `mono.rs` `a_shadowed_field_behind_a_row_variable_is_dropped_from_the_layout`, now `a_spread_over_a_row_variable_that_has_the_field_adds_no_slot` | spread over an unknown record that has and lacks the field | Shadowing is gone; the test checks both cases add no slot. |

#### Coq records-model rework (estimated, not done)

Read `proofs/goat_ln.ott`, `GoatRows.v` and the files that mention rows
(`GoatDefs`, `GoatMeta`, `GoatSubst`, `GoatSound`, `GoatRank2`, `GoatProofs`).
The proof core has records as literals and projection only; it has **no spread**.
So ADR 0033 does not invalidate anything that is proved today, and the two
sizes below are different jobs.

- **Small: forbid duplicate labels in the existing model (about 2 to 3 days).**
  Rows keep `nil | r | l : T ; R`; add a well-formedness predicate (no label
  twice, a row variable's `lacks` set). `pi l R` becomes an `option` instead of a
  `list`. Lemmas that change: `pi`/`rtail` (definitions), `req_pres`,
  `req_pi`, `pi_head`, `req_surface` (all in `GoatRows.v`, about 60 of its 216
  lines), plus the `T-Proj` case in `GoatSound.v` that calls `req_surface`. The
  `swap` rule of `req` already needs `l <> l'`, so it is unchanged. The
  `Forall2_teq_*` lemmas disappear. This buys the "one label, one slot" fact
  that `layout_fields` assumes today, and nothing about spread.
- **Large: presence rows and a spread that updates or extends (about 3 to 5
  weeks).** Needed only if the proof is to cover spread, which the plan does not
  currently ask for.
  1. Grammar: a presence sort (`pre`, `abs`, presence variable) and either
     `l : T^p ; R` or a `Maybe` row form. Ott regenerates the locally-nameless
     `open`/`close`/`subst`/`fv`/`lc` for the new sort, a new atom kind, and a new
     expression form for spread with its field list (the same cons-list trick
     the record spine uses).
  2. `teq`/`req`: three new rules (a `pre` head, an `abs` field that drops out,
     presence-variable congruence). `teq_req_refl`, `teq_shape`, `teq_Record_inv`
     and every inversion lemma gain cases.
  3. `GoatRows.v`: `pi` over presence, `req_pres` restated (a present field is
     preserved, an absent one disappears), `req_surface` restated, plus a new
     lemma that unifying a presence flag is sound.
  4. `GoatSubst.v` (661 lines, 10 row mentions): substitution and its
     commutation lemmas get a presence case, and substituting a presence
     variable is new.
  5. `GoatSound.v`: new `T-Spread` rule with update and extend premises, the
     preservation and progress cases, and the canonical-forms lemma for records.
  6. `GoatRank2.v`: row mentions rechecked (11).
  The parse-and-print roundtrip files are untouched until spread is a surface
  form in the proof core.

Whichever size is chosen, the **checker's** `lacks` set is already the
Rémy "this row variable never holds l" constraint, so the Rust and Coq models
meet at the same predicate.

### Recommendation

**Accept** the rule in the Decision. It costs about 450 lines of non-test code, makes a type
change a kid-readable error, removes ADR 0028's limitation and ADR 0011's
shadowed-slot case, and shows no compile-cost change. **Do not** accept the
consequence that "#403's nested knots are expected to become unnecessary": the
spike shows they stay necessary, and that nesting alone does not rescue the
three-method model either. Rescope #403 to the nested-knot machinery (it makes
the two-method model check) and open a new issue for the three-method blow-up.
The Coq work is not on the critical path: the proof core has no spread, so the
small job (forbid duplicate labels) can follow the Rust change and the large
job waits for spread to enter the proof core.
