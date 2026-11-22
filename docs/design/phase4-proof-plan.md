# Phase 4 proof plan: spread update-or-extend with presence variables (design pass)

Status: decided. Issue #453, part of #435, governed by ADR 0037 (phase 4) and
ADR 0033. Written against `master` at 4dad6c1, after phase 3 (#527, #528). The
owner delegated the proof-model choices to this pass; each is recorded in
section 3 with the alternatives it beat. The calculus and proofs follow in the
stacked PR.

## 1. What the checker does today

Read from `checker/src/infer.rs` (`infer_spread`, `override_field`,
`infer_restrict`, `keep_field_type`), `checker/src/ty.rs` and ADR 0033, which
#412 implemented.

- **A spread updates or extends.** `{...p, x: v}` copies `p` and sets `x`. When
  `p` has `x`, the new value must have `x`'s type and the result has `p`'s type.
  When `p` lacks `x`, the result is `p`'s type plus `x`. A type-changing update
  (`{...ball, x: "hi"}` with a numeric `x`) is an error that names the field.
- **A field of unknown presence is a `Row::Maybe`.** When `p`'s row is not yet
  known (`set_x = program(r) do {...r, x: 1} done`) the spread unifies `p`'s row
  with `{x?p: Number | rho}`, a field that is there or not by the presence
  variable `p`, and returns `{x: Number | rho}`. So `set_x` has one principal
  type, `({x?: Number | rho}) -> {x: Number | rho}`, and serves `{x: 4, z: 2}`
  and `{y: true}`. A presence variable is an ordinary type variable bound to
  `PRESENT = Unit` or `ABSENT = Bool` (`ty.rs`), so generalization and
  instantiation carry it with no second substitution.
- **`lacks`.** Rémy's "this row variable never holds `l`": a table from row
  variables to the labels they cannot hold. The spread records, for the tail
  `rest` of a `Maybe`, that it lacks the label, so no row gains a second `x`.
  Unifying a `Maybe` against a row that lacks the label binds the flag to
  absent, against a present field to present.
- **Rows never hold a label twice** (ADR 0033 decision 5). The checker's rows
  are scoped-label rows by construction, but the `lacks` table keeps every
  inferred one free of duplicates.
- **Several fields** in one spread are overridden one after the other
  (`override_field` in a loop), the base and the field values inferred first, in
  order.
- **Restrict.** `{x, ...rest} = p` binds `rest` to `Restrict(p, [x])`:
  `p` unified with `{x: fresh | tail}`, the result `{tail}`, and `tail` made to
  lack `x`. Destructuring a label the record does not have is an error.
- **Methods.** A `Row::Maybe` and a `Row::Extend` both carry a `method` flag
  (ADR 0034). Methods are phase 6 of the corrected order (the elaboration
  theorem, methods, dot calls); this phase leaves the flag out.

## 2. The calculus gains

Everything below is in `goat_ln.ott`, regenerated into `Goat_ott.v`, and
`GoatDefs.v`.

**Syntax.**

- A row entry `l ^ P : T ; R` (`row_Maybe l P T R`): the field `l` at type `T`,
  present or absent as `P` says, then the rest `R`. `P` is a `typ`: `Unit`
  means present, `Bool` absent, a type variable is a presence variable. This is
  the checker's encoding (`PRESENT`, `ABSENT`), so a presence variable is the
  `typ_Var` the generalization, instantiation and substitution machinery
  already handle, and no `typ`, no environment and no sort changes.
- Terms `spread(e1, l, e2)` (`{...e1, l: e2}`) and `restrict(e, l)`
  (`e` with its first `l` taken out). A spread with several fields is the nest
  `spread(spread(e, l1, e1), l2, e2)`; evaluation order and every type are the
  same, because the checker overrides field by field. A rest pattern with `k`
  labels is `k` nested restricts. No new value form.

**Row equivalence** (`req`, which `teq` reaches through `T_Rec`) gains five
rules:

| Rule | Reads |
| --- | --- |
| `maybe` | `l^P:T;R ~= l^P':T';R'` from `P ~= P'`, `T ~= T'`, `R ~= R'` |
| `pre` | `l^Unit:T;R ~= l:T;R` |
| `abs` | `l^Bool:T;R ~= R`, when `l # R` |
| `swap_em` | `l^P:T;l':T';R ~= l':T';l^P:T;R`, when `l <> l'` |
| `swap_mm` | the same for two `Maybe` entries |

`l # R` (`rlacks l R = true`) says `R`'s spine, to its `nil`, names no `l`. A
row ending in a row variable lacks nothing. A `Maybe` entry of another label
does not count. The absent entry's field type `T` is phantom: `abs` ignores it,
as Rémy's does.

**Typing.**

```
G |- e1 : {l ^ P : T ; R}      G |- e2 : T
------------------------------------------ T_Spread
G |- spread(e1, l, e2) : {l : T ; R}

G |- e : {l : T ; R}
------------------------------ T_Restrict (as stated in section 3, Q7)
G |- restrict(e, l) : {R}
```

One spread rule covers both cases through `T_Conv`. A base of type
`{l: T; R}` converts by `pre` to presence `Unit` (an update, the result is the
base's type). A base `{R}` with `l # R` converts by `abs` to presence `Bool` (an
extension). A base typed with a presence variable stays as it is. That variable
is what a lambda parameter's type carries, and instantiating it with `Unit` or
`Bool` at a call is what makes `set_x` serve both records.

**Reduction.**

```
spread({fs}, l, v) --> {set l v fs}     where set replaces the first l-field
                                        or, when there is none, prepends l: v
restrict({fs}, l)  --> {drop l fs}      where drop removes the first l-field
```

plus the congruences (base, then the field value, as for application) and
`traps` rules that carry a trap out of either operand. `set` is a total
function: it looks at the record, not the type, so the step rule has no type
premise. Types make the two cases agree, which is the preservation proof.

## 3. Decisions

Each is a proof-model choice the owner delegated. The ones that change the
shape of what later phases build on are marked **(load-bearing)**.

### Q1. How presence is represented **(load-bearing)**

- **A. A `typ` in the presence slot, `Unit` present and `Bool` absent
  (chosen).** No new sort, no environment, no substitution; `ftv`, `gen`,
  `inst`, `ap_typ` already do the right thing for a variable in a type position.
  A presence variable instantiated at `Int` is ill-sorted and harmless: no rule
  reads the slot except `pre` and `abs`, so such a row never equals the row of a
  record literal and no value inhabits it.
- **B. A new nonterminal `pre ::= present | absent | a`.** Honest, but a second
  variable namespace: a new atom kind, `ftv`/`gen`/`inst`/`ap` for it, and
  every lemma that quantifies over type variables doubles.
- **C. A presence sort `k_Pres` in the kinding environment `D` (ADR 0038).**
  It would stop the `Int` instantiation, at the price of a sort lattice that
  is no longer a chain (`finer`, `sat`, `bin_sig_ap` all change) for a
  property no theorem needs. Revisit with the algorithm proof, which wants to
  say a presence variable is never unified with `Int`.

### Q2. How `lacks` enters the calculus **(load-bearing)**

`abs` is unsound without a lacks premise. Take `rho := {x: Bool}`: the base
`{x: true}` has type `{x^Bool: Number; rho}` if `abs` ignores `rho`, the spread
updates `x` in place, and the result `{x: 1}` is not of the claimed type
`{x: Number; x: Bool}`. The checker rules this out with its `lacks` table
(Rémy's row-variable kind); the calculus must too.

- **A. A syntactic premise `l # R`, true only of a closed spine (chosen).** It
  is stable under every substitution (a substitution changes types and row
  variables, and a lacking row has no row variable), so `teq_ap` and the type
  substitution lemma need no new idea. Cost: a row variable never lacks anything,
  so a spread whose base row ends in a row variable that the checker knows lacks
  the label (the remainder of a rest pattern: `{x, ...rest} = p` then
  `{...rest, x: 2}`) has no derivation. The program is accepted by the checker
  and is outside the calculus; the corpus skips it (section 6). The calculus
  accepts strictly less there, so soundness is unaffected.
- **B. Row variables carry a lacks sort in `D`** (the label set they cannot
  hold), `kres` and `inst` demand substitution images respect it, and `l # R`
  consults `D` for a variable tail. Faithful to the checker and complete for
  rest patterns. It extends `sat`, `kres`, `inst`, `casch_inst`, the
  type-substitution lemma and the algorithm's substitution invariant from type
  variables to row variables: I estimate it at the size of ADR 0038's whole
  phase (about a quarter of `GoatSound.v` rewritten). Not needed for any
  soundness statement, so it waits for the algorithm proof, where it is needed
  for completeness. A has `l # R` as a predicate of `R` alone; B generalizes it
  to a predicate of `D` and `R`, so A's rules and lemmas carry over with the
  variable case added.
- **C. Reduce at instantiation** (a smart `ap_row`, rewriting `l^Unit:T;R` to
  `l:T;R` and `l^Bool:T;R` to `R` when the image lacks `l`), with no `pre` or
  `abs` in `req`. It makes the inversion below trivial and costs a case
  analysis in every substitution-algebra lemma (`ap_comp`, `teq_ap`, the
  free-variable lemmas), which `req` rules do not. Rejected: the cost lands in
  the lemmas that already carry the proof's difficulty.

#### Q2-B, worked out

An attempt at B found which parts of it are load-bearing. Record them before
the next try.

- **Environment.** `denv` becomes a record `{dsort; dlk}` with a coercion to
  `dsort`, so `D a` still reads a sort; `dlk D r l = true` says the row variable
  `r` lacks `l`. `rlacksD D l R` is `rlacks` with a variable tail read from
  `dlk`. A row substitution is `rkres D D' sr`: every label `r` lacks, `sr r`
  lacks in `D'`. `rlacksD_ap` (stable under `ap_row`) is a one-line induction.
- **A new rule, not a change to `req`.** Indexing `req` (hence `teq`) by `D`
  touches every file. Instead add `T_SpreadL`: `G |- e1 : {R}`, `rlacksD D l R`,
  `G |- e2 : T` give `G |- {...e1, l: e2} : {l: T; R}`. For a value `e1` the row
  `R` equals a literal's row, so it has no variable (`req` preserves the tail),
  `rlacksD` is `rlacks`, and `req_abs` turns the derivation into a `T_Spread`
  one; preservation reuses `spread_step_typing`. Progress and the inversions
  gain one case each, mechanical.
- **What a `let` must do (the part that decides the cost).** A scheme must
  record the lacks of the row variables it quantifies, and `T_Let`/`T_Letrec`
  must choose them the way they choose `k`: `typing (extr (ext D V k) Vr rk) G e1
  T1` and `x : gen G T1 k rk`, with `inst` demanding `rlacksD D l (sr r)` for
  every `l` in `rk r`. The shortcut "generalized rows carry no lacks" (a
  `lacks_free` premise on `T_Let`) type checks the rule but **breaks
  preservation**: term substitution removes a binder from the context, which
  makes a row variable generalizable that was free before, and the `let` body's
  derivation then needs a premise the original one did not have
  (`typing_ftv_mono`, `ctx_more_gen`). So `rk` has to ride along wherever `k`
  does: `gen`, `casch` (`rk` through the renaming `gr`), `casch_inst`,
  `casch_gen_sch_equiv`, `sch_more_gen` (an `rkup` beside `kup`),
  `typing_denv_agree` (rows outside the agreed set map to `Empty`, which lacks
  everything), `typing_inst_gen`, and `Sch` in all its constructors.
- **Algorithm W.** Needs a lacks map next to `D` in the unifier: binding `r :=
  R` checks `rlacksD`, `l^P:T;R1 ~ r` with `r` lacking `l` binds `P := Bool` and
  `R1 := r`, and `restrict` gives its fresh tail the label. Every `kres D D'
  (sT s)` in `GoatInfer*.v` gains the row half, and `gen_ren` carries `rk`.
- **Corpus.** Delete `lacks_on_tail` and the error-text test once the count
  is 0.

### Q3. Scoped labels stay

ADR 0033 rule 5 says no record type holds two fields with one label. The
calculus keeps Leijen's scoped rows (a row may hold `x` twice, the first one
wins) and adds presence on top: a calculus that accepts a superset of types is
still sound, `{x: 1, x: 2}` is already well formed in it, and forbidding
duplicates would be the "small job" of the ADR's estimate (a well-formedness
predicate on every row in every statement) for no soundness gain. The runtime
agrees with scoping: a spread or restrict touches the **first** `l`. The
differential corpus only writes records with distinct labels, so the checker and
the calculus compare on the language the checker accepts.

### Q4. One rule for update and extend

`T_Spread` with a presence slot, versus the checker-shaped pair `T_SpreadUpd`
(base `{l: T; R}`) and `T_SpreadExt` (base `{R}`, `l # R`) plus a third rule for
a variable presence. One rule needs `pre` and `abs` in `req`, so the
Q2-A/B-versus-C question is the whole choice; chosen with Q2-A.

### Q5. Runtime semantics

`set` replaces the **first** `l`-field when there is one and prepends otherwise.
The alternative, always prepend (the shadowing of ADR 0011), makes an update
return a record with two `x` and breaks `T_Spread`'s result type. A single-field
spread term keeps the step rule free of an order question; a multi-field spread
is a nest, as in section 2.

### Q6. Phase-3 groups, `mu`, and the rest of the judgment

- **Groups.** A tag payload is a record, a spread over a payload works like any
  other, and a group value is not a record, so `{...tag, x: 1}` has no derivation
  (`T_Conv` cannot make a `grp` a `Record`, `teq_Record_inv`). `slots_row`,
  `tag_payload` and `arms_wf` do not mention `Maybe`: a declared payload has no
  presence variables. No phase-3 lemma changes beyond the new `row` case.
- **`mu`.** `lct` and `gd` read a `Maybe` entry as they read an `Ext` one (the
  presence slot too). A guarded recursive record may hold optional fields. No
  new rule.
- **The judgment `typing D G e T`** is unchanged: no environment, no sort.
- **Generalization.** `ftv_row` of a `Maybe` entry includes the presence slot, so
  `gen` quantifies a presence variable together with the type variables.
  `T_Let` is untouched; a spread is not a syntactic value (`is_gen_value`
  rejects it), as in the checker (`is_syntactic_value`).

### Q7. Restrict, and what its typing rule says **(load-bearing)**

`T_Restrict` as written in section 2 needs the preservation step "the record
without its first `l` has type `{R}`", which needs `req` to cancel an entry
(`l: T; A ~= B` implies `B` minus its first `l` is `~= A`). `GoatRows.v` proves
only the soundness direction of the per-label characterization (`req_pres`);
cancellation is the hard completeness direction its header explains. Instead,
the rule keeps the premise the proof needs, as a relation on the row:

```
G |- e : {R0}       rm l R0 T R
----------------------------------- T_Restrict
G |- restrict(e, l) : {R}
```

`rm l R0 T R` says the first `l` of `R0`'s spine (skipping other entries,
and a `Maybe l' ...` of another label) is at type `T` with rest `R`; a
`l^Unit` entry is a present `l`, any other presence slot has no `rm`. It is
defined by structural recursion, so a substitution maps it to itself, and one
lemma, `rm` commutes with `req` (existence and the type and rest up to `~=`,
by induction on the derivation, both directions for `sym`), gives
preservation. It is the checker's `infer_restrict` with `lacks` left out
(Q2-A).

### Q8. What goes outside, and what the parser fragment does

- **Outside, with the reason.** The `method` flag on a row entry (phase 6); a
  `lacks` table on row variables (Q2-B); the multi-label `Restrict` as one node
  (it is the nest of single restricts); the checker's `Copied` error text
  (wording, not a type).
- **Parser and printer.** Phase 3 left the parser and printer proofs alone, and
  `rule_map.rs` exempts the new term forms. This phase does the same for
  `spread` and `restrict`: T1 to T3 gain only the cases that carry the new
  constructors through `close_exp`, `bind_group` and `inst`. The surface
  `{...p, x: v}` and `{x, ...r} = p` have no denotation yet (the phase-3
  precedent, plan Q9); a ticket after the algorithm covers them with tag
  declarations and `match`.
- **Algorithm W.** Out of this ticket (ADR 0038 decision 4 and the phase-3
  precedent). The stack in the next PR keeps `GoatInfer*.v` compiling by
  teaching the unifier that a `Maybe` entry does not unify (`None`), so
  `infer_closed_sound` and `infer_mu_free` stay proved over the programs it
  accepts. A follow-up gives W the presence cases (surface a `Maybe` through a
  row, bind a presence variable to `Unit` or `Bool`) and extends the
  differential test.

## 4. Which lemmas change

| File | Change |
| --- | --- |
| `goat_ln.ott`, `Goat_ott.v` | `row_Maybe`, `e_spread`, `e_restrict`; five `req` rules; `rlacks` embedded before the relation, used as the formula `l # R` |
| `GoatDefs.v` | a `row_Maybe` case in `ap_row`, `open_row`, `lcr`, `gdr`, `ftv_row`, `frv_row`; `fs_set`, `fs_drop`, `rm`; `T_Spread`, `T_Restrict`; `st_spread1/2`, `st_restrict1/2`, `tr_spread*`, `tr_restrict` |
| `GoatRows.v` | `pi` reads a `Maybe` (`Unit` adds the field, anything else adds none); `req_pres` gains the five rules; `rm` commutes with `req` |
| new `GoatPresence.v` | the one hard lemma (below) and the lemmas under it |
| `GoatMu.v`, `GoatTags.v`, `GoatSubst.v` | the `row_Maybe` case of each mutual induction (`ap_open_mut`, `teq_ap`: `rlacks` is stable under `ap`, so `abs` maps to `abs`) |
| `GoatMeta.v` | `lc`, regularity, inversions, progress cases for both terms; canonical forms need no change |
| `GoatSound.v` | type substitution (L4/L5) and term substitution (L6) cases; preservation for `st_spread` and `st_restrict` |
| `GoatInfer*.v` | unifier returns `None` on a `Maybe` entry; `infer` returns `None` on the new terms (they are not yet inferred) |
| Den/Print/Shape | the cases that say `scoped` excludes the new terms |

The one hard lemma, **presence inversion**: if `Rf` is the row of a record
literal (only `Ext` entries, ending in `nil`) and `req Rf (l^P:T;R)`, then
`P = Unit`, or `P = Bool`, `req Rf R` and `Rf` has no `l`. It is what lets the
`st_spread` case of preservation pick update or extension from the record while
the type says it by `P`. Proof: a total normalizer `nf` that rewrites `Unit`
entries to `Ext` and drops a `Bool` entry whose tail (normalized) lacks the
label, shown to satisfy `req R (nf R)` and, by induction on the `req`
derivation, `req0 (nf R1) (nf R2)` where `req0` is the old relation (congruence
and swaps, no `pre`/`abs`) extended with the `Maybe` congruences and swaps. A
`req0`-invariant, the number of `Maybe` entries, finishes it: `Rf` has none, so
the normalized right side has none, so `P` was `Unit` or a lacking `Bool`.

## 5. What is proved, and the theorems

`progress`, `preservation` and `soundness` gain the cases above and keep their
statements; `typing D G e T` is unchanged. `make check-assumptions` still lists
the same eight theorems. Progress needs no inversion: a value base is a
record literal by canonical forms, and `set` and `drop` are total. Preservation
is where Q2 and Q7 pay. Worked examples go in `GoatPhase4.v`: `set_x` at a record
with and without `x`, `{...p, x: true}` for a numeric `x` has no derivation,
`restrict` then `spread` through a closed row, a rest pattern that names a label
the record lacks has no derivation.

## 6. The corpus: how the 42 programs go to 0

`core_corpus.rs` counts 42 programs under `Feature::Spread`
("outside the calculus: spread or restrict"): the spread and rest-pattern
examples of the docs and tests, `bump`, `countdown`, `go` (#147), `update`,
`set_x`, the recursive and record-holding variants, and the errors
(`{...3, x: 1}`, `{...p, x: "one"}`, a rest pattern naming a missing label).
The next feature in order, `Builtin`, is unaffected. 222 more programs sit under
`UnwritableType` ("an inferred type with a method or presence row"), the other
half of the same gap; it falls only as far as the presence rows go (the
method-flagged ones stay).

The follow-up that closes this (algorithm and differential, as #528 was for
tags) does three things:

1. **Reader.** `ExprKind::Spread { base, fields }` reads as nested
   `(spread E l e)`; `ExprKind::Restrict { record, labels }` as nested
   `(restrict E l)`. A `Maybe` row in an inferred type is written `l^P:T` on both
   sides of the comparison (the type column gains one form).
   `Feature::Spread` and the
   presence half of `UnwritableType` are deleted.
2. **Algorithm.** Unification surfaces a label through a `Maybe` entry, binds a
   presence variable to `Unit` or `Bool` (as `unify_presence` does), and keeps
   `l # R` closed rows (Q2-A). Soundness of the new cases is by the typing
   rules.
3. **One new, narrow skip.** A spread or restrict whose base row ends in a row
   variable the checker knows lacks the label (Q2-A's gap) is accepted by the
   checker and has no derivation. The reader detects the shape from the node
   types and counts it under `Feature::LacksOnTail`; the test (`f = program(p) do
   {x, ...r} = p if true then r else {x: 1} done done` is the one such program
   today, and the checker rejects it) pins its size. It goes to 0 with Q2-B.

So the skip falls from 42 to 0, with `LacksOnTail` standing in for the programs
Q2-B would compare.

## 7. Size and risk

Calibrated against phase 3 (#527: +1235 across 25 files, no change to `req`).

| Part | Lines |
| --- | --- |
| `goat_ln.ott`, `Goat_ott.v` (regenerated) | 60 |
| `GoatDefs.v` | 120 |
| `GoatRows.v`, `GoatPresence.v` | 350 |
| the case a `row_Maybe`/`e_spread`/`e_restrict` adds to each mutual induction (about 12 files) | 250 |
| `GoatSound.v`, `GoatMeta.v` (substitution, progress, preservation) | 250 |
| `GoatPhase4.v` | 200 |
| README, `docs/semantics.md`, ADR 0033 amendment | 150 |
| **Calculus and soundness** | **~1400** |
| Algorithm W, reader, differential | ~600, own ticket |

Risks, most serious first.

1. **Presence inversion (section 4).** It is the one lemma whose proof is not
   mechanical. The spike for it: state `req0`, `nf` and the two properties in a
   scratch file before any other change. If `nf` does not commute with
   `swap_em` the fallback is Q2-C.
2. **`rlacks` under `ap`.** `teq_ap` for `abs` needs `rlacks l (ap R) = true`
   from `rlacks l R = true`; true because `ap_row` leaves a spine alone, but it
   is a lemma of its own.
3. **Ott.** The embedded `rlacks` must precede the generated relation; checked
   by a prototype (Ott 0.34 keeps `embed` in source order).
4. **A late change of judgment**, the phase-2 lesson. Nothing here changes the
   judgment. If Q2-B is later wanted, `l # R` gains a `D` argument; the rule text
   and every lemma except the variable case carry over.

## 8. Outcome of the proof PR

The plan held. Differences from the text above, all small:

- `rm` is a function (`rmf`, returning an option) with `rm l R T R'` its graph,
  not an inductive relation: inverting an inductive `rm` over a row variable
  unrolls forever, and the functional form makes each `req` rule a computation.
- The guard `gd` of a recursive type skips the field type of an absent entry
  (`Bool` presence). `abs` drops that type, and a guard that counted it would
  not be preserved by equality in both directions.
- `ftv_row` and `frv_row` of a `Maybe` entry include the presence slot, as the
  plan says, and `GoatInferMuFree.v` counts it too (`mu_free_row`).
- The proof needs no change to `typing D G e T`, `inst`, `gen`, `kres` or any
  sort, as the plan predicted. About 1500 lines added across 28 files, 900 of
  them the new `GoatPresence.v` (`presence_inv`, `rm` respecting `req`),
  `GoatSpread.v` and `GoatPhase4.v`.
- Algorithm W, the corpus reader and the parser fragment are the follow-ups
  section 6 lists. `Feature::Spread` is therefore still in `core_corpus.rs`; it
  goes to 0 with the algorithm ticket.
