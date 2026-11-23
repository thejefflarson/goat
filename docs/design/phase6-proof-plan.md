# Phase 6 proof plan: structural ordering and equality as a typed primitive (design pass)

Status: DRAFT for the architect, with owner questions in section 9. Issue #455,
part of #435, governed by ADR 0037 (phase 6), ADR 0038 (the sort mechanism) and
ADR 0036 (the order itself). Written against `master` at 2a87719, after phase 5
stages 1 to 5 (iso-recursive `mu`, W with knots, methods in the rules), phase 3
(tag groups), phase 4 (spread and restrict), and #525 (W defers a comparison on
an open variable). The owner delegated the proof-model choices to this pass;
each is recorded in section 3 with the alternatives it beat. No `proofs/`,
`checker/`, `mir/` or ADR file changes in this PR.

Terms. A **sort** is the constraint a type variable carries in the calculus:
`Any`, `Numeric`, `Literal` today (ADR 0038). A **kinding environment** `D` maps
each type variable to its sort; `sat D k T` says `T` may stand where a variable of
sort `k` stands. **`Eq`** is the checker's `Kind::Eq`: any type with no function
inside it, which ADR 0036 makes the requirement of all six comparison operators
(`== != < <= > >=`), not of `==` alone. A **value** is a closed term that cannot
step (a numeral, a string, `unit`, a record of values, `con w tg v`, `fold v`, a
`program`). **`cmp_rel a b c`** (new, section 2) is the relation that says
comparing the values `a` and `b` gives `c`, one of `Lt`, `Eq`, `Gt`. A
**three-way result** is such a `c`; the operators read it through the existing
`cmp_holds o c`. **W** is the Coq model of inference (`GoatInfer*.v`). **A skip**
is a corpus program the differential test leaves out for a named reason.

## 1. What the checker and mono do today

Read from `checker/src/infer.rs` (`type_bin`, `join_operands`, `require`,
`constrain_kind`, `constrain_row`), `checker/src/kinds.rs`,
`mir/src/mono/structural.rs` (`compare`, `compare_fn`, `str_compare_fn`,
`equal_fn`) and ADR 0036.

**Typing.** `a < b` (and `<= > >= == !=`) joins its operands to one type, an `Int`
beside a `Float` widening to `Float` (ADR 0040), and requires the shared type to
satisfy `Kind::Eq`. `constrain_kind` decides that structurally:

| Type | `Eq` |
| --- | --- |
| `Int`, `Float`, `String`, `Bool`, `Unit` | yes |
| record, variant (a tag group, a list) | yes when every field type, every tag payload type, and a row variable's tail is `Eq` |
| recursive type `Rec(b, body)` | `body` is `Eq`, with the binder `b` assumed `Eq` while the body is walked (the `bound` set), so a tree `mu t. {v: Int; kids: List t}` is comparable |
| function | no, a spanned error (`can't compare ... it has a function inside`) |
| type variable | the variable gets the `Eq` kind (`add_kind`); a kind table is also kept for **row** variables, so unifying an `Eq` variable with `{x: t | rho}` puts `Eq` on `t` **and** on `rho` |

`Kind::Ordered` (`Int` or `Float` only) is a different constraint: it serves `/`
and a literal flowing beside a number (`require_number`), not `<`. `Appendable`
(`String` or a list, for `++`) is disjoint from the numeric kinds. Kinds combine as
a set, and `conflicts` is true only for a numeric kind with `Appendable`.

**Mono.** For `Int` and `Float` the operator stays one MIR `Cmp`. For any other
ground type mono derives a function memoized on the canonical type, returning
-1, 0 or 1, and the operator tests the result against 0 (so the operator is
`cmp_holds o c` read off the three-way result). The derived order:

- `Bool`: `false < true`. `Unit`: always 0 (both operands are still evaluated).
  Strings: bytewise over `StrLen`/`StrByte`, a prefix first.
- Record: field by field in label order, the first unequal field decides, the last
  field a tail call. Variant: tag rank first (`ranks`, below), then the payload
  left to right. A list is the variant `Empty < Link`, so it is lexicographic.
- Numbers inside a larger value: `==`, then `<`, else greater (ADR 0036 decision 5).
  A bare `Float < Float` is one `Cmp` and keeps IEEE semantics.
- Tag rank. A row holds labels sorted, so declaration order is not in `Ty`; the
  checker keeps `tag_ranks: HashMap<String, u32>` (`Lowered::tag_ranks`) beside the
  type, handing out numbers in declaration order, the prelude's group first. A
  group's tags take consecutive numbers.
- A comparison at `Func`, `Rec` or `Var` after `unfold_head` is a mono `Trap`; the
  checker never lets one through.

**What the differential corpus skips today.** `cargo run -q -p goat_checker
--release --example core_corpus` on `master` at 2a87719 writes 44168 programs and
skips these, among others:

| Skip | Count | Programs |
| --- | --- | --- |
| "a comparison of non-primitive operands" (`Feature::Ordering`) | 2 | `{x: 1, y: 2} >= {x: 1, y: 3}` and `{x: 1, y: true} == {x: 1, y: true}` |
| "a comparison at a parameter left generic" (`Skip::GenericComparison`) | 4 | `program(a, b) do a == b done`; `same = program(a, b) do a == b done` used at `Int`, `String` and a record; the two `clamp` programs, `math = {double: ..., clamp: program(x, low, high) do if x < low then low else if x > high then high else x done done}` |
| "tags and match" (`Feature::TagsAndMatch`, counted before `Ordering`) | 185 | includes every program that compares a tag or a list |
| "arithmetic on non-primitive operands" (`Feature::OperatorOperand`) | 7 | not this phase: `+ - * / // %` on records and `Unit` |

The enum order matters (`core_corpus.rs`: a program is counted under the first
feature in `Feature` order that it uses), so the 2 is a floor: it counts only the
programs with no tag, loop or builtin. When the tags corpus reader lands (phase 3's
corpus work, not yet on `master`), comparisons of tags and lists move from
`TagsAndMatch` into the comparison stages below.

## 2. How the calculus models it

Today `GoatDefs.v` types a comparison with `sig_cmp : kind o = k_cmp -> cmp_typ B
-> bin_sig D o B B Bool`, where `cmp_typ` is the four concrete types `Int`,
`Float`, `String`, `Bool`, and steps it with `bs_cmp_int`, `bs_cmp_float`,
`bs_cmp_str`, `bs_cmp_bool`. A comparison at a type variable has no derivation
(ADR 0038 decision 2: "A comparison stays at concrete types until the `Eq` and
`Ordered` sorts exist"), which is why #525 made W run twice and settle a comparison
at a concrete type (`lenient`, `resolved`, the `ora` argument of `bin_arg`).

This phase replaces the four concrete types by one sort and the four step rules by
one relation.

### 2.1 The sort `k_Eq`

`sort` gains `k_Eq`, placed between `Numeric` and `Any`:

```
Literal  finer than  Numeric  finer than  Eq  finer than  Any
```

so `finer` gains `finer k_Numeric k_Eq` (every `Numeric` type, `Int`, `Float` and a
closed record of numerics, is comparable) and the chain stays a chain.
`finer_lit` already puts `Literal` below everything. Appendable (`++`) is not in
the calculus; if it joins, it sits beside `Numeric` under `Eq` and the order stops
being a chain (a `finer_b` change, noted in section 10).

`sat D k_Eq T` is the existing `sat` with `Eq` cases:

- `Int`, `Float`: true. `String`, `Bool`, `Unit`: true for `Any` and `Eq`, false
  for `Numeric` and `Literal`.
- `typ_Var a`: `finer (D a) k_Eq`.
- `typ_Record R`: `rsat_eq D R`, every field satisfies `Eq` (a `row_Maybe l P T R`
  needs `T` to satisfy `Eq` whatever `P` is, as the checker's `constrain_row` does,
  so the predicate is stable when a presence variable is later set). A row that
  ends in a row variable is **not** `Eq` here; see Q4.
- `typ_Arrow`: false. This is the whole of "functions are not comparable".
- `typ_Mu B`: `B` satisfies `Eq` with `typ_Bvar _` read as true, the checker's
  `bound` set. The recursion is guarded (`GoatGuard.v`), so the body is finite.
- `typ_Grp w T`: every parameter the declaration `w` uses (slot code `6 + j`)
  satisfies `Eq` at the `j`th place of the spine `T`. Concrete slots are the five
  base types, all `Eq`; slot `0` (the group itself) is the coinductive case,
  decided by the group being named once. A parameter no slot mentions is not
  constrained, as in the checker, whose variant row never holds it. The check is a
  helper `spine_sat` over the spine, structural on `T`, so `sat` stays a
  `Fixpoint`.

`sat_finer`, `sat_ap` (`GoatSubst.v`, substitution respects sorts), `kres`,
`ext`, `typing_denv_agree` (Int satisfies every sort) and `sat`'s use in
`T_Let`/`T_Letrec` generalization carry over with one more case each.

### 2.2 The typing rule

`sig_cmp` becomes

```
sig_cmp : kind o = k_cmp -> sat D k_Eq B -> bin_sig D o B B Bool
```

and `cmp_typ` is deleted. The six operators share the rule exactly as the checker
shares one constraint. A mixed `Int`/`Float` comparison is still `float(e)` on the
`Int` side, inserted by elaboration (the reader), as for arithmetic: the calculus
has no mixed signature.

### 2.3 The step rule: a relation on values

A comparison on two values is `bin_step o a b (of_bool (cmp_holds o c))` for the
`c` that `cmp_rel a b c` gives. `cmp_rel` is an inductive relation, in the style
the README already uses for the opaque `Float`:

```
cr_int     : cmp_rel (num a) (num b) (z_cmp a b)
cr_float   : fl_pair x y -> cmp_rel x y c                    (any c: Float is opaque)
cr_str     : cmp_rel (str p) (str q) (str_compare p q)
cr_bool    : val_bool x = Some a -> val_bool y = Some b -> cmp_rel x y (bool_compare a b)
cr_unit    : cmp_rel unit unit Eq
cr_fold    : cmp_rel v1 v2 c -> cmp_rel (fold v1) (fold v2) c
cr_con_eq  : cmp_rel v1 v2 c -> cmp_rel (con w tg v1) (con w tg v2) c
cr_con_lt  : tg1 < tg2 -> cmp_rel (con w tg1 v1) (con w tg2 v2) Lt
cr_con_gt  : tg2 < tg1 -> cmp_rel (con w tg1 v1) (con w tg2 v2) Gt
cr_rec     : labs = sorted distinct labels of fs1 ->
             cr_fields labs fs1 fs2 c -> cmp_rel {fs1} {fs2} c
cr_fields  : lexicographic over labs, reading the FIRST field of each label in
             each operand: nil gives Eq; for l :: labs', a result c <> Eq from
             cmp_rel (get l fs1) (get l fs2) is the answer, and Eq goes on to labs'
```

Reading it against ADR 0036:

- **Records in label order.** A record value's spine lists its fields in source
  order, possibly with a shadowed duplicate (rows are scoped-label rows,
  `goat_ln.ott`). `cr_rec` fixes the order independent of both operands: the sorted
  distinct labels of the first operand, each read as the first field of that label
  in each operand. The order is the order of the calculus's `label`, a `nat`. This
  is not `rec_zip`'s order (`GoatRecArith.v` pairs by the first operand's spine
  order, which is fine for `+` and wrong for `<`, because `{y: 2, x: 1} < {x: 1,
  y: 2}` must not depend on which operand is written first). The proof needs the
  alignment fact that two values of one record type have the same distinct labels;
  `rec_zip` has the same obligation and the same source, `presence_inv` and the
  per-label characterization of `req` (`GoatRows.v`, L2'), so it is a precedent,
  not a new technique.
- **Tags by rank.** The rank of `con w tg` is `tg`, its position in the
  declaration `w`, which the term carries. ADR 0036's "a group's tags take
  consecutive places where it is written, the prelude's before the program's" is
  the checker's program-wide table restricted to one group, and values of one type
  all belong to one group, so only positions within `w` matter. The payload is
  `tag_payload w Ts tg`, the closed record of the slots labelled by position, so
  `cr_con_eq` followed by `cr_rec` compares the payload "left to right" because
  labels `0, 1, 2, ...` sort in that order. A tag with no slots has payload
  `unit`, which `cr_unit` makes `Eq`.
- **Lists.** With the prelude group `tag List = Empty | Link(_, List)` (`Empty` at
  position 0), `Empty < Link` and `Link(a, as) < Link(b, bs)` by `a` then `as`.
  No list rule exists: lists are instances of `cr_con_*` and `cr_rec`. Prefix-first
  falls out of `Empty < Link`.
- **Strings and numbers.** Unchanged (`str_compare`, `z_cmp`).
- **`fold`.** A value of a `mu` type is `fold v` (iso-recursive, phase 5), so
  `cr_fold` compares the unrolled values. This is not vacuous: the checker's
  `Rec` rule exists for trees like `mu t. {v: Int; kids: List t}`, which are finite
  because the recursion passes through a tag group's parameter.
- **Float.** `cr_float` relates a pair of Float values to every `c`. For a bare
  `Float < Float` the existing `bs_cmp_float` (any `Bool`, so a NaN comparison can
  be false) stays as the rule for a Float operand pair; `cr_float` covers a Float
  inside a larger value, where ADR 0036 decision 5's "`==`, then `<`, else greater"
  gives some three-way result. Over-approximating that by "any `c`" is sound for
  every theorem (preservation needs the result to be a `Bool`; progress needs one
  to exist) and is the same trade the README already made for `Float`
  arithmetic. It cannot say "a NaN sorts after everything" (see section 9, question 1).

**Determinism and totality.**

- *Totality.* `cmp_total`: if `sat d_any k_Eq A` and `v1`, `v2` are closed values
  of `A`, some `c` has `cmp_rel v1 v2 c`. This is what `progress` needs. By
  induction on the size of `v1`, generalizing `A` and `v2`, with the canonical-form
  lemmas by type: `canon_grp_spine` (a `con`), the `mu` canonical form (a `fold`),
  `Int`/`Float`/`String`/`Bool`/`Unit`, and a record. The size induction, not a
  type induction, handles recursive groups and `mu`: the type does not shrink
  across the recursive slot, the value does. `sat d_any k_Eq A` has no variable at
  `A` (`d_any` is `Any` everywhere), so every leaf is concrete.
- *Determinism.* On values with no Float leaf (`float_free`), `cmp_rel` is a
  partial function: `cmp_rel v1 v2 c1 -> cmp_rel v1 v2 c2 -> c1 = c2`. With Float
  leaves it is a relation, as `bin_step` already is. No theorem needs more:
  `progress` and `preservation` are for the relation.
- *Order laws (optional, stage 1d).* On float-free values of one `Eq` type,
  `cmp_rel` is reflexive on `Eq`, antisymmetric (`Lt` one way is `Gt` the other) and
  transitive. These are the facts the prelude's `sort`, `biggest` and
  `insert_sorted` need; they are not needed for soundness.

**`mu` and recursive types.** Comparison recurses on values, which are finite
trees, so a recursive type adds only the `Bvar` and `Mu` cases of `sat` and
`cr_fold`. `sat_eq_unroll` says `sat D k_Eq (mu B)` gives `sat D k_Eq (open_typ 0
(mu B) B)`: by induction on `B`, a `bv 0` becomes `mu B` and the hypothesis supplies
it, other forms recurse. This is what typing `T_Unfold` needs to hand the inner
values to `cmp_total`.

**Elaboration (`erase`).** `erase` drops `fold` and `unfold`, so `erase (fold v) =
erase v`. `cr_fold` makes `cmp_rel` agree with it: `cmp_erase : cmp_rel a b c ->
cmp_rel (erase a) (erase b) c` for values, by induction, which `erase_step`
(`GoatElab.v`) needs for the `st_bin` case. The typed converse in
`GoatElabConverse.v` reads the unerased shape off the type.

**Interaction with W.** The comparison becomes a generic operator like `+`: W
unifies the two operands (an `Int` beside a `Float` still needs the reader's
`float(e)`), unifies the result with a fresh `k_Eq` variable `eta`, and returns
`Bool`. A variable operand binds to `eta` by `finer_b`, so a `Literal` variable
survives (`1 < 2` leaves a `Literal` variable, which the instance defaults to `Int`,
ADR 0038 decision 3), and `program(a, b) do a == b done` is `forall a:Eq. a -> a ->
Bool`, instantiated at a fresh `Eq` variable per use. `generalize` already records
each quantified variable's sort and `instantiate` restores it. `bind` checks
`sat_b D k_Eq T` (the boolean twin of `sat`) before binding an `Eq` variable to a
non-variable, so an `Eq` variable meeting a function fails, which is the checker's
error. #525's machinery (the `lenient` run, `resolved`, `ora`, `settle`, the
`k_cmp` branch of `bin_arg`) has no work left and is deleted in stage 1a. The
README's "The one place it commits is a comparison" paragraph goes with it.

### 2.4 The sort does not reach inside a type

`unify_t` never changes `D` (README, "Algorithm W with sorted variables"): a
variable meets a non-variable type only if the type already satisfies the
variable's sort. The checker pushes the kind inward: `eta := {p: xi}` puts `Eq` on
`xi`. So with `same = program(a, b) do a == b done` and `f = program(x) do
same({p: x}, {p: x}) done`, W (stage 1) rejects `f` where the checker accepts it
(`xi` has sort `Any`, `sat Eq` of `{p: xi}` fails). The same gap exists today for
`Numeric` (README: "it does not push the sort onto a variable inside the record").
For `Eq` it is more reachable: any generic comparison on a compound containing a
parameter's type hits it. Stage 2 closes it (Q3, option B); the 6 corpus programs
in section 1 do not need it, because their compound operands hold only numerals
(`Literal` is finer than `Eq`).

**Measured (stage 2 spike, `differential/sort_gap.sh`).** The script patches a
scratch copy of the extracted algorithm so that `sat_b` accepts a variable of any
sort inside a type, and `rsat_b` a row variable, then reruns each program the
checker accepts and the algorithm refuses. Of 24295 checker-accepted corpus
programs the algorithm refuses 11, all recursive-type programs; none passes under
either leniency, so **0 corpus programs hit the inner-variable gap and 0 hit a
row-variable sort**. The gap is real: appended to the hand-written list, the five
programs `f = program(x) do same({p: x}, {p: x}) done` then `f(1)` (and variants
with two fields, `add` for `Numeric`, and an inline `{p: x} == {p: x}`) each make
the checker accept and W refuse, so the differential reports 5 mismatches. No
generator or source in the corpus builds one, so stage 2's propagation (Q3, B)
would change no corpus verdict; whether to pay for it (every `unify_*` statement
and its callers in `infer` change) is a completeness choice, not a soundness one.

## 3. Proof-model decisions and the alternatives they beat

**Q1. How to say what `<` does on a non-primitive value.**

- **A. A relation `cmp_rel` on values, called from one `bin_step` rule (chosen).**
  Matches how `bin_step` already treats `Float` (a relation, not a function), keeps
  evaluation untyped (a step depends on the two values and the operator, never on a
  type), and keeps the `Float`-leaf cases honest. Determinism and totality are
  lemmas over it.
- **B. A Coq function `cmp_val : exp -> exp -> comparison`, with an oracle
  argument for the Float leaves.** Determinism is free, but the function needs a
  `Float` oracle parameter threaded through `bin_step`, which breaks the README's
  "needs no axiom or parameter" property and makes `bin_step` depend on an extra
  argument in every theorem statement. Rejected.
- **C. Small-step rules that rewrite `a < b` on a record or tag to nested `if`s on
  the fields.** It mirrors mono's derived function and needs a three-way primitive
  per scalar plus a rule per constructor, for a result that `cmp_rel` states in
  eight lines; a list comparison becomes a loop in the *semantics*, making
  termination of a comparison a proof obligation. Rejected: mono is not in the
  proofs (CLAUDE.md: errors come from the checker; the proofs cover the checker's
  language), so mirroring its derivation buys nothing.
- **D. Elaborate each comparison into a derived `letrec`/`match` function in the
  term language, as mono does.** The most faithful and the largest; it would
  verify the derivation scheme, which is mono's job and a different theorem.
  Recorded as a possible later refinement proof, not this phase.

**Q2. How to align record fields.** The relation (A) fixes the label set by the
first operand and reads both operands by label (`cr_rec`), versus pairing by spine
order (`rec_zip`'s order, wrong for `<` as shown in 2.3) versus a type-indexed
comparison that walks the type's row (rejected: a step may not depend on a type).

**Q3. Whether the sort propagates into the types it meets.**

- **A. No propagation (stage 1).** Smallest change; leaves the stated gap of 2.4,
  counted in the corpus.
- **B. `push_sort` at `bind` (stage 2).** When an `Eq` variable binds to a type
  with an inner variable of a coarser sort, rename that inner variable to a fresh
  variable of sort `Eq` (the substitution `xi := eta'`), returning the extended
  kinding environment. Renaming respects the sorts (`kres`: `Eq` is finer than
  `Any`), so `Good`'s "only a fresh variable gets a sort, by `upd`" invariant
  holds; no `D` mutation is needed. The cost is that `unify_t`, `unify_k` and
  `unify_co` return a kinding environment (today they return `(s, n')` and prove
  `kres D D`), so each statement and the callers in `infer` change. It also closes
  the `Numeric` gap for records of variables. Chosen as a measured stage, after
  stage 1 and a spike that counts how many generated programs hit the gap.
- **C. Make the checker stop propagating.** That changes which programs are
  accepted, a language change; rejected.

**Q4. Row-variable sorts.** The checker keeps kinds on row variables too, so `a ==
b` followed by `a.x` gives `a` the type `{x: t | rho}` with `rho` of kind `Eq`.
The calculus's `denv` is `typvar -> sort`: a row variable has no sort and
`rsat` treats a row ending in a variable as false.

- **A. Leave it (chosen for stages 1 and 2).** Rows in an `Eq` type must be
  closed; a program that compares an open record whose row the checker kinds is
  refused by W (and counted by the driver as an algorithm refusal, as `DeepKnot`
  is). Same behavior as `Numeric` today.
- **B. Add a second kinding environment for row variables** (`rden`), with `Any |
  Numeric | Eq`, threaded through `kres`, `ext`, `gen`, `inst` and W. Large (every
  sort lemma gains a row twin) and overlaps #564 (a `lacks` sort on row variables),
  which needs the same machinery. Recommended as one effort with #564 if the spike
  shows a count worth closing; not part of this phase's critical path. Section 10
  lists it as risk 3.

**Q5. Where Float's NaN behavior lives in the model.** `cr_float` is any `c`. A
specific model of ADR 0036's rule would need a NaN in the calculus (a Float is an
opaque nat). Not modeled; section 9 question 1 is why a specific model would first need
the owner.

**Q6. `Ordered`.** ADR 0038 decision 2 names both `Eq` and `Ordered`. `Ordered`
(`Int` or `Float`) serves `/` in the checker; after elaboration every `/` operand
is a `Float` and W gives `/` the type `Float`, so no sort is needed. This phase
adds `Eq` only and says so in ADR 0038's follow-up note.

## 4. Which lemmas and files change

| File | Change |
| --- | --- |
| `GoatDefs.v` | `sort` gains `k_Eq`; `finer` gains `finer_numeric_eq`; `sat`/`rsat` gain the `Eq` cases (`String`, `Bool`, `Unit`, `Mu`, `Bvar`, `Grp` via `spine_sat`, `rsat_eq`); `cmp_typ` deleted, `sig_cmp` uses `sat D k_Eq`; `cmp_rel` and its helpers (`rec_labels`, `get_first`); `bin_step` loses `bs_cmp_int`, `bs_cmp_str`, `bs_cmp_bool` for `bs_cmp` through `cmp_rel`, keeps `bs_cmp_float` |
| `GoatSubst.v` | `sat_ap` for the new cases; `cmp_typ` use at line 785 goes |
| `GoatMeta.v` | `progress`'s comparison case calls `cmp_total` (it destructs by type today); `sat_finer` gains Numeric to Eq |
| new `GoatCompare.v` | `cmp_total`, `cmp_det_float_free`, `sat_eq_unroll`, the record alignment lemma, `cmp_erase`, (optional) the order laws |
| `GoatSound.v` | the `st_bin` case of preservation uses the new `bin_step`; `typing_denv_agree` and `sch_more_gen` get the extra sort case |
| `GoatInfer.v` | `cmp_ty`, `open_var`, `settle`, `bin_arg`'s `k_cmp` branch, the `lenient`/`ora`/`resolved` parameters and the second run of `infer_closed_env` removed; the comparison case unifies with a fresh `k_Eq` variable |
| `GoatInferSort.v` | `sat_b` for `Eq`, `finer_b` for the new chain |
| `GoatInferSound.v`, `GoatInferGuard.v`, `GoatInferW.v`, `GoatInferKnot.v`, `GoatInferTyp.v`, `GoatExtract.v` | the `ora`/`lenient` parameters drop out of every signature; the comparison case of `infer_sound` and `infer_guard` is the `Numeric`-operator case with `Eq` |
| `GoatElab.v`, `GoatElabConverse.v` | the `st_bin` case uses `cmp_erase` |
| `GoatPhase1.v`, `GoatPhase2.v` | the examples that assumed a comparison at a concrete type (12 and 4 mentions of `cmp_typ`/`bs_cmp`) are restated |
| new `GoatPhase6.v` | worked examples, section 5 |
| `GoatAssumptions.v` | `cmp_total` joins the listed theorems |
| `checker/examples/core_corpus.rs`, `differential/driver.ml`, `differential/README.md` | section 6 |
| `proofs/README.md`, `docs/semantics.md`, ADR 0038 (a follow-up note), `proofs/_CoqProject`, `proofs/Makefile` | the phase-6 section, the Eq sort, the deleted two-run paragraph |

`goat_ln.ott` does not change: the comparison operators and every term the relation
reads (`unit`, record, `con`, `fold`) already exist. The typeset `goat.ott` gains
the `Eq` sort and the comparison rule in the stage that closes the phase. The parser
proofs (T1 to T3) are expected unchanged because a comparison is already the one
operator the fragment allows and a record literal is a primary; stage 1b checks that
`GoatPrint*`'s printed fragment accepts a record operand and says so if it does not.

## 5. What is proved

- **`progress`, `preservation`, `soundness`, `infer_closed_sound`, `infer_guarded`,
  the three of `GoatElab.v`** keep their statements, with 0 admits and no new axiom
  (`make check-assumptions`). The comparison case of `progress` is the new work.
- **`cmp_total`** (section 2.3), new to `GoatAssumptions.v`'s list.
- **`cmp_det_float_free`, `cmp_erase`, `sat_eq_unroll`** (supporting lemmas).
- **Order laws** (stage 1d, optional).
- **Worked examples (`GoatPhase6.v`).** Each ADR 0036 clause as a `cmp_rel`
  derivation or an `Example` on `bin_step`: `1 < 2`, `"ab" < "abc"`, `false < true`,
  `() == ()`, `{x: 1, y: 2} < {x: 1, y: 3}` written in both field orders, `Low <
  Medium < High` over `tag Level = Low | Medium | High`, `Empty < Link(1, Empty)`,
  `Link(1, Empty) < Link(1, Link(0, Empty))` and `Link(1, Empty) < Link(2, Empty)`
  (lexicographic with a prefix first), a tree `fold({v: 1, kids: Empty})` against
  another. And what has no derivation: a comparison at a function type, at a
  record with a method, `Link(1, Empty) < Empty` of two different group types, and
  at a variable of sort `Any`.

Not proved, and said so in the README: that mono's derived functions compute
`cmp_rel` (mono is outside the proofs); that the reader numbers labels in label
order (section 6, the bridge); IEEE behavior inside a compound (Q5).

## 6. The corpus: how the two skips go to 0

A count goes to 0 when its feature lands, and its programs then show up under the
next feature they use or are compared (`differential/README.md`).

**"A comparison at a parameter left generic" (4).** Stage 1a. After W gives a
comparison an `Eq` variable (2.3), the reader stops skipping a comparison whose
operand is a variable (`Skip::GenericComparison`, the `generic_comparison` field and
its tracking in `in_comparison`, and the `FORCED` list that pins the programs the
rule used to misjudge, `core_corpus.rs`) and the driver compares them. The four
programs become compared; the `same` program is the interesting one, since one
`Eq` scheme is used at `Int`, `String` and a record. Risk: a program in the 44168
that the checker accepts and W rejects (the no-propagation gap, 2.4) would surface
as a mismatch. The stage report counts them first; if any appear, stage 2 moves
ahead of the reader change, or the driver counts them as algorithm refusals.

**"A comparison of non-primitive operands" (2).** Stage 1b. The reader's
`non_primitive` test (a record, `Unit`, a `Rec` or a `Variant` among the operands'
checker types) no longer counts `Ordering`; the two programs have `Literal` fields,
which satisfy `Eq`, so W types them without propagation. `Feature::Ordering` is
deleted: tags are counted earlier in `Feature` order and a program that compares a
variant must build one, so after the reader handles record and `Unit` operands no
program can reach it. The comparison of two `Float`-bearing records is compared like
any other.

**Beyond the two.** The "tags and match" skip (185) is phase 3's reader work, not
this phase's; when it lands the comparisons of tags and lists are compared by stage
1c's rules, with no further change here. The reader writes a `Rec`-typed operand as
an `R` line today (recursive type, compared by W's types as regular trees) and needs
no change.

**The label bridge.** The calculus orders labels as `nat`; the checker orders
labels by their string. The reader numbers a label by first use
(`Reader::labels`), which is not monotone in the string. The proofs hold for any
order on `label`; whether the compiled program agrees with the calculus on a
record comparison depends on the numbering being monotone. The differential test
compares types, not values, so this is a trusted bridge, like `float(e)`. Stage 3
renumbers labels by sorted name when it writes the corpus (a pass over the
finished term; the cost is small and is the only change that makes the bridge true
in the programs the test reads). The same holds for tag position: the reader must
write the prelude group `List = Empty | Link` with `Empty` first.

## 7. Interactions

- **#525 and #510.** The two-run W (`lenient`, `ora`) exists because a comparison
  had no sort. Stage 1a removes it, so every theorem and extraction signature loses
  two parameters. This is the largest mechanical churn in the phase (the ten
  files in section 4) and is why stage 1a is the biggest; it is a deletion of
  machinery, so no new idea is proved. The two minimal terms of #510 (`v = 71 //
  88` then `v <= v` and `v - 3.1`) must keep typing as `Float`; with `Eq` they
  do, because `v`'s variable stays `Literal` until the `-` binds it to `Float`. A
  Coq example in `GoatPhase6.v` pins both.
- **#564 and Q4.** A `lacks` sort on row variables needs a row kinding
  environment; so does Q4-B. Whichever lands first defines it, and the other uses
  it. Say so in whichever PR is second.
- **#433.** Independent. A parameter receiver's knot changes which `Rec` types a
  program has; `sat Eq` of a `mu` is defined for any guarded body.
- **Tags corpus reader.** Independent of this phase's order; the dependent stage is
  1c's differential coverage, not its proofs (the Coq examples cover tags and
  lists).
- **Proof gate (ADR 0037).** This PR touches none of `grammar/goat.peg`,
  `checker/src/{infer,lower,ty}.rs`, `prelude/prelude.goat`, so it needs no
  waiver. The stages change `proofs/`, which satisfies the gate; stage 1a/3's
  reader edits are `checker/examples/`, outside it.

## 8. Staged PR plan

Sizes are lines added, calibrated against phase 5 (stage 3 about 1100, stage 5
about 1200) and phase 2's sorts. The `Goat_ott.v` file does not change.

| Stage | Contents | Size | Corpus effect |
| --- | --- | --- | --- |
| 0 | this note | 520 (docs) | none |
| 1a | `k_Eq` on the primitives and `Unit`: `sort`, `finer`, `sat` (Int, Float, String, Bool, Unit, Var, Arrow false), `sig_cmp` at `sat D k_Eq`, `cmp_rel` for scalars and `unit`, `progress` for them, W's comparison through a fresh `Eq` variable, deletion of `lenient`/`ora`/`resolved`/`bin_arg`'s comparison branch across `GoatInfer*.v` and extraction, the reader and driver change, `GoatPhase6.v` (scalars, #510's two terms, `same` at three types) | ~900 added, ~350 deleted | `GenericComparison` 4 -> 0 |
| 1b | records: `rsat_eq`, `rec_labels`, `cr_rec`, the alignment lemma, `cmp_total` for records, W's `sat_b` for records, the reader reads record and `Unit` operands, `Feature::Ordering` deleted, examples (both field orders) | ~800 | `Ordering` 2 -> 0 |
| 1c | tags and `mu`: `spine_sat`, `Mu`/`Bvar` in `sat`, `sat_eq_unroll`, `cr_con_*`, `cr_fold`, `cmp_total` for groups and folds, `cmp_erase` and the `GoatElab` cases, examples (`Level`, lists, a tree) | ~700 | none (the tags reader is not here) |
| 1d (optional) | the order laws on float-free values | ~400 | none |
| 2 | sort propagation: `unify` returns the kinding environment and renames an inner variable of a coarser sort to a fresh `Eq` (or `Numeric`) variable; a spike first counts the programs the gap refuses | ~800, spike ~100 | none unless the spike finds programs |
| 3 | close: label renumbering in the reader, README and `docs/semantics.md` sections, ADR 0038 follow-up note, `goat.ott` Eq rule, `GoatAssumptions.v` | ~250 | confirms 0 |

Ordering: 1a, 1b, 1c in sequence (each builds on the previous sort and relation);
1d and 2 are independent of each other and of 3 after 1c; 3 last. The reader work
in 1a and 1b depends only on those stages' Coq. The spike of stage 2 can run
against stage 1b's W at any time. Total about 3500 to 3900 lines of Coq and Rust
beyond the note, mostly 1a's deletions plus 1b/1c's alignment and canonical-form
work.

## 9. Owner questions

Nothing in this plan changes which types are comparable: it models ADR 0036 as
accepted (every type with no function inside, ordering by structure). One point
inside ADR 0036 does not hold as written, and one choice follows from it.

1. **ADR 0036 decision 5's NaN rule does not give "a NaN sorts after everything".**
   Mono derives a number's three-way order as `==`, then `<`, else greater
   (`compare` in `mir/src/mono/structural.rs`). Take a record with one `Float`
   field. For `{x: NaN}` against `{x: 0}` the test gives greater, which puts the NaN
   after 0 as the ADR says. For `{x: 0}` against `{x: NaN}` it also gives greater
   (`0 == NaN` and `0 < NaN` are false), so `{x: 0} > {x: NaN}` is true as well,
   and both `a > b` and `b > a` hold. The order is not antisymmetric on NaN, so
   `sort` on records holding NaNs depends on the algorithm's comparison order.
   The proofs do not need an answer (`cr_float` is any `c`, section 2.3, and the
   order laws of stage 1d hold on float-free values only), but the README's claim
   of a total structural order is false for NaN until it is settled. Options:
   (a) keep the rule and state in ADR 0036 that NaN breaks antisymmetry (nothing
   to implement); (b) three tests, `==`, `<`, `>`, then a NaN test, so a NaN sorts
   after every non-NaN and equals another NaN in the order (a change to mono and a
   language-visible change to `sort` on NaNs, and `==` on records would still say
   false for NaN fields). I recommend (b) in a separate ticket because it restores
   the order the ADR describes, but it changes what the language does, so it is
   yours to decide. Until then the proofs take (a).
2. **None other.** The remaining modelling choices (relation against function,
   label order, sort propagation, row-variable sorts) are proof-internal and
   decided in section 3.

## 10. Risks

Most serious first.

1. **Stage 1a's churn.** Removing `lenient`/`ora` touches every `infer` signature
   and the extraction. The proofs are a deletion, but a signature change across ten
   files breaks every statement that names `infer`. Mitigation: the comparison is
   the only user of `settle`, so the change is mechanical, and stage 1a can land as
   its own PR if it grows.
2. **The record alignment lemma (stage 1b).** Two values of one record type have
   the same distinct labels; it rests on `req`'s per-label characterization and
   `presence_inv`. `rec_zip` proved the same shape for arithmetic, so there is a
   precedent, but the comparison also needs the sorted label list to be canonical
   (same set, same sort, same list), which is new. If it fights, the fallback is to
   require `sat Eq` rows to be closed `row_Ext` chains and prove alignment for
   those only.
3. **The corpus count of the propagation gap and Q4's row sorts.** Unmeasured. A
   comparison of an open record whose row the checker kinds (`program(a, b) do
   (if a == b then 1 else 2) + a.x done`) is refused by W until Q4-B. The stage 2
   spike prints the number first; if it is zero in the 44168 programs and the
   generators, Q4-B waits for #564.
4. **A third constraint on a sort chain.** `Appendable` would sit beside `Numeric`
   under `Eq`, turning the `finer` chain into a lattice. `finer_b` and `bind`
   assume a chain (a variable binds to the finer of two). `++` is not in the
   calculus today.
5. **Trusted bridges grow.** Label numbering and the group's declaration order are
   reader facts the test does not check (section 6). They are stated in the README,
   like `float(e)`.
6. **Value semantics are not differentially tested.** The driver compares types.
   `cmp_rel` is checked against ADR 0036's clauses by worked examples, not against
   the interpreter. A table test in `mir` or `tests/` that pins the ADR's
   orderings (including a record in two field orders and a list prefix) would close
   most of that for little; it is outside this plan's stages and I suggest it as a
   separate ticket.
