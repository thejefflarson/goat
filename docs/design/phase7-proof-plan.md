# Phase 7 proof plan: the inference algorithm is complete, and a nightly fuzzer tests it (design pass)

Status: DRAFT for the architect, with owner questions in section 9. Issue #456,
part of #435, governed by ADR 0037 (decisions 2 and 6, and the amendments), ADR
0038 (sorts) and the decision recorded on #456 (2026-11-14): no immediately
applied function literals get let-polymorphism, so `T_AppPoly` and rank-2 are out
and completeness is stated against the rules the checker implements. Written
against `master` at 9f03ec0, after phases 1 to 6 (and the soundness half of
phase 7, which is `infer_closed_sound` and `infer_elab_sound`). The owner
delegated the proof-model choices to this pass; each is recorded in section 3. No
`proofs/`, `checker/`, `fuzz/`, workflow or ADR file changes in this PR.

Terms. **W** is the Coq model of inference (`GoatInfer.v`, `GoatInferKnot.v`,
`GoatCoerce.v`, `GoatInferW.v`): Hindley-Milner algorithm W with Leijen's row
unification, a sort on each type variable, a knot-tying unifier for recursive
types, and head coercions. **The rules** are the inductive relation `typing D G e
T` in `GoatDefs.v`. A **sort** is the constraint a type variable carries (`Any`,
`Numeric`, `Literal`, `Eq`); a **kinding environment** `D` maps each type variable
to its sort (ADR 0038). **`kres D D' S`** says the substitution `S` sends each
variable of `D` to a type that satisfies that variable's sort in `D'`. **An
instance** of a type `T'` in `D'` is `S T'` for some `S` with `kres D D' S`.
**`erase`** drops `fold` and `unfold` from a term (`GoatElab.v`). **`unroll_eq n
T T'`** is the calculus's equality of recursive types: a finite chain of at most
`n` unfoldings and foldings (`GoatDefs.v`). **A mgu** is a most general unifier.
**Fuel** is the natural-number argument that makes W's recursion structural; a
run that exhausts it returns `None`. **The corpus** is the 44,380 programs
`checker/examples/core_corpus.rs` writes; **the driver** is `differential/driver.ml`,
which runs the extracted W on them (`make -C proofs differential`).

## 1. What exists and what is missing

**Soundness is done.** `infer_closed_sound`: if `infer_closed_elab fuel e = Some
(D, T, e')` then `typing D nil e' T` and `erase e' = e`. `infer_guarded` adds that
every recursive type W returns is guarded. All are checked closed
(`GoatAssumptions.v`), with 0 admits.

**Completeness is not started.** ADR 0037 decision 2 asks W to infer "a principal
type for every program the rules accept". Today the evidence is the differential
test: of 44,380 corpus programs, 42,958 are compared with 0 mismatches, and the
rest are skipped for named reasons (`proofs/README.md`, "Known incompleteness").
That is a measurement of the programs the corpus holds, which is what decision 6
accepts for the tie to the Rust checker but not for decision 2's theorem about W.

**The fuzzer does not reach W.** `.github/workflows/nightly-fuzz.yml` runs four
bolero targets for 20 minutes each on `ubuntu-latest`
(`differential_interp_vs_wasm`, `check_never_panics`, `compile_never_panics`,
`parse_recovery_holds_its_invariants`). None runs the extracted W. ADR 0037
decision 6 says the differential runs "on the fuzzer's programs nightly"; no job
does that yet.

## 2. The theorem

### 2.1 What the rules derive, and what "the same program" means

The checker's types are equi-recursive (a type equals its unrolling); the rules'
are iso-recursive (`fold` and `unfold` are terms). The phase 5 amendment settled
that the bridge is `erase`: W returns an elaborated `e'` with `erase e' = e`. So
the declarative side of completeness is not `typing D nil e T` on the source
`e`, which has no `fold`; it is the existence of an elaboration the rules accept:

```
typable e T  :=  exists e', erase e' = e /\ typing d_any nil e' T
```

`d_any` is `Any` everywhere (the program judgment, ADR 0038). `T` may hold free
variables of sort `Any` and nothing else free.

### 2.2 Statement A (the plain fragment), proved first

A term is **plain** when it holds no `fold`, no `unfold` and no method field
(`fs_meth`). For a plain term `erase e' = e` forces `e' = e`, so no coercion
enters and no `T_Obj`, `T_Fold` or `T_Unfold` is used.

```
Theorem infer_complete_plain : forall e T,
  lc e -> plain e -> typing d_any nil e T ->
  exists fuel D T' e'',
    infer_closed_elab fuel e = Some (D, T', e'') /\
    exists S, kres D d_any S /\ teq (apT S T') T.
```

Read: if the rules type a plain closed program, W accepts it, and the type `T`
the rules gave is an instance of the type `T'` W returned, up to `teq` (record
fields in any order, a presence `Unit` read as a present field). `T'` is
principal. Three corollaries follow without more proof:

1. **Typable if and only if accepted** (with `infer_closed_sound`): on plain
   programs W accepts exactly what the rules derive. This is the sentence ADR
   0037 decision 2 wants, and it makes a non-derivation theorem out of every W
   rejection: W rejects, so no derivation exists. The README's open item
   ("no theorem that `{...lit, x: 1}.a()` has no derivation") closes this way
   once statement B covers methods.
2. **Principal types are unique up to renaming:** two principal types are
   instances of each other.
3. **The differential test has an oracle with a proved meaning:** a plain program
   where the checker accepts and W rejects is a bug in the checker, in the
   corpus reader, or in the rules, never in W's search.

`∃ fuel` is deliberate. W's recursion is fuel-indexed, and a polynomial bound on
the fuel does not exist (principal types of Hindley-Milner terms can be
exponentially large, and `unify_t` spends one unit of fuel per node it visits). The
theorem says some fuel is enough; `infer_fuel_mono` (section 4, L0) says more is
too. The driver runs at 100,000.

### 2.3 Statement B (recursive types and methods), a later tier

```
Theorem infer_complete : forall e T,
  lc e -> typable e T ->
  exists fuel D T' e'',
    infer_closed_elab fuel e = Some (D, T', e'') /\ erase e'' = e /\
    exists S n, kres D d_any S /\ unroll_eq n (apT S T') T.
```

The only change is that `teq` becomes `unroll_eq n`: the rules' `T_Fold`,
`T_Unfold` and `T_Obj` equate a recursive type with its unrolling, so a derivation
may use a recursive type where W's principal type has the unrolled one. Section 6
says what this needs and why it is a separate tier.

### 2.4 The fragment

Statements A and B cover every term of `goat_ln.ott` as it stands after phase 6:
the core and operators (phase 1), `letrec` groups (2), tags, `match` and lists (3),
spread and restrict with presence (4), `mu`, methods and `self` (5), comparison
at the sort `Eq` (6). The parser's reader (`core_corpus.rs`) and the printer are
not part of the theorem; their agreement with the checker is the differential
test's job (the trusted bridges in `proofs/README.md`).

## 3. Where W is known to be incomplete, and what to do about each

Each entry lists what the gap is, whether the rules derive the program (that
decides whether it falsifies completeness), and the decision. **Fix first** means
the theorem is false while the gap stands; **outside** means the hypothesis of
the theorem already excludes the program, so the gap costs nothing.

| Gap | Size today | Derivable in the rules? | Decision |
| --- | --- | --- | --- |
| Sort propagation, #623 | 5 hand-written programs; 0 of 24,295 checker-accepted corpus programs | Yes (`f = program(x) do same({p: x}, {p: x}) done`, `f(1)`) | **Fixed** (stage 7.3, sort half): the unifiers return the environment and push the sort (`push_sort`) |
| No sort on a row variable (the checker kinds `Eq` on a row tail) | 0 corpus programs; `program(a, b) do (if a == b then 1 else 2 done) + a.x done` shows it | Yes: `rsat` reads the row variable's sort | **Fixed** (stage 7.3b): a sort pushed onto a type variable's binding reaches its row variables (`push_sort_r`) |
| `lacks` on a row variable, #564 | 222 corpus programs (`LacksOnTail`) | Yes (`T_SpreadL`, stage 7.2) | **Fixed** (stage 7.3b): the unifier passes lacks and sort to a fresh tail, `restrict` gives its tail the label, a spread tries `T_SpreadL` first; the skip is gone and the 222 programs compare |
| `sat_b` answers `Any` only for `mu` and tag groups | 0 in the corpus (the reader skips tags, 185) | Yes: `sat` holds of a comparable tag group, W refuses to bind an `Eq` variable to it | **Fixed** (stage 7.4): `sat_b_iff` proves `sat_b` decides `sat`, `mu` and groups included; the reader's group-comparison skip is gone |
| `T_Let` takes any pin `Tm` | `r = {a: 1}  {x: r.a + 1.5, y: r.a // 2}`, about 2 corpus programs, 3,100 before ADR 0038's addendum | Yes, with `Tm = Unit`: the rule generalizes the record's `Literal` variable; the checker and W reject | **Fix first, in the rule**: add the premise that `Tm` holds every `Literal` variable of `T1` unless `e1` is a function, a bare numeral or a `letrec` (stage 7.1). The checker is the language (ADR 0038 addendum), so the rules narrow, not W widen |
| Deep coercion (3 programs, #606), the row knot (6), a group member that needs a `fold` around its lambda (1) | 10 corpus programs | No `e'` has `erase e' = e` (it would need an eta-expansion; `T_Letrec` forbids `fold` of a lambda) | **Outside**, because `typable` demands such an `e'` |
| Two `mu` types for one regular tree, `step(ball).x` (#606) | 1 program | No finite `unroll_eq` relates them (the issue's measurement), so no `e'` | **Outside** |
| `unroll_eqb` is a bounded search, "not complete" (`GoatInferKnot.v`) | not measured | Yes, whenever some `unroll_eq n` holds and the search budget is below `n` | **Statement B only**; this is the hard part of tier B (section 6) |
| 65 `SplitGroup` programs: a value binding uses a group member before the group's last member | 65 corpus programs | The reader hoists the group into one `letrec`, which the rules generalize; the checker uses the member at its monomorphic type, so the two disagree by construction | **Outside**: the reader skips them, the term is not in the fragment. Whether the checker's behavior is intended is owner question 2 |
| Mixed `Int`/`Float` (`float(e)`), `Ordered`, `Appendable` | the reader's job (`differential/README.md`) | Not in the rules | **Outside**; the differential test checks `float(e)` placement, and these are not theorem hypotheses |

Two lessons the table carries. First, **completeness is false against the rules
as written** because of `T_Let`: the rules derive a program the language rejects.
Soundness cannot see this; only completeness's mirror image, "the rules derive no
more than the checker accepts", does. Section 4's stage 7.1 audits every rule for
the same shape before the proof starts. Second, **the 11 refusals of #606 cost
nothing in statement A**: a program that needs a recursive type has no plain
derivation, so the theorem never mentions it, and statement B excludes them by its
`erase e' = e` hypothesis rather than by proving non-derivability.

## 4. Proof strategy

The proof is the standard completeness proof of algorithm W (Damas and Milner
1982; mechanized in Coq by Dubois and Menissier-Morain 1999, in Isabelle by
Naraschewski and Nipkow 2000 and Nipkow and Urban's AFP entry), adapted to four
things this calculus adds: sorts, rows with scoped labels, presence, and `Tm`
pins. Leijen's "Extensible records with scoped labels" (2005) proves the row
half on paper; nothing mechanizes it for this calculus, so that is new work.

**The induction.** By mutual induction on the derivation of `typing` and
`field_typing`, generalizing over the algorithm's state, prove the principal-type
statement the classical proofs use:

> If `S1` respects the sorts (`kres D D1 S1`), `G1` is an instance of `S1 G`
> (`ctx_le`, below), and `typing D1 G1 e T1`, then for some fuel
> `infer fuel D G e n = Some (s, D', T, n', e')`, and there is `S2` with `kres D' D1
> S2`, `S1` agreeing with `S2 . s` on every variable below the supply `n`, and
> `teq (apT S2 T) T1`.

The closed theorem is the case `G = G1 = nil`, `D = D1 = d_any`, `S1 = id`. The
lemmas, in the order they are needed:

**L0, fuel and supply.** `infer_fuel_mono` and `unify_fuel_mono`: a `Some` result
at fuel `f` is the same at `f + 1`. Every case of the induction sums fuel over its
sub-runs, so the fuel of the whole run is the sum plus one. The fresh-variable
supply invariant `DOk` (D is `Any` beyond `n`) is already proved for soundness
and is reused as is. About 250 lines.

*As built (stage 7.5, `GoatCompleteFuel.v`).* The statement above is true of
`unify_t` and `unify_r` and false, or at least not provable, of everything that
calls them. `None` means both "no unifier" and "out of fuel", and four places
branch on `None`: `coerce_dec` (`teq_dec` first, then unfold, then fold),
`unify_co` (`unify_t`, then `unify_k` and `coerce_dec`), the two-`mu` case of
`unify_k` (the bodies, then an unrolling) and `infer`'s own `spread_present`
fallback and `unify_mem`. A larger fuel can turn the first branch's `None` into a
`Some` that replaces the fallback's answer, so `infer f = Some r` does not give
`infer (S f) = Some r`. What is proved instead:

- `unify_t_mono`, `unify_r_mono`: `f <= g` and `Some r` at `f` give `Some r` at
  `g`. `teq_dec_mono` follows.
- `Stable P`: `P` holds at every fuel from some point on. It is closed under
  conjunction (`Stable_and`), under weakening (`Stable_mono`) and under the step
  from sub-calls at fuel `f` to a caller at `S f` (`Stable_below`).
- `unify_co_stable`: a `unify_t` success at one fuel is a stable, coercion-free
  `unify_co` success. The plain fragment (no `fold`, `unfold` or method) reaches
  `unify_co` only this way.
- `infer_app_stable`: the composition for one construct, to show the shape every
  L3 case takes. L3 states each case as "the sub-runs are `Stable`, so the run is
  `Stable`", and L2 supplies `Stable` unifier runs from `unify_t_stable`. The
  closed theorem then asks for one fuel in `Stable`, which exists.

So `infer_fuel_mono` is not a lemma of the development and `∃ fuel` in statement A
is read as `Stable`. The theorem's statement does not change.

**L1, instance order on contexts and schemes.** `sch_le s' s`: every instance of
`s'` (under the sorts the scheme records) is an instance of `s`; `ctx_le G' G` is
the pointwise order. Two lemmas: `typing_ctx_le` (a derivation under a context of
more general schemes stays a derivation under any instance of it) and `gen_mono`
(generalizing a more specific type over a more specific context gives a scheme
that is no more general, with the recorded sorts carried by `kres`). The `Tm` pin
joins both: `pin_ctx Tm G` is a context with one more binding, so `gen_mono` is
proved for `gen (pin_ctx Tm G)`. This is where the rewritten `T_Let` of stage 7.1
helps: its premise says which variables the pin holds. About 900 lines.

*As built (stage 7.5, `GoatCompleteInst.v`, `GoatCompleteGen.v`,
`GoatCompleteMono.v`, `GoatCompleteLet.v`).* The orientation is the existing
`ctx_more_gen`'s: `sch_le D s s'` reads "`s` is an instance of `s'`" (`s'` is the
more general), and `ctx_le D G G'` is pointwise, same names. Three changes from
the text above.

1. `sch_le` is stated up to the environment on the scheme's *free* variables
   only: every `D'` that agrees with `D` on them gives the same inclusion of
   instances, and the free variables of `s'` are free in `s`. The `let` rule's
   premises live in `ext D V k` and `extr`, so the order has to survive an
   extension on variables the context does not mention (`sch_le_ext`,
   `sch_le_extr`); a plain "every instance in `D`" does not. The containment is
   what the `T_Let` case of `typing_ctx_le` needs: a context of more general
   schemes may not mention a variable the derivation generalizes. It is part of the
   definition, so `ctx_le_ftv` and `ctx_le_frv` are one-liners.
2. `typing_ctx_le` runs from the instance to the more general context (`ctx_le D
   G G'`, `typing D G e T`, so `typing D G' e T`). The plan's sentence ("a
   derivation under more general schemes stays a derivation under an instance")
   has the direction backwards: a variable the derivation instantiates at the
   instance's scheme is instantiated at the more general one, never conversely.
   The proof is `typing_ftv_mono`'s with the instance order in place of
   `sch_more_gen`; `sch_more_gen_le` embeds the old relation, and `gen_more_gen`
   gives the `T_Let` and `T_Letrec` generalizations. The completeness induction
   does not call it (its hypothesis is "the derivation's context is an instance of
   `S1 G`", so each rule is read at that context); it is the statement that makes
   `ctx_le` the right order.
3. `gen_mono` compares the derivation's `gen (pin_ctx Tm Gd) (S2 T') k rk` with
   `apS S2 (gen_ren Dal (pin_ctx Ta Ga) T')`, the algorithm's scheme under the
   substitution the induction carries (`sch_le D` of the first to the second).
   Comparing it to `gen_ren` directly is wrong: the algorithm's quantified
   variables are odd atoms `S2` leaves alone, and the derivation's instance sends
   the odd atom standing for `a` to what it sends `S2 a` to. The hypotheses are
   `OkS S2`, `kres` and `rkres` of `S2` into the environment the derivation's first
   premise lives in (`extr (ext D V k) Vr rk`), `even_ctx Ga`, and `frozen S2 Ga Gd`
   (`S2` sends each free variable of the algorithm's context to a type over the
   derivation's free variables). `T1 = S2 T'` is literal equality: `teq` can
   drop a variable (an absent presence field), which would change which variables
   the derivation generalizes. `gen_mono_let` takes the pin as `let_pin` and
   discharges its half of `frozen` from the derivation's `lit_pinned` premise
   (`let_pin_frozen`: a numeral variable the algorithm pins maps to a `Literal`
   variable the derivation cannot have generalized). The L3 `let` case therefore
   owes `frozen S2 Ga Gd`, which is the induction's "`Gd` is an instance of `S2
   Ga`" read through `ctx_le`.

Sizes: about 1,100 lines in all (`GoatCompleteFuel.v` 148, `GoatCompleteInst.v` 338,
`GoatCompleteGen.v` 180, `GoatCompleteMono.v` 366, `GoatCompleteLet.v` 60), against
the 1,150 estimated.

**L2, the unifier is a most general unifier.** The heart of the proof, split by
what it unifies:

- *Types without rows or `mu`.* If `S1` makes `T1` and `T2` equal, `unify` succeeds
  and returns `s` with `S1 = S2 . s`. The occurs check never rejects when a
  unifier exists, because an image `S1 a` has finite size and `S1 T2`, with `a`
  inside `T2`, is strictly larger. This also shows `unify_k`, which ties a knot
  where `unify_t` fails the occurs check, behaves as `unify_t` whenever a finite
  unifier exists, so statement A needs no knot reasoning. Measure: the pair
  (number of unbound variables, size), as in every classical proof. About 600
  lines.
- *Rows with scoped labels and presence.* `rewrite_row` and `unify_r` must satisfy
  Leijen's two theorems: termination (the side condition that the tail variable of
  the row being rewritten is not in the substitution's domain) and completeness
  (if a unifier makes two rows `req`, `unify_r` finds a more general one). The
  `req` relation is already characterized per label (`GoatRows.v`, used by the
  soundness proof); L2 needs its converse, the inversion that a `req` of two
  `row_Ext` spines rewrites one into the other. A label can occur twice (scoped
  labels stay, section 3 of phase 4's plan), which is why the proof follows
  Leijen's measure (the count of labels not yet matched) and not a structural one.
  Presence adds one rule: a presence type `P` is unified like any type, a closed
  row without the label supplies `Bool`, a row that has it supplies `Unit`. About
  900 lines, the largest single lemma.
- *Sorts.* `unify_sorted` returns the updated kinding environment (the #623
  design, `docs/design/phase6-proof-plan.md` section 2.4, Q3-B): binding a
  variable `a` of sort `k` to `T` replaces each variable of `T` whose sort is
  coarser than the sort `k` forces on it by a fresh variable of the forced sort.
  The completeness half: `sat D1 k (S1 T)` and `kres D D1 S1` give `D'` and `S2`
  with `kres D' D1 S2` and `S2 . s` agreeing with `S1`. The forced sort on a
  position is `Eq` through a record field, a `mu` body and a tag payload, and
  `Numeric` through a record field. About 500 lines, after stage 7.2 and 7.3.

*As built (stage 7.6, `GoatCompleteRows.v`, `GoatCompleteUnify.v`).* The
fragment is base types, variables, arrows and, with `b = true`, records of closed
rows (a spine of `Ext` fields, no tail variable, no presence entry) whose fields
are in the fragment; substitution images are arbitrary. `unify_t_complete`,
`unify_r_complete` and `unify_co_complete` say: if `S` makes two such types (rows)
`teq` (`req`) and respects the sorts (`kres D D1 (sT S)`), then from some fuel on
(`Stable`) the unifier returns an `s` in the fragment through which `S` factors
(`Fac S s`: `teq (S x) (S (s x))` for every `x`). Four adaptations.

1. **No renaming, so `S2 = S`.** Nothing in the fragment makes `push_sort`,
   `push_sort_r` or the fresh row variable of `rewrite_row` run (a sort is pushed
   only onto a record's variables, and a closed row is never rewritten through a
   variable), so the environment and the supply come back unchanged and `S`
   factors through the answer itself. The `S2 . s` of the plan's statement
   appears only when a variable is invented, which is the part that is not
   proved.
2. **The measure is the size of the image, made `teq`-invariant.** `tsz` and `rsz`
   count `Arrow`, `Record` and `Ext` nodes and give an absent presence size zero,
   so `teq` and `req` preserve them (`teq_req_size`, a case per rule). The plan's
   (variables, size) pair is not needed: the second call of the arrow case
   unifies `s1 B` and `s1 B'`, whose image under `S` is `teq` to that of `B`, so
   its size is that of `B`, below the whole.
3. **The `req` inversion is the field-list characterization, by swaps.** For a
   closed spine, equal field lists at every label (`pi`) make two rows `req`
   (`req_of_pi`): the first entry of a label surfaces by `req_swap`
   (`surface_req`), the rest is the induction. This is the converse of
   `req_pres` that `GoatRows.v` leaves open, and it is what cancels the head in
   `unify_r`'s recursion (`req_cancel`). It needs no Leijen-style measure: the
   rows are closed, so the label count falls by one at each step.
4. **Sorts are general for types without records and trivial with them.** For
   `b = false` the sort environment is arbitrary: a sorted variable binds to a
   scalar only if the scalar has the sort (`sat_scalar`), and to an arrow only at
   `Any`, which `kres` forces. With records (`b = true`) every variable must be
   `Any`.

What is not proved, and why. Each item is a fact about the definitions, so it
wants a decision before the proof, not more proof.

- **`sat` is not invariant under `teq`.** `Record {l^Unit : Int}` is `teq` to
  `Record {l : Int}` (`req_pre`) and only the second is `Eq`
  (`sat_not_teq_invariant`). A sorted variable bound to a record then pushes its
  sort onto the field variables, and `S` need not respect the pushed sort on them,
  so `S` does not factor through the answer in `kres`. The sorted-variable-under-a-
  record half of the plan's sort bullet needs `sat` to see through presence, or
  the completeness statement to assume that the images satisfy the sorts up to
  `teq`.
- **`rewrite_row` fails at a row variable that lacks the label**, where `Bool`
  presence (the label is absent from it) would do (`rewrite_row_lacks_gap`).
  `l^p : a | r'` against `m : B | r` with `r` lacking `l` has the unifier
  `p := Bool, r' := m : B, r := {}` and `unify_r` returns `None`. Row-tail
  completeness is false until `rewrite_row` returns `(Bool, a, r, sid)` there.
- **`bind_row`'s occurs check rejects an absent presence.** `r` against
  `l^p : a | r` has the unifier `p := Bool, r := {}` (`req_abs`), and `occR`
  returns `None`.
- **`sat_b` is conservative on `Grp` and `Maybe`**: it is `false` for an `Eq` or
  `Numeric` sort where `sat` can hold, so a sorted variable bound to a tag group
  or to a row with a presence entry is refused. Tag groups are therefore left out
  of the fragment.

Sizes: `GoatCompleteRows.v` 177 lines and `GoatCompleteUnify.v` 498, against the
2,000 estimated for the whole of L2. Left for later stages: rows with a tail
variable and presence entries (`rewrite_row`'s fresh variables, `bind_row`'s
`rk_join`, the invention of `S2` on them), sorts pushed under a record, and the
mu-free tag group.

*As built (stage 7.6b, `GoatSatTeq.v`).* PR 656 listed four gaps and the
architect's ruling is the decision procedure: build the smallest goat program for
each, run the checker on it, and **if the checker accepts it, fix W; if it
rejects it, tighten the calculus**. The differential target compared each program
against the extracted algorithm (`checker/examples/core_corpus.rs` with a source
list in place of the corpus), so "the checker accepts" is the checker's verdict
on the exact program, and "W refuses" is the driver's `w-refuses`. A random search
(four seeds of 3,000 programs, about 2,970 accepted each: functions,
applications, restricts, spreads, `if`, `==`) found the four findings below and
three more. Before the fixes 56 of 2,969 programs of one seed disagreed; after,
2 do, and both are findings 2 and 7.

| # | Finding | Smallest program | Checker | Call |
| --- | --- | --- | --- | --- |
| 1 | `sat` is not `teq`-invariant under an absent presence | `program(w) do t = {...w, x: program(z) do z done}; u = if true then w else {} done; w == w done` | accepts: an `ABSENT` presence is peeled, so the function field is never compared | `sat` reads through presence, in the calculus (`GoatDefs.rsat`) and in W (`rsat_b`); proved `teq`-invariant (`sat_teq`) |
| 2 | `rewrite_row` is `None` at a row variable that lacks the label | `f = program(q) do {...q, x: 1} done; g = program(p) do {x, ...r} = p; f(r) done` | accepts (`unify_row`'s `Maybe` arm: `surface_bounded` finds nothing, so `pres := ABSENT` and the rest unifies) | the ruling says fix W; **not done**, see below |
| 3 | `bind_row`'s occurs check on `r ~ {l^p: a \| r}` | none found | the equation reaches `occurs_row_deep`, then `tie_row_knot` (a recursive row, a driver skip) or "would have to contain itself" | no program needs it; recorded, no change |
| 4 | `sat_b` is `false` on `Maybe` | `program(q) do e = q == q; {...q, x: 1} done` | accepts: the field of an unresolved presence takes the sort, the row is `Eq` | `sat_b` decides the clause finding 1 defines; `sat_b_iff` re-proved |

**Finding 1, and 4 with it.** The calculus said `rsat D k (Maybe l P T R)` only at
`Any`, so `Record {l^Unit: Int}` (`req_pre` equals `Record {l: Int}`) was not
`Eq`. It is now `(P = Bool \/ sat D k T) /\ rsat D k R`: an absent entry is no
field, any other presence (`Unit`, or a variable the checker has not settled)
holds a field the sort reaches. `sat_teq_mut` proves `sat` and `spine_sat` agree
on `teq` types and `rsat` on `req` rows, a case per rule; the `Bool` presence
comparison goes through `teq_Bool_inv`. The change reaches the sort lemmas that
inspect a `Maybe` entry (`sat_finer_mut`, `sat_ap_mut`, `sat_mono_mut`,
`sat_pw_mut`, `sat_loc_mut`, `sat_ext_out_mut`, `sat_open_mut`, `sat_b_iff_mut`,
`rm_sat`), and `row_sig` of record arithmetic, which now has a `Maybe` clause
(`rm_row_sig`, `rm_ext_req` take the `rm_maybe_inv` case). It is the checker's
reading: `constrain_row` constrains the field of every `Maybe` that `resolve_row`
leaves, and `peel` drops an `ABSENT` one. `Numeric` follows `Eq` (the checker has
one `constrain_row`).

**A fifth finding, found by the search: `unify_r` compares the field type of an
absent entry.** `f0 = program(q) do {...q, x: 1}; q done` then
`v3 = f0({y: 1}); {...v3, x: "s"}`: `v3 : {x^Bool: Int | {y: Number}}` meets
`{x^p: String | r}` and W unifies `Int` with `String`. The checker has peeled the
absent entry. `drop_abs` removes an entry whose presence is `Bool` and whose rest
lacks its label (`req_abs`, so the rows stay `req`), and `unify_t` (records) and
`unify_r` (the recursive call, after the substitution made an entry absent) call
it on both rows. `unify_sound` and `unify_t_gsub` carry `req_drop_abs`,
`EvR_drop_abs`, `mgr_drop_abs`; `unify_r_complete` carries `drop_abs_crow` (a closed
row has nothing to drop). `unify_k`/`unify_kr` (the knot unifier) are unchanged: a
recursive-type program with an absent entry stays a driver skip.

**Finding 2, why it is not fixed here.** The program is derivable in the checker
and in no calculus rule: the argument `r : Record r0` (`r0` lacks `x`) must meet
`Record {x^Bool: a | r0}`, and `req_abs` keeps the syntactic `rlacks`, which is
`false` on a row variable (`GoatRows`, stage 7.2: "`req_abs` is unchanged"). So
W returning `(Bool, a, Var r, sid)` at a lacking variable would give a unifier
whose result is not `req` to anything, and `unify_sound` could not state it. The
fix is a conversion that reads `rlacksD D`: a `teqD D` (or two typing rules,
`T_Absent` in both directions, with `rlacksD D l R = true`) used by `T_Conv`, and
`unify_sound` stated in it; every induction on `typing` (progress, preservation,
substitution, `GoatElab`, the cases of W) gains the case. That is a stage of its own
(7.6c) and the ruling's "fix W" cannot be met without it. Stage 7.6c fixes it
another way (below): `rewrite_row_lacks_gap` is gone and the program is in
`HANDWRITTEN`.

**Two more W gaps the search found, same shape (checker accepts, W refuses), not
fixed.**
- *Sorted row tail.* `rewrite_row` is `None` when the variable's sort is finer
  than `Any`. With the finding-1 clause the rewrite can be made: the fresh field
  variable takes the sort and the fresh tail keeps the kind
  (`rsat D' k (Maybe l p a r')` holds for `D' a = k`). `f0 = program(q) do
  {...q, y: true} done; program(w) do e0 = w.x; e1 = w == w; f0(w) done` hits it
  (`w`'s tail is `Eq`, and the call rewrites it to present `y`). Needs
  `rewrite_row_sound` to carry an `upd` of the field variable through `GoodU`.
- *Operand order of a comparison.* `infer` unifies the left operand with the
  sorted result variable, then the right; the checker unifies the operands first
  (`join_operands`) and then requires `Eq` of the joined type. `program(w) do t =
  {...w, x: program(z) do z done}; w == {} done` is accepted by the checker and
  refused by W (the sort reaches `w`'s unresolved `Maybe` before `{}` settles it).
  Arithmetic requires the sort of the left operand first in the checker too, so
  only the comparison order differs.

*As built (stage 7.6c).* The three gaps above are closed; each witness is in
`HANDWRITTEN` and compares with 0 mismatches.

**Finding 2, by refining the row variable instead of converting.** The ruling asked
for a conversion that reads `rlacksD D`. A smaller change does the same work:
`rewrite_row` at a row variable `r` that lacks `l` returns `(Bool, a, r', s, ...)`
with `s = [r := l ^ Bool : a ; r']`, where `r'` is fresh and has the kind of `r`.
The two rows then agree syntactically (`req_refl`), so `unify_sound` keeps its
statement in `req`, and neither `T_Conv`, nor `typing`, nor any induction on it
changes. Two definitions follow the refinement. `rlacksD D l R` now reads an absent
entry (`Bool` presence) for `l` as no field, so `l ^ Bool : a ; r'` still lacks
`l` and `rkok` holds of the new binding (`rlacksD_ap`, `rlacksD_mono` gain the
case); `spread_step_typing_L` no longer goes through `rlacks` and uses `rlacksD_pi`
(a row that lacks a label has no field-carrying entry for it) instead.
`lacks_ok` allows an absent entry for a lacked label for the same reason. The
refinement keeps the checker's answer: the driver prints a `Bool` entry as nothing,
so `r'` is `r` up to renaming. It is also the most general unifier: a `S` that
unifies the rows sends `r` to a row `R` that lacks `l`, and `l ^ Bool : a ; R` is
`req` to `R` by `req_abs`.

The same refinement is needed when the *other* row is the variable. `r` against
`l ^ p : a ; R'` (`unify_r`'s `row_Var` arms, `bind_row`) used to fail `lacks_ok`
before it could ask for `p := Bool`. `bind_row` is now a wrapper: it binds each
presence variable of an entry for a label `r` lacks to `Bool` (`abs_vars`,
`bool_sub`, kept only when the variable's sort admits `Bool`), then pushes the sort
of `r` onto the row variables inside `R` (`push_sort_r`, as `bind_prop` does for a
type), then calls the old definition (`bind_row_core`). `bind_row_sound` and
`bind_row_gsub` keep their statements. The witness is `f = program(q) do {...q, x:
1} done; g = program(p) do {x, ...r} = p; f(r) done`.

**Sorted row tail.** `rewrite_row` at a row variable of any sort binds it to `l ^
p : a ; r'`; the fresh field variable `a` takes the sort of the row variable
(`upd`) and `r'` keeps its kind (`rupd`). `rewrite_row_sound` carries both through
`GoodU` (`Good_upd`, `Good_rupd`, `Good_lift`); the new clause of `rsat` for a
`Maybe` entry is what makes `rkok` hold of the binding.

**Operand order.** A comparison (`is_cmp_op`) unifies the two operands first and
then unifies the left operand's joined type with a fresh variable of sort `Eq`, as
the checker's `join_operands` does; the arithmetic operators keep the sort of the
left operand first. `infer_sound` has a case for it (`sig_cmp`, the coercions of the
two unifications composed on the left operand) and `infer_guarded` one.

*A fourth gap, found by the search: a variable's sort reaches the row variables
inside its row.* `bind_row` pushed the sort onto the type variables of `R` and
not onto its nested row variables, so `f0 = program(q) do e = q == q; {...q, z: 2}
done; program(w) do f0({x: {...w, y: 1}}) done` was refused. It is fixed with the
`push_sort_r` above.

*What stays open.* Four of the ~12,500 accepted programs of the random search (four
seeds, about 3,100 accepted each, `if`, `==`, spreads, restricts, rest patterns,
functions and calls) still disagree, all `w-refuses`, all one shape: an absent
entry against its own tail. After `f0(r0)` binds `r0`'s row to `z ^ Bool : N ; r'`,
a later unification meets `z ^ Bool : N ; r'` and `r'` (the smallest:
`f0 = program(q) do {...q, z: 1} done; program(w) do {z, ...r0} = w; v1 = f0(r0);
if true then w else v1 done done`), or meets two absent entries for one label with
different field types (`f1 = program(q) do {...q, z: "s"} done; f0 = program(q) do
{x, ...r} = q; {...r, z: 1} done; program(v0) do {z, ...r1} = v0; v2 = f1(r1);
f0(r1) done`). The checker peels the absent entry whenever its tail lacks the label.
Neither side can be rewritten to the other: `req_abs` needs the syntactic `rlacks`,
and `bind_row`'s occurs check (finding 3) refuses `r' := z ^ Bool : N ; r'`. This
is the conversion the ruling described (`teqD D`, or `req_abs` reading `rlacksD D`),
and it is not built: the refinement above removes the entry from the rows W builds
at a rewrite, but not from the rows two earlier calls left behind. Finding 3 is
therefore not "no program needs it".

**What L2 gains.** `sat_teq` removes the first of the two definitions that stopped
L2 (sorted variables under a record: a pushed sort now survives any
representative). Rows with tail variables stay out: they need finding 2 (the
rewrite at a lacking variable), the sorted-tail rewrite above, and the invention
of `S2` for `rewrite_row`'s and `bind_row`'s fresh variables. Tag groups stay
out: `sat` on a group is `sat_b`-decidable (stage 7.4) but the fragment's
`Res`/`Fac` need the group's spine in the induction.

*As built (stage 7.6d, `GoatConv.v`).* The residual of stage 7.6c is closed: an
absent entry against its own tail, and two absent entries of one label with
different field types, now unify. The fuzz failure of the 30,000-iteration gate is
fixed as well.

**The fuzz failure.** `g1 = program(p4) do g1(p4) done; {lab0: g1((1 // 1)), lab1:
g1()}` has W accept what the checker rejects (a call with no argument to a function
of one parameter). The gap was the corpus reader, not W and not the calculus: it
writes `f()` as a call of `f` on `unit`, and it compared the checker's rejection with
W's verdict for every program that had only one-parameter functions and calls
(mode `U`). A rejected program carries no node types, so the reader cannot tell
`f()` at the arity of `f` from `f()` that the checker refuses for its arity, and W
reads the unit argument as an ordinary one. A zero-parameter function or call in a
rejected program now clears `unary`, so the driver skips its rejection (mode `N`);
an accepted program is read as before. The nightly fuzz runs to date (the
latest scheduled one is 2026-11-22) list four targets and do not include
`differential_checker_vs_w`, so this failure had not turned the nightly red; the
scheduled runs failed in the `goat_wamr` C build.

**Conversion at the environment.** `nfT D` normalizes a type: inside arrows and
records it drops each `Maybe` entry whose presence is `Bool` and whose normalized
rest `rlacksD D` its label. `teqD D T T'` is `teq (nfT D T) (nfT D T')`, so it holds
of every `teq` pair (`teq_teqD`: `req_abs` is the case of an entry whose rest lacks
the label by syntax, and the swap and presence cases need the order of dropping,
which is inner entry first) and of an absent entry against a tail variable `D` gives
the label to. `T_Conv` is `T_ConvD`, whose premise is `teqD D`; `T_Conv` the lemma
keeps every construction that has a plain `teq`. `mu` and tag groups are opaque to
`nfT`: a binder's body has bound indices that `rlacksD` cannot read, so a recursive
type or a tag payload converts as `teq` does, and the unifier keeps the plain
`unify_t` for a payload. The two choices cost the same corner, an absent entry
inside a tag payload or a recursive type, which stays a driver skip or a refusal
as before.

What the proofs needed is in `GoatConv.v` and the first-field lemmas of `GoatSpread.v`: the relation is an equivalence
containing `teq`; a type's own normal form is `teqD` to it (`nfT_idem`); `sat`, the
operator signatures, `pi`, `rm` and the first field of a record read the same
before and after normalizing (`sat_nf`, `row_sig_nf`, `pi_nf`, `rm_nf`); and the
inversions of `teq` (arrow, record, `mu`, group, a base type) have `teqD` versions
(`teqD_Record_inv`, `teqD_Record_pi`). Canonical forms return the literal's row
equivalent to the normal form of the type's row (`canon_record`); preservation of a
spread, a restrict and a field access normalizes both sides and ends in `req` on
normal forms (`presence_invD`, `spread_step_typing`, `restrict_step_typing`);
the substitution lemma needs `teqD D' (ap T) (ap T')` from `teqD D T T'` under
`rkres D D'` (`teqD_ap`: an entry dropped at `D` is dropped at `D'`, `rlacksD_ap`).

**W.** `unify_tD` and `unify_rD` are `unify_t` and `unify_r` with `nfR D` for the
`drop_abs` of 7.6b and 7.6c, taken at the environment the comparison runs in;
`unify_tD_sound` says the two types are `teqD` at the environment returned, from the
`Good` facts of the steps (`lift_teqD`, `req_via_nfD`, `row_step_reqD`). `unify_coD`
puts the coercions after that conversion (`chainD D cs T T'` is a `teqD D` and then
`chain`); `coerce_typingD` and `chainD_apT` carry it through a substitution, and
`infer` calls `unify_coD` everywhere except where a recursive group or a method
literal meets its slots. Those keep the plain unifier, because a method's type is
related to its slot's by `unroll_eq`, which has no environment. `infer_sound`
and `infer_guarded` are re-proved against `unify_coD`. `drop_abs` and the
completeness results of 7.6 stay stated about `unify_t`, which the algorithm no
longer calls for plain unification; moving them to `unify_tD` is the next step of
the completeness induction.

**Results.** The two programs of the 7.6c residual are in `HANDWRITTEN` and compare
with 0 mismatches; the whole corpus compares 43,358 programs with 0 mismatches. A
fresh random search (seeds 11 to 14, 3,000 programs each, functions, calls,
restricts, rest patterns, spreads, `if`, `==`, projections) compared 11,869 programs
with 0 mismatches, where 7.6c left 4 of about 12,500. The 30,000-iteration fuzz
target passes, and so does a 120,000-iteration run.

**Sort order and an open presence (`checker/tests/absent_field_sort.rs`).** A sort
that reaches a `Maybe` entry whose presence is still a variable constrains the
field, in the checker and in `rsat_b` alike, because the entry may turn out
present; one that arrives after the presence is `ABSENT` finds the entry peeled
and never touches the field. So `program(r) do s = {...r, id: program(v) do v done}; a = r == r; b = r == {k: 1}; 1 done`
is rejected and the same body with `b` first is accepted, and a field type that
took an `Eq` sort while its entry was open keeps it after the entry goes absent.
The verdict is sound (the program that is refused is one the sorts could not
justify at that moment). The checker and the algorithm agree on the record
programs above and on the rejected order of the field-type program; its accepted
order (`f = program(r, x) do s = {...r, id: x}; b = r == {k: 1}; a = r == r; 1 done`,
called with a function for `x`) is a `w-refuses` the algorithm still has, so it
is a checker test and not a corpus program. Making it principal needs a sort held on the presence variable and
discharged when the presence settles, which changes `rsat_b` and `sat_b` and
their soundness lemmas; it is not done.

*As built (stage 7.6e, `GoatCompleteUnify.v`, `GoatCompleteSorts.v`,
`GoatCompleteFuel.v`).* The ratified next step, retargeting L2 to the unifier W
calls, is done; the row-tail half of L2 is not, and what is proved of it is the
invention of the factoring substitution, in pieces.

**Retarget.** `unify_tD_mono`/`unify_rD_mono` (`unifyD_mono_pair`: the group arm
hands the payload to the plain unifier, so it leans on `unify_t_mono`),
`unify_tD_stable`, `unify_rD_stable` and `unify_coD_stable` replace
`unify_co_stable`. `unify_tD_complete`, `unify_rD_complete` and
`unify_coD_complete` assume `teqD D1 (S T1) (S T2)` (`reqD D1` for rows) and
conclude `FacD D1 S s`: `teqD D1 (S x) (S (s x))`. They come from the 7.6
induction by one substitution rather than a second induction: `nfS D1 S` sends `x`
to `nfT D1 (S x)`, and on a type of the fragment `nfT D1 (S T)` is `nfS D1 S`
applied to `T` (`nf_ap`; a fragment type is its own normal form, `nf_cp`), so
`teqD D1` of the images is `teq` of `nfS`'s images, `kres` transfers by `sat_nf`,
and `FacD` is `Fac` of `nfS`. The induction itself changed in the names
(`unify_tD`, `unify_rD`) and in `nfR D` for `drop_abs`, which is the identity on
a closed row of the fragment.

**Adaptation: tag groups stay out.** A group's payload is compared by `unify_t`
and by plain `teq` (`nfT` does not go inside a group, 7.6d), so the group arm of
`unify_tD` needs completeness of the plain unifier on the payload and a
`teq`-hypothesis on it. The `nfS` step above breaks there: `nfT D1 (S (Grp w A))`
is `Grp w (S A)` with `S A` not normalized, which is not `Grp w (nfS .. A)`, so
`FacD` does not follow from `Fac` of `nfS`. The two ways out both cost a second
induction (state L2 for `unify_t` and `unify_tD` together, or prove `unify_tD`
and `unify_t` agree on the fragment, which needs every run to preserve it). The
cost is not the group: `tsz` would count a payload and `cp` gain one clause.

**What is proved of the invention.** `GoatCompleteSorts.v` (283 lines) has the
extension `S2` for each place W makes a fresh variable, each stated on its own,
with the supply and environment facts the induction will thread.

- `push_sort_complete` and `push_sort_r_complete`: if each variable `push_sort`
  renames has an image of the pushed sort (`sat D1 k (S b)`, `rsat D1 k (S q)`),
  then `S2` (the image of the variable on the fresh one) respects the extended
  environment (`KR D' D1 S2`), keeps the other component, and composes with the
  renaming to give `S` back on the atoms below the supply. This is the part of
  "sorts pushed under records" that needs invention; the reading of the sort off
  `S a`'s image is `sat_teq` (7.6b), which the caller applies.
- `rewrite_row_var_complete`: if `S r` is `req` to `l ^ P0 : T0 ; R0` and the
  variable is not in the guard `av`, `rewrite_row` at `Var r` succeeds in both of
  its branches (the variable lacks `l`, or does not), and `S2` sends the fresh
  presence, field and tail to `P0`, `T0`, `R0`. The row kinding is `rkok_req` and
  `rkok_maybe_tail`/`rkok_maybe_abs` (a row of a kind has a tail of the kind; a
  label the kind lacks has an absent entry); `rlacksD` is what makes the lacking
  branch go through.
- `bind_row_tail_complete` and `rk_join_ok`: `S2` for the fresh variable at the
  tail of the row `bind_row_core` binds, which has the join of two kinds.

**DECISION NEEDED: the sort of an absent field.** `rewrite_row_var_complete`
carries one hypothesis (`Hfield`) that the sort of the row variable does not give.
At a row variable that does not lack `l`, the fresh field variable takes the sort
of the row variable; the declarative `rsat` leaves an absent entry
(`l ^ Bool : T0`) unconstrained. A substitution that sends the presence to `Bool`
and the field to a function, under a row variable of sort `Eq`, is a unifier the
calculus admits and no W run factors through (the fresh field variable is `Eq`
and `S2` would have to send it to a function). W agrees with the checker here
(it constrains the field of a presence it has not resolved, and peels one it has),
so this is the checker's order-dependence against the calculus's, not a W bug:
the options are to state statement A with the corner excluded (a hypothesis on
the derivation's substitution), or to make `rsat` constrain the field of every
entry. Not run against the checker; the corner is read off the definitions.

**Not done, and where it stops.** Each is a gap in a different lemma.

1. *Req inversion for rows with a tail.* `rewrite_row_var_complete` takes `req (S
   r) (l ^ P0 : T0 ; R0)` as given. The induction needs it from `req (S R1) (S
   R2)`, which is the cancellation `req (l : A ; X) (l : B ; Y)` gives `teq A B`
   and `req X Y` for rows with a tail and presence entries. For a closed spine it
   is `req_cancel` (field lists, `req_of_pi`). With a tail variable, and with
   presence variables, the field-list characterization is not enough (`l ^ p : a`
   and `l ^ q : b` have equal field lists and are not `req`), so it needs a normal
   form for rows and `req`'s soundness and completeness against it. This is the
   Leijen rewriting lemma, and it is the largest missing piece (the plan's 900
   lines were for it).
2. *Leijen's side condition.* `unify_r` refuses `rewrite_row` when the tail of the
   second row is in `frv_row R1` (any row variable of the first, nested ones too).
   Completeness has to show that when a unifier exists the tail is not there, by a
   size argument on `S` (the label count falls by one only if `S r` cannot contain
   the row it is bound inside). `rewrite_row_var_complete` assumes the guard.
3. *`bind_row` end to end.* `abs_vars`/`bool_sub` (an entry for a lacked label
   has presence `Bool` under `S`), the second occurs check on the renamed row, and
   `lacks_ok`; `bind_row_tail_complete` is only the fresh tail.
4. *The induction with `S2`.* The statement threads `(D', n', S2)` through each
   call, with the freshness of the atoms of the types and of `S`'s images, and the
   `Res`/`Fac` composition (`Fac` carried from `S` to `S2` by the factoring
   lemmas above). Nothing here is hard, and none of it is written.
5. *`bind_prop` with sorts.* The assembly of `push_sort_complete` into a
   `bind_prop` completeness (the sort reaches every variable of a type that
   satisfies it, `sat` back to the renamed type, the occurs check after renaming)
   is what removes the `b = true` restriction (every sort `Any`) from the
   records of the fragment.
6. *Tag groups, `mu`, methods* (above, and statement B).

*As built (stage 7.6f, `GoatRowNf.v`, `GoatCompleteSide.v`).* Item 1 is done.
Item 2 is refuted as stated, and the refutation changes what items 3 to 5 can
claim. Items 3 to 6 are not started: the induction needs W's guards settled
first (below).

**Item 1: the row normal form (`GoatRowNf.v`, about 400 lines).** `raw l R` is
the list of entries of label `l` in `R`, each a (presence, field type) pair, a
plain field having presence `Unit`. `ents l R` is `raw l R` with the absent
entries at the end of the list dropped when the tail is closed (`rtail R` is
`row_Empty`): `req_abs` drops an absent entry exactly when nothing of its label
follows it and the tail is closed, so the trailing run goes, and an open tail
keeps every entry. `req_iff_nf` says `req R1 R2` iff `rtail R1 = rtail R2` and,
at every label, `Forall2 ent_eq (ents l R1) (ents l R2)` (`ent_eq`: `teq` on the
presence and on the field type).

- *Soundness* (`req_nf`) is an induction on `req` in the style of `req_pres`,
  carried by `cons_t` (the list after putting an entry in front, which drops it
  again if it is absent and last under a closed tail).
- *Completeness* normalizes both rows (`nf_exists`: each row is `req` to one whose
  `raw` lists are its `ents`, by dropping the absent entries `req_abs` allows) and
  then compares rows with no droppable entry entry by entry (`req_of_raw`) by
  surfacing the first entry of a label (`extract_req`, with `req_swap_em`,
  `req_swap_mm`, `req_pre`). This is the swap-congruence obligation the 7.1 plan
  left out, with presence entries and a tail variable.
- *Cancellation* (`row_cancel`): `req (l ^ P : A ; X) (l ^ Q : B ; Y)` gives `req
  X Y` and either `teq P Q` and `teq A B`, or both presences are `Bool`. The
  second disjunct is not slack: `l ^ Bool : Int ; {}` and `l ^ Bool : String ; {}`
  are both `req` to `{}`, so an absent field's type carries no information (the
  reason `unify_rD` drops absent entries before comparing, 7.6c). `row_cancel_ext`
  (plain fields: `teq A B`, `req X Y`) and `row_cancel_mixed` (a presence entry
  against a plain field: the presence is `Unit`) follow. The theory has no
  hypothesis on the tail or on the presences, so it covers a tail variable and
  presence variables (rigid: `req` has no substitution).

**Item 2: Leijen's side condition does not hold of the checker's `av`.**
`rewrite_row` refuses the tail variable of the second row when it is in
`frv_row R1`, every row variable of the first row. `leijen_tail` proves the
original condition: when both rows end in the same variable, the second has no
entry of `l`, and the first has a present one, no substitution makes them `req`
(`cnt`, the number of present entries of a label, is `req`-invariant, `raw_ap`
says a substitution adds the same entries to both through the common tail, and
the first has one more). Two unifiable pairs `unify_rD` refuses show the guard is
wider than that, both proved by `unify_rD ... = None` and an explicit `req` of the
images:

- `side_blocks_nested`: `{l0: Int, l1: {...r}}` against `{l1: c, ...r}`, unified
  by `r := {l0: Int}`, `c := {l0: Int}`. The variable occurs in a field type of
  the first row, not in its tail, and there is no cycle. (The first row's head is
  `l0`, the second has no `l0`, and its tail is in `frv_row R1`.)
- `side_blocks_absent`: `{l0^p: Int, ...r}` against `{l1^q: Int, ...r}`, unified
  by `p := Bool`, `q := Bool`, `r := {}`: the substituted rows are both `{}`.

So "the side condition never blocks a unifiable pair" is false of W. The size
argument works for a present head and a common tail (`leijen_tail`) and fails for
a nested occurrence and for a head whose presence a unifier makes absent.

**Item 3: the occurs checks have the same shape.** `bind_row_blocks_absent_tail`:
`r` against `{l0^p: Int, ...r}` is unified by `p := Bool`, `r := {}`, and
`bind_row`'s first `occR` check refuses it. `bind_prop_blocks_absent`: `a` against
`{l0^Bool: a}` is unified by `a := {}`, and `bind_prop` refuses it (`unify_tD`
normalizes a record only against a record, so the type `bind_prop` gets is not in
normal form). These are the occurs check reading a variable inside an absent entry
as an occurrence, where the calculus reads the entry as no field.

**DECISION NEEDED: what does completeness of the unifier claim for rows with
absent entries?** Statement A's induction (item 4) needs, at each `rewrite_row`
and `bind_row`, that the guard passes when `S` unifies. The four theorems above
say it does not, in two ways. Options:
  (a) Change W so the guards read the normal form: `rewrite_row`'s `av` becomes
      `{row_tail R1}` when the first entry is present (the original Leijen
      condition, which `leijen_tail` justifies), and the occurs checks in
      `bind_row`/`bind_prop` run on `nfT`/`nfR` of the bound type, so an
      absent entry is not an occurrence. W is the proof's model of the checker, so
      the Rust checker takes the same change (or is shown to agree), and the
      differential and soundness proofs are redone for the new guards. This keeps
      statement A as written. I recommend it.
  (b) State statement A for derivations whose rows meet neither shape: a
      hypothesis on the unifier `S` that no absent entry of the problem has a
      variable of the problem behind it. It keeps W and the checker and weakens
      the theorem by a premise no program can be checked against.
  What I chose: neither is in this PR; the four theorems record the gap, and
  items 3 to 5 wait on the owner's choice, because (a) changes `GoatInfer.v` and
  the soundness lemmas that name `rewrite_row`'s `av` (`rewrite_row_sound`).
  Whether the Rust checker is blocked on the same pairs is not run; the shapes
  need a presence variable that a later constraint makes `Bool`, and the checker
  peels absent entries as it goes (`peel`), which may bind them before the
  guard sees them. #667 is the place to find out.

**Not started: items 3 to 6.** With the guards in question the induction with
`(D', n', S2)` would be proved for the wrong statement. The pieces that do not
depend on the choice are in `GoatCompleteSorts.v` (the invention) and now
`GoatRowNf.v` (the cancellation `rewrite_row_var_complete` takes as a hypothesis:
`row_cancel` gives it, from `req (S R1) (S R2)` once the first row's front entry
is surfaced).

*As built (stage 7.6g, `GoatCompleteBind.v`, `GoatCompleteSide.v`, `GoatInfer.v`).*
The triage the 7.6f ruling asked for is done, one of the four pairs moved W, and
item 5 is proved for plain types. Items 3, 4 and 6 are not started.

**Triage: the four blocked pairs run as goat programs.** Each row says what
`goat check` does and what the extracted W does on the program.

| pair | program | checker | W (before) | decision |
|---|---|---|---|---|
| `side_blocks_nested` | `program(u) do {b, ...w} = u; v = {a: 1, b: w}; if true then v else u done done` | accepts, `({b: {a: Number}, a: Number}) -> ...` | refuses (`w-refuses` mismatch) | option (a), done |
| `side_blocks_absent` | none found | not reached | refuses | option (b) |
| `bind_row_blocks_absent_tail` | none found | not reached | refuses | option (b) |
| `bind_prop_blocks_absent` | none found | not reached | refuses | option (b) |

The nested pair is `{a: Int, b: {...r}}` against `{b: c, ...r}`, reached by a
rest pattern (`w` has the row `r`, the tail of `u`) and a record that puts `w` in
a field. The checker's own probe (a temporary `eprintln!` in `unify_row`, not
committed) printed exactly that pair, and the two-parameter and one-parameter
forms of the program are now in `HANDWRITTEN`.

For the other three, every route a program has to a presence variable goes
through a spread (`{...p, a: v}` gives `p` the row `{a ^ pres: type of v, ...r}`)
or a rest pattern, and each such variable's row tail is fresh at the point the
entry is made. A common tail with two different fronts then needs a unification
that binds it, and the binding resolves the presence (to present, or by the
checker's `peel`) before the pair can be formed. I tried about fifteen programs
(spreads of two parameters then merged, spreads then rest patterns, a spread
whose new field is the record itself) and instrumented the checker over the
51,587-program corpus plus those: no program formed a blocked pair of the
second, third or fourth kind. What the instrumentation did find were programs
with infinite types (`g2 = program(p) do {lab0: p, lab1: g2(p)} done`) where the
guard's shape appears and the checker refuses for the infinite type, which is
no evidence against W. The checker also has no guard to compare against in
these three: where a variable occurs behind an entry, it ties a recursive type
(`{...s, next: s}`) or refuses (`this record would have to contain itself`).
So there is no verdict to post to #667 for them. They stay as hypotheses in
statement A (option (b)), and the corpus search is the place to look again.

**Option (a), the guard.** `side_av R1` (`GoatInfer.v`) is the tail variable of
the first row and nothing else; the four call sites of `rewrite_row` in
`unify_t`/`unify_r` and their copies in the guard, knot and soundness files read
it in place of `frv_row R1`. Every lemma about `rewrite_row` is generic in `av`
(`rewrite_row_sound`, `rewrite_row_gsub`, `rewrite_row_mg` all quantify over it),
so the soundness proofs needed no change beyond the name. The differential
compares the same 50,158 programs with 0 mismatches, so no program the checker
refuses is now accepted by W. A first-row front with a variable presence takes
the same `av`; if its presence is made absent the pair is the second one above,
and a run that does not resolve it recurses until the fuel runs out.

`GoatCompleteSide.v`: `side_blocks_nested` is replaced by `nested_sub_unifies`
(the unifier) and `side_passes_nested` (`rewrite_row` does not meet the guard);
`rewrite_row_total` says `rewrite_row` fails only at the guard; and
`side_guard_passes` is the completeness of the guard: if `S` unifies two rows and
the first starts with an entry `S` makes present (`teq (S P) Unit`), then
`rewrite_row l (side_av R1) D R2 n <> None`, by `leijen_tail` when the tails
agree. The hypothesis on the front entry is the option (b) hypothesis, and it is
all the statement needs of the second pair.

**Item 5: `bind_prop` with sorts (`GoatCompleteBind.v`).**
`bind_prop_sorted_complete`: if `S` unifies `a` and `T`, `T` is plain (`pf`: no
recursive type, group or index), the atoms of `a` and `T` are below the supply,
`a` is not in `T`, and `T` is locally closed, then `bind_prop D a T n` succeeds
and the extension `S2` of `S` to the fresh variables respects the new
environment (`KR D' D1 S2`), `S x` is `teq` to `S2 (s x)` for every old type
variable, and `S r` is `S2 (s r)` for every old row variable. Parts:

- `push_sort_facts`, `push_sort_r_facts`, `push_sort_dok`, `push_sort_r_dok`:
  what the two renamings leave behind (they send a variable to a variable, a row
  variable to a row variable, the fresh ones are at or above the supply, the sorts
  of old atoms are unchanged, and every renamed variable's image has the sort).
- `sat_reach_mut`: the sort reaches the variables of a type that satisfies it, so
  `push_sort_complete` and `push_sort_r_complete` get their sort hypotheses.
- `sat_ren_mut`: a plain type whose variables are sent to variables of the finer
  sort satisfies the sort when its image does, which is how `sat_b` on the
  renamed type succeeds. Both lemmas take the field condition `fld`.
- `lcb_ap_var`, `ftv_ren`: the occurs check after the renaming.

**The field condition (`fld`), a second form of the #667 corner.** For every
entry `l ^ P : F` of `T`: if `S` makes `P` absent then the image of `F` satisfies
the sort, and the image of `P` satisfies it. The first half is the `Hfield`
hypothesis of `rewrite_row_var_complete` at `bind_prop`: `rsat` leaves the field
of an absent entry unconstrained and `sat_b` checks it, so an `S` that makes the
entry absent over a function field, under `Eq`, unifies a pair `bind_prop`
refuses. The second half is new and comes from the presence variable being in
`ftv T`: `push_sort` renames it to a variable of the sort, whose image `Unit`
does not satisfy `Numeric`. The calculus has no arithmetic on records (the
corpus skips them: "arithmetic on non-primitive operands"), and `Eq` holds of
`Unit` and `Bool`, so the second half is automatic for `Any` and `Eq`. Both
halves stay hypotheses of statement A until #667 settles the first.

**Not done.**
3. *`bind_row` end to end.* The pieces: `abs_vars`/`bool_sub` (an entry for a
   lacked label has presence `Bool` under `S`, from `rlacksD` of `S r`, so `S`
   factors through `bool_sub`), one `push_sort_r` on the row, the tail renaming
   (`bind_row_tail_complete`, done), one `push_sort` on the field variables, and
   three occurs checks. The same machinery as `bind_prop_sorted_complete` carries
   it: the composite renaming, `sat_ren_mut` on the row, and the agreement
   lemma. The occurs checks are the third and fourth blocked pairs: a row whose
   tail is `r` itself and whose entries are all absent unifies and is refused, so
   the lemma takes the option (b) hypothesis (the row has a present entry, or `r`
   is not its tail).
4. *The induction with `S2`*, and the `unify_tD`/`unify_rD` completeness it
   threads through `row_cancel` and `GoatCompleteSorts.v`. Nothing in the
   plan changed here: `unify_complete_aux` is stated for closed rows and every
   sort `Any`, and carrying `(D', n', S2)` through each call is the largest step
   left. It needs items 3 and 5 as lemmas, which is why they come first.
6. *Groups outside `mu`.*

*As built (stage 7.6h, `GoatCompleteBindRow.v`, `GoatCompleteSide.v`).* Item 3 is
done. Items 4 and 6 are not started, and L2 is not closed. This stage measured the
guard's cost, proved `bind_row` end to end, and found one more pair W refuses.

**The `side_av` guard's cost.** Stage 7.6g's guard recurses until the fuel runs
out where the old one blocked, so the differential's W run was measured on the
same 51,590-program corpus before and after (the extracted `driver` alone, one
core each, run side by side on one machine; the 7.6f tree is the "before").

| tree | `driver corpus.tsv`, wall (user) |
|---|---|
| 7.6f (before the guard moved) | 365.5 s (357.6 s) |
| 7.6g (`side_av`) | 369.1 s (361.0 s) |

The guard costs 1.0% (user time 1.0%), well under the 25% bar, so no early exit
is added. (The nested-occurrence program is the one mismatch on the 7.6f tree, as
expected; the 7.6g tree compares all 50,161 programs with 0 mismatches. The two
extra full runs on one machine at once gave 369 s and 366 s against 358 s on the
7.6g tree alone while it shared the machine with a Rocq build, so the noise is
larger than the difference.) The driver dominates the differential's wall time:
about 6 minutes of the 6.4 minutes the whole `make differential` takes.

**Item 3: `bind_row` (`GoatCompleteBindRow.v`, about 700 lines).**
`bind_row_sorted_complete`: if `Sg` respects the environments (`KR D DT Sg`) and
unifies `r` with `R` (`req (sR Sg r) (apR Sg R)`), then `bind_row D r R n`
succeeds, and the extension `S2` of `Sg` to its fresh variables respects the new
environment (`KR D' DT S2`), `DOk D' n'` holds, and `Sg` factors through the
result: `teq (sT Sg x) (apT S2 (sT s x))` and `req (sR Sg q) (apR S2 (sR s q))`
for every atom `x` and `q` below the supply. The steps have a lemma each, in the
order the algorithm runs them:

- *`bool_sub`/`abs_vars`.* An entry of `R` for a label `r` lacks has presence
  `Bool` under `Sg` (`abs_vars_bool`, from `rlacksD` of `Sg r` read through
  `req_rlacksD`), so `sat_b D (D p) Bool` holds for each presence variable
  (`KR` gives `sat` of the image) and `Sg` factors through `bool_sub`
  (`bool_sub_agree`). After the substitution every entry of a lacked label is
  absent (`lacks_ok_bs`), whether its presence was a variable or `Bool`.
- *`bind_row_mid_complete`.* One `push_sort_r` on the row variables of the
  result, completed by `push_sort_r_complete` with the reach from `sat_reach_mut`
  (row part). `push_sort_r_new` records where a renamed variable goes (to itself
  or to a fresh atom below the new supply), which the later agreement needs.
- *`bind_row_core_complete`.* The tail is renamed to a fresh variable of the join
  of the two kinds. `bind_row_tail_ext` is `bind_row_tail_complete` with the
  extension spelled out (`sT` unchanged, the fresh variable gets `Sg q`, the old
  row variables keep their images), because the composite needs those equations.
- *`bind_row_fin_complete`.* One `push_sort` on the type variables of the
  fields, then `rsat_b` on the renamed row (`sat_ren_mut`, row part) and
  `lacks_ok` (preserved by a renaming of variables, `lacks_ok_vren`).

The field condition travels across the three renamings by `fld_pull`: a
substitution `u` that `S'` after `u` agrees with `S` on keeps `frld` (the
equations `apT S' (apT u X) = apT S X` come from `ap_agree`).

**Hypotheses of `bind_row_sorted_complete`.** The atoms of `R` are below the
supply, `R` is plain (`prf`), locally closed, and `frld` holds at the sort of
`r`'s kind (the #667 corner, as in `bind_prop_sorted_complete`). The two
occurs-check pairs of the 7.6f ruling (`bind_row_blocks_absent_tail` and the
nested occurrence behind an absent entry) are one hypothesis: `r` is not in
`frv_row R`. It also excludes an occurrence under a *present* entry, which no
unifier admits (`leijen_tail` for the tail; for a field, the `tsz_occ` argument
of the closed fragment); that size argument is not proved for rows with
variables, so the hypothesis is stronger than the ratified one by exactly those
cases, and statement A will need the lemma that discharges them. Adaptation:
the sort condition on the row variables of `R` (`finer (rk_sort (drk D q))
(rk_sort (drk D r))`) is not a hypothesis of the theorem. `push_sort_r`
establishes it (`push_sort_r_facts`), and it is a hypothesis only of
`bind_row_core_complete` and `bind_row_fin_complete`, which run after it.

**One more pair W refuses: `field_blocks_absent`.** `l0^p: Int` against
`l0^q: String` is unified by `p := Bool` and `q := Bool` (both rows are the empty
row), and `unify_rD` returns `None` for every fuel: it pairs the two entries,
unifies the presences, and then compares the field types. `row_cancel` says an
absent field's type carries no information, so this is the second disjunct of the
cancellation, and it is a fourth member of the option (b) family (the first three
are `side_blocks_absent`, `bind_row_blocks_absent_tail` and
`bind_prop_blocks_absent`). It is not run against the checker: reaching it needs
two presence variables of one label compared before a later constraint makes both
absent, and the corpus search of stage 7.6g found no program that makes one
absent after the comparison. DECISION NEEDED, same shape as the 7.6f ruling:
statement A takes a hypothesis that no two compared entries are absent under the
unifier with different field images, or W compares the field types only when the
presences are not both unresolved. Chosen here: the hypothesis (option (b)); no
change to W.

**What remains of 7.6** (as of 7.6h; stage 7.6i below supersedes it).

1. *`rewrite_row` for a whole second row.* `rewrite_row_var_complete` is the
   leaf at a row variable. The closed leaf (a row with no entry of the label
   gets presence `Bool`), the steps at an `Ext` and a `Maybe` entry, and the
   guard at the tail variable remain: surfacing the entry through the spine with
   `extract_req` and the swap lemmas, and carrying `S2` through the recursion
   (the first `S2` from `rewrite_row_var_complete`, the entries in front read
   back through it).
2. *Conversion at the environment in the induction.* The recursive calls of
   `unify_rD` run on `nfR D2` of the substituted rows, and the hypothesis at a
   call is `reqD D1` of the images, so the induction needs `nfR D1 (apR Sg (nfR D
   R)) = nfR D1 (apR Sg R)` (an entry `nfR D` drops is dropped by `nfR D1`
   after `Sg`, from `KR`). `bind_row_sorted_complete` takes plain `req`, which
   `reqD` does not give for a bare variable against a row; the induction states
   its entry hypothesis as plain `teq`/`req` (what a derivation has) and carries
   the normal form as an invariant.
3. *The induction (item 4).* `unify_complete_aux` for rows with variables and
   presence entries, with `(D', n', S2)` threaded: the atoms of both types and of
   the images of `Sg` below the supply, a measure that does not fall at an absent
   entry (`rsz` counts none, so a lexicographic measure with the entry count),
   `Stable` fuel, and the four arms of `unify_rD` (`bind_row` on either side, the
   rewrite). The leaves are `bind_prop_sorted_complete`, `bind_row_sorted_complete`
   and item 1.
4. *Groups outside `mu` (item 6).* The group arm of `unify_tD` hands the
   payload to the plain `unify_t`, so it needs the plain unifier's completeness
   beside the environment-reading one (the 7.6e adaptation).
5. *The occurrence under a present entry,* above, and the hypotheses of statement
   A: the four pairs, `fld`, and the presence variable at `Numeric`.

*As built (stage 7.6i, `GoatCompleteRewrite.v`, `core_corpus.rs`).* Item 1 of the
7.6h list is done and `field_blocks_absent` is triaged. The unifier induction
(items 3 and 4) is not started, and L2 is not closed.

**Triage: `field_blocks_absent` run as a goat program.** The pair is
`l0^p: Int` against `l0^q: String` with both presences unresolved when the two
entries are compared. Two spreads give the entries (`{...p, a: 1}` puts
`a ^ pres: Number` in the row of `p`), and `if true then p else q done` unifies
the two rows.

| program | checker | W |
|---|---|---|
| `program(p, q) do {...p, a: 1}; {...q, a: "x"}; if true then p else q done done` (statements on separate lines) | refuses: `type mismatch: expected Number, found String` at `q` | refuses (the field types differ) |
| the same with `a: 2` | accepts, `({a: Number \| t5}, {a: Number \| t5}) -> {a: Number \| t5}` | accepts |

The checker compares the field types of two fronts unconditionally: the `Maybe`
arm of `unify_row` (`checker/src/infer.rs`) calls `unify_presence`, then
`unify_ty` on the fields, then recurses. A later constraint cannot make the
presences absent before a comparison that has already run, and `peel` drops an
entry only when its presence is already absent when the row is read. So the
checker refuses every program that forms the pair, and the verdict is the
option (b) one: no program reaches the pair with the checker accepting, W is
unchanged, and statement A keeps a hypothesis excluding it. Both programs are in
`HANDWRITTEN` (50,161 programs compared, 0 mismatches).

*Update (2026-11-24, #667 step 3).* Both programs above now check in the checker
and in W when the field types clash: the `a: 1` against `a: "x"` program is
accepted, in either order of the spreads and either order against a statement
that settles the presence. W decides the two entries absent (`absent_clash`) when
the field types clash by shape and both rests lack the label, and its spread
declares the lack on its tail. `field_blocks_absent` is the pair W still unifies,
two variable field types; the hypothesis of statement A stays for it.

*Update (2026-11-24, #667 held equations).* W now holds the spread's equations,
re-holds them at each use of a scheme, and generalizes a `let` under a parameter's
row when the presences it holds end absent (`absent_req`, `V_let_own`); the
differential has no mismatch left on the held-equation corpus programs. What
stays open is the case where such a presence ends present and a variable the
equation does not mention needs two types, and a program mixing two such `let`s
whose presences end differently (`proofs/README.md`, "Held equations", step 5).

**Item 1: `rewrite_row` on a whole second row (`GoatCompleteRewrite.v`).**
`rewrite_row_spec` quantifies over the row: if `Sg` respects the environments
(`KR D D1 Sg`), the atoms of `R` are below the supply, `Sg R` can present `l`
(`Surf l (apR Sg R)`) and `rewrite_row l av D R n = Some (P', T', R', s0, D0,
n1)`, then there is an `S2` with `KR D0 D1 S2`, `n <= n1`, `DOk D0 n1`, `Sg`
factoring through `s0` (`teq` on type atoms, `req` on row atoms below the
supply), and the invariant `req (apR Sg R) (l ^ S2 P' : S2 T' ; S2 R')`. The
caller reads presence, field and rest off the invariant with `row_cancel`
(`rewrite_row_front`). Design points:

- *The invariant, not a target.* Stating the result as an equation to a given
  `l ^ P0 : T0 ; R0` would need the entry surfaced through every skipped entry
  with `extract_req` and a swap lemma per constructor, and would break at a
  closed tail where `req_abs` drops absent entries. The invariant carries the
  entry in front at every step: the `Ext` and `Maybe` steps are `req_head` or
  `req_maybe` (the skipped entry's type converts by `ap_factor`) followed by
  `req_swap_em` or `req_swap_mm`; the found entry is `req_pre` or `req_refl`;
  the closed end is `req_abs`.
- *`Surf`.* `Surf l Q` (`Q` is `req` to some `l ^ P : T ; R0`) holds exactly when
  `raw l Q <> nil` or the tail is `row_Empty` (`Surf_iff`, from `req_nf`,
  `extract_req` and `rlacks_iff`), so an entry for another label passes it down
  (`Surf_ext`, `Surf_maybe`). Only the row-variable leaf uses it, to get the
  `req (sR Sg r) (l ^ P0 : T0 ; R0)` that `rewrite_row_var_complete` needs.
- *The guard is a separate fact.* `rewrite_row_spec` takes success as a
  hypothesis; `side_guard_passes` (7.6g) supplies it. `rewrite_row_complete`
  combines them for the call `unify_rD` makes: given `Sg` unifying `R1` and `R2`
  and a front entry of `R1` that `Sg` makes present, the rewrite of `R2` at
  `side_av R1` succeeds, presence and field of the rewritten entry equal `Sg`'s
  image of the front entry up to `teq` (the absent-pair alternative of
  `row_cancel` is contradicted by the present front), and the rests are `req`.
- *Field condition at the tail.* The one hypothesis beyond the unifier's: at the
  tail variable `r`, for each presentation `l ^ P1 : T1` of `Sg r`, if `r` does
  not lack `l` and `P1` is `Bool` then `T1` satisfies the sort of `r`. This is the
  `Hfield` corner of `rewrite_row_var_complete`, the same #667 shape as `fld`.
- `ap_cong_on`: substitutions that agree up to conversion on the atoms of a type
  give converted images (the factoring of a skipped entry's type; also what the
  induction's composite factoring needs).

**Item 2: the conversion at the environment.** The commutation the 7.6h list
asks for holds up to `req` and is already an instance of `teqD_ap_nf_mut`
(`nfR_ap_nfR`: `req (nfR D1 (apR Sg (nfR D R))) (nfR D1 (apR Sg R))`); the
induction states its hypothesis as `reqD D1` of the images and does not need
syntactic equality. What does not follow is the plain `req (sR Sg r) (apR Sg R)`
that `bind_row_sorted_complete` takes: `reqD D1` of a bare variable's image
against a row is `req` only after `nfR D1` on both sides, and `nfR D1 (sR Sg r)`
need not equal `sR Sg r`. Two ways to close it, neither done: state
`bind_row_sorted_complete` at `reqD D1` with its factoring conclusion at `reqD
D1` (the shape `FacD` has in the closed fragment), or replace `Sg` by a
substitution whose row images are `nfR D1` of `Sg`'s (`nfS` normalizes the type
images only) and show it still respects the environments.

**What remains of 7.6** (as of 7.6i; stage 7.6j below supersedes it).

1. *The induction.* `unify_tD`/`unify_rD` complete for mu-free types and rows
   with variables and presence entries, with `(D', n', S2)` threaded. Leaves,
   all proved: `bind_prop_sorted_complete`, `bind_row_sorted_complete` (modulo
   item 2 above), `rewrite_row_complete`, `row_cancel`, and
   `push_sort_complete`. To do: the invariant over the atoms (both types and the
   images of `Sg` below the supply, `old`), a measure that does not fall at an
   absent entry (`rsz` counts none, so a lexicographic measure with the entry
   count), `Stable` fuel (GoatCompleteFuel.v), and the four arms of `unify_rD`
   (`bind_row` on either side, `Empty` against `Maybe` by the swap, the
   rewrite). The arm after the rewrite recurses on the rests with `S2 ∘ s1 ∘ sp ∘
   s0` threaded, so each recursive call needs `KR`, the atoms and the entry
   hypothesis for the new substitution (`ap_factor` and `ap_agree`).
2. *Groups outside `mu`.* The group arm of `unify_tD` hands its payload to the
   plain `unify_t`, so it needs the plain unifier's completeness beside the
   environment-reading one (the 7.6e adaptation).
3. *The occurrence under a present entry.* `bind_row_sorted_complete` assumes
   `r` is not in `frv_row R`, stronger than the ratified hypothesis by the cases
   no unifier admits (`leijen_tail` for the tail; a field needs the `tsz_occ`
   size argument extended to rows with variables). Statement A needs the lemma
   that discharges them.

**Statement A's hypotheses, as they stand.**

- *The four absent-entry pairs (option (b), ratified).* A unifier `Sg` of the two
  rows never (i) makes the front entry of `R1` absent through a presence
  variable while the tails of `R1` and `R2` share a variable the guard then
  blocks (`side_blocks_absent`; the proved `side_guard_passes` assumes
  `teq (apT Sg P) Unit`); (ii) binds a row variable `r` to a row ending in `r`
  whose entries it makes absent (`bind_row_blocks_absent_tail`); (iii) binds a
  type variable to a record holding the variable behind an entry it makes absent
  (`bind_prop_blocks_absent`); (iv) unifies two entries of one label that it makes
  absent with different field images (`field_blocks_absent`, triaged above; since
  2026-11-24 W finds the pair when the field types clash, `field_clash_absent`, and
  the hypothesis is needed only for two variable field types).
- *`fld`/`frld`* at `bind_prop`, `bind_row` and the tail of `rewrite_row` (the
  field of an entry `Sg` makes absent satisfies the sort of the variable; #667).
- *The presence variable at `Numeric`* (`fld`'s second half): `push_sort` renames
  it to a variable of the sort, whose image `Unit` does not satisfy `Numeric`.
- *The occurs-under-present condition* (stage 7.6j): every occurrence of the
  bound variable in the type or row is under a present entry (`po`, `pos` in
  `GoatCompleteOcc.v`). This is the ratified exclusion of the pairs (ii) and
  (iii) above, stated as a hypothesis on `Sg`; the size lemma turns it into the
  occurs check passing. An occurrence in a presence position does not count (the
  sizes do not read a presence), so a variable bound to a type holding it only as
  the presence of one of its own entries is excluded too.
- *Plainness:* the types and rows are mu-free and group-free (`pf`/`prf`),
  locally closed, with every atom below the supply.

*As built (stage 7.6j, `GoatCompleteOcc.v`, `GoatCompleteUnifyPlain.v`,
`GoatCompleteRf.v`).* The row induction (items 1 and 3 of the list above) is not
done and L2 is not closed. What is done is the restatement at the environment,
the size lemma, plain completeness on the closed fragment, and the induction on
the record-free fragment, which carries the threading the row arms will reuse.

**Restatement at the environment.** `bind_row_sorted_complete` takes
`reqD DT (sR Sg r) (apR Sg R)` and concludes `reqD DT (sR Sg q) (apR S2 (sR s q))`
for the old row variables (the type atoms stay plain `teq`, which implies
`teqD`). `bind_prop_sorted_complete` takes and concludes `teqD`, because the
record arm of the induction calls it on a field of a row that `unify_rD` has
normalized, where `teqD` is what the hypothesis is. `rsat_reqD`, `rkok_reqD` and
`sat_teqD` carry a sort and a kind across the conversion (`nfR`/`nfT` only drop
absent entries, which no sort reads). `bind_prop_sorted_complete` also concludes
`n <= n'` and `DOk D' n'`, which the next call needs and the old conclusion left
to `bind_prop_sound`.

**The occurs-under-present size lemma (`GoatCompleteOcc.v`).** `po S vt vr T`:
a type variable satisfying `vt`, or a row variable satisfying `vr`, occurs in `T`
with every entry above it present under `S` (its presence image is not `Bool`);
`pos` is the same through at least one present entry. `po_size` and `pos_size`
bound `rsz`/`tsz` of the image below by the size of the variable's image, and
`nf_sz` says `nfT`/`nfR` leave `tsz`/`rsz` alone, so `bind_row_occ` and
`bind_prop_occ` conclude `r notin frv_row R` and `a notin ftv_typ T` from the
unifier (`reqD`/`teqD`) and the occurrence hypothesis. `bind_row_pres_complete`
and `bind_prop_pres_complete` are the two theorems with the hypothesis in place
of the stronger one. The lemma needs the entry to be present: `Maybe l p T (Var r)`
with `p := Bool` is the blocked pair (ii), and `pos` is false of it.

**Plain completeness on the closed fragment (`GoatCompleteUnifyPlain.v`).**
`unify_t_complete` and `unify_r_complete`: the same fragment (`cp`, `crow`) and
substitutions (`Res`) as `unify_complete_aux`, with `drop_abs` for `nfR D` and
plain `teq`/`req` hypotheses. It is a copy of the induction with the function
names changed (about 170 lines): the arms differ only in the row normalization,
which is the identity on a closed row of fields. The group arm of `unify_tD` needs
it for the payload, but does not follow from it alone: the `nfS` reduction of
`unify_tD_complete` (the induction runs for `nfS D1 S`) does not give the payload
call its plain hypothesis (`nfT` does not go inside a group, so `apT (nfS D1 S)
(Grp w A)` is not `apT S (Grp w A)`). The induction has to carry `S` for the
payload calls and `nfS D1 S` for the rest, or state the group case at `S`.

**The induction on record-free types (`GoatCompleteRf.v`).**
`unify_tD_rf_complete`: for types of base types, variables and arrows (`rf`), a
substitution `Sg` with `KR D DT Sg` and `teqD DT (Sg T1) (Sg T2)`, `DOk D n` and
every atom below the supply, `unify_tD` succeeds from some fuel on with `(s, D',
n')`, and an `S2` with `Sem`: `KR D' DT S2`, `DOk D' n'`, `SI n n' s` (the supply
grows, the images of the old variables are record-free over atoms below `n'`, no
row variable moves), `teqD DT (Sg x) (S2 (s x))` for the old `x`, and `S2` agrees
with `Sg` on the old row variables. Neither the occurs check nor the field
condition is a hypothesis: with no entry in a type every occurrence is present
(`rf_po`) and no field is absent. The measure is `tsz (apT Sg T1)`; the arrow case
runs the second call at `(D1, n1, S2)` on `apT s1 B`, with the hypothesis from the
factoring (`ap_factor_rf`) and the atoms and plainness from `SI`
(`SI_comp` composes two steps). `bind_prop_SI` proves `SI` for `bind_prop` (with
`push_sort_new`: a renamed type variable goes to itself or to an atom below the
new supply). Not stated for `unify_t`: the arms are the same, and the copy is
the same size as the one above.

**What remains of 7.6** (as of 7.6j; stage 7.6k below supersedes it).

1. *The row arms of the induction.* Add records to the induction above: the
   fragment gains rows with variables and presence entries, `SI` gains the row
   images (record and row-variable atoms below the supply, plain and locally
   closed rows), and `Sem` is stated at `reqD` for rows. The four arms of
   `unify_rD` call leaves that are proved: `bind_row_pres_complete` (either
   side), `rewrite_row_complete` and `row_cancel` for the rewrite, with `S2 ∘ s1 ∘
   sp ∘ s0` threaded. The measure is lexicographic: `rsz` counts no absent entry,
   so the entry count breaks the tie at one. The fuel is `Stable`. The
   hypotheses on `Sg` are the ones listed above, quantified as predicates on the
   substitution at each leaf (`po`/`pos` for the occurs checks, `fld`/`frld` for
   the field condition); they have to be carried to the recursive calls with the
   new substitution `S2`, by `fld_pull` and an analogue for `po` that has not
   been written.
2. *Groups outside `mu`.* `unify_t_complete` exists for the closed fragment; the
   group arm of `unify_tD` needs the induction to carry `S` beside `nfS D1 S`
   (above), and the plain induction for rows with variables is a second copy of
   item 1.
3. *`unify_t` on the record-free fragment,* the copy of `GoatCompleteRf.v`.

*As built (stage 7.6k, `GoatCompleteRfRows.v`).* Items 1 and 3 of the 7.6j
list are done for a restricted hypothesis set; the full set is open. DECISION
NEEDED, below.

**What is proved.** `unify_tD_complete_full` and `unify_rD_complete_full`: for
mu-free, group-free types and rows (`pf`/`prf`: base types, variables, arrows,
records of plain fields, presence entries and row variables) with every atom
below the supply (`atT`/`atR`), a substitution `Sg` that unifies the two at
plain `teq`/`req`, a trivial environment (`Dtriv`) and `DOk D n`, the unifier
succeeds from some fuel on (`Stable`) and `Pkg Sg n s D' n' S2` holds. Every arm
of `unify_tD` and `unify_rD` is in the induction: the variable and scalar
leaves, `bind_prop`, the record arm, `bind_row` on either side, and the rewrite
with `S2 ∘ s1 ∘ sp ∘ s0` threaded (`rw_arm`). The `Empty`/`Maybe` swap and a
row that is empty against one with an entry are contradictions (`rsz`).

**The two restrictions.**

- *Every entry is present* (`ps`/`psr`). A `Maybe l P T R` entry satisfies `Sg P
  = Unit`; a plain field is present. With every entry present, the four absent
  pairs of the 7.6f ruling cannot arise, the guard never binds, the field
  condition's absent half is vacuous, `nfR` is the identity on every row in play
  (`ps_nf`), `po`/`pos` follow from the entries (`ps_po`, `ps_pos_row`; a
  variable that `Sg` sends to `Unit` is excluded, which the unifier equation
  does: `Unit` is not an arrow or a record), and the measure needs no entry
  count: `rsz` falls by the front entry. The lexicographic measure of the 7.6j
  list is not needed here; it is needed for absent entries.
- *A trivial environment* (`Dtriv`: every type variable has sort `Any`, every row
  variable the kind `rk_any`). No sort is pushed, so `bind_prop` is
  `sbT a T` (`bind_prop_any`), `bind_row` renames only the tail of its row
  (`bind_row_triv_none`, `bind_row_triv_some`), every substitution respects the
  environment (`KR_triv`), and the field condition at a sort is `sat_any`. The
  closed fragment's `unify_tD_complete` makes the same assumption for records
  (`b = true -> forall c, D c = k_Any`). The sorted leaves
  (`bind_row_pres_complete`, `bind_prop_pres_complete`) are not used; only
  `rewrite_row_complete` is, at the trivial environment.

**What carries the hypotheses.** `Pkg Sg n s D' n' S2` is one step's promise: the
supply grows, `DOk` and `Dtriv` hold at the result, the images `s x` of the old
type atoms and `s q` of the old row atoms are in the fragment over atoms below
`n'` with every entry present under `S2`, and `Sg` factors through `s` by `S2`
at plain `teq`/`req`. `Pkg_comp` composes two steps; `pkg_ap_T`/`pkg_ap_R` carry
a type or row of the fragment through a step (`pf_ap`, `atT_ap`, and `ps_pull`,
the analogue of `fld_pull` for the presence hypothesis); `pkg_fac_T`/`pkg_fac_R`
factor `Sg` through it. Plain `teq`/`req` is enough because `Sg`'s images are
never normalized: with every entry present, `nfR` does nothing to the rows the
calls pass, and the plain `rewrite_row_complete` takes a plain `req`, so item 2
of the 7.6i list (the conversion at the environment) does not arise here.
`Pkg_sem` reads a step at `KR`, `teqD`, `reqD`.

**Leaves.** `pkg_bind_prop`, `pkg_bind_row` (tail renamed to `ea n`; `S2` is `Sg`
with `ea n` sent to the old tail's image), and `pkg_rewrite` (`rw_shape`: the type
variables are untouched, and the row variable is bound to an entry of three fresh
variables or nothing; `rw_facts`: the presence, field and rest it returns are in
the fragment, with every entry present under `S2`). `unify_rD_rw` unfolds the
arm.

**What remains of 7.6** (as of 7.6k; stage 7.6l below supersedes it).

1. *Absent entries.* The hypothesis `ps` is the strong side of the ratified
   list. Dropping it brings back (i) to (iv) of the 7.6f ruling as predicates on
   `Sg` at each leaf, the lexicographic measure (an absent entry has size 0;
   `rewrite_row_front`'s absent-pair alternative), the `Empty`/`Maybe` swap arm,
   and `fld_pull`/an occurs analogue to carry them to the recursive calls with
   `S2`. The conversion question of the 7.6i item 2 returns with it: an image of
   `Sg` may then hold an absent entry, so `reqD` is not `req`.
2. *Sorts.* `Dtriv` is the assumption to drop. `bind_prop_sorted_complete`,
   `bind_row_pres_complete` and `rewrite_row_complete` are proved for sorted
   environments, but `Pkg` then needs the fresh variables of `push_sort`
   (`SI` of the 7.6j induction: `bind_prop_SI`, `push_sort_new`) and the
   presence variable at `Numeric` (`fld`'s second half) as a hypothesis carried
   through the steps.
3. *Groups outside `mu`.* The group arm of `unify_tD` hands its payload to the
   plain `unify_t`; the induction needs the plain unifier beside it (the 7.6e
   adaptation) and `S` beside `nfS D1 S`. Not started.
4. *`unify_t` on the fragment,* the copy of this induction for the plain unifier.

DECISION NEEDED: the hypothesis set of `unify_tD_complete_full` is stronger than
the ratified list (every entry present, trivial environment). Options: (a) accept
it as the stage-7.6k result and take absent entries and sorts as separate stages
(chosen: each is a self-contained extension of `Pkg` and the arms, and the
present, trivial case is the one L3's core constructs (variables, application,
`let`, projection) reach first); (b) hold the stage until the ratified list is
covered. The shape of statement A's hypothesis for L3 is the open point: `ps`
and `Dtriv` are properties of `Sg` and the environment at the call, so L3 has to
show them of the substitution it builds, which fails for a program with a numeric
literal or operator in scope (a `Numeric` sort) and for one that restricts a
record.

*As built (stage 7.6l, `GoatCompleteRfRows.v`, `GoatCompleteRewrite.v`,
`GoatCompleteBind.v`, `GoatCompleteBindRow.v`).* The trivial environment is gone
and the plain unifier runs beside the one W calls. Groups are not done.

**What is proved.** `unify_tD_complete_full` and `unify_rD_complete_full` take
`KR D DT Sg` (the sort of each variable's image, the kind of each row variable's
image, the labels it lacks) and `Dsrt D Sg` in place of `Dtriv D`, and `Pkg`
promises `Dsrt D' S2` and `KR D' DT S2` at the environment the step returns. A
type variable may have any of the four sorts. `Dsrt` is two conditions: `Drow D`
(every row variable's sort is `Any` or `Eq`) and `NN D Sg` (`Sg` sends no
`Numeric` variable to a record). The same theorems conclude that the plain
unifier (`unify_t`, `unify_r`) succeeds with the same result at the same fuel
(one `Stable` of a conjunction), which is the prerequisite for the group arm:
`unify_t` reads rows through `drop_abs`, `drop_abs_ps` says it is the identity on
a row whose entries are all present, and each leaf (`stable2_*`) is stated for
both.

**Leaves.**

- *`bind_prop`, `bind_row`: the fresh variables of `push_sort`.* `RenN n n' r`:
  `r` sends each atom below `n` to itself or to a fresh atom in `[n, n')`, types
  and rows alike; `RenN_comp` composes two, `RenN_push`, `RenN_push_r` and
  `RenN_tail` are the three stages. `bind_prop_unfold`, `bind_row_unfold`,
  `bind_row_core_unfold` and `bind_row_fin_unfold` read the stages off a successful
  call, `pkg_close_T` and `pkg_close_R` close the last one (the images of the old
  atoms are renamings except the bound atom, whose image is the renamed type or
  row, in the fragment with every entry present by `ren_ap_T`/`ren_ap_R`/`ren_ps_T`/
  `ren_ps_R`). Existence comes from `bind_prop_sorted_complete` and
  `bind_row_sorted_complete`, which now take a Boolean choosing the conversion of
  their hypothesis and factoring (`teqX`, `reqX`: `true` is the old statement at
  `teqD`/`reqD`, `false` is plain `teq`/`req`); the plain form is what `Pkg`
  needs, because an image of `Sg` may hold an absent entry that `reqD` would
  normalize away.
- *`bind_prop` at `Any` and `Eq`* (`pkg_bind_prop_ae`): the field condition is
  `ps_fld` (every presence is `Unit`, which satisfies both sorts). A variable of
  sort `Numeric` is never renamed at these sorts (`push_sort_keeps`, `finer_b
  Numeric Any = finer_b Numeric Eq = true`), and `push_sort_sorts` says a pushed
  sort is only ever the pushed one, so `NN` passes to `S2`.
- *`bind_prop` at `Numeric` and `Literal`* (`pkg_bind_prop_nl`): the type is `Int`
  or `Float`. An arrow satisfies neither sort, a record satisfies no `Literal`, and
  a record bound to a `Numeric` variable is excluded by `NN`; the other scalars
  fail `sat`. A scalar has no variable, so no sort is pushed and the step is
  `bind_prop_scalar`.
- *`bind_row`* (`pkg_bind_row`): the sort is `Any` or `Eq` (`Drow`), so the field
  condition is `ps_fld` again, `ps_lacks` makes the lacks check and the
  presence-to-`Bool` step vacuous (an entry of a label the kind lacks cannot be
  present), and the joined kind of the renamed tail has a sort `Drow` allows
  (`Drow_join`).
- *`rewrite_row`* (`pkg_rewrite`): `rewrite_row_complete` no longer takes the
  field condition at the tail (`Hfield`). `rewrite_row_spec` takes `SurfP`, a row
  that presents the label with a presence that is not `Bool`, and two presentations
  of one label agree on a present one (`row_cancel`), so the walk never reaches the
  absent presentation whose field the sort of the row variable does not constrain.
  The hypothesis was unsatisfiable at a sort other than `Any` (take the absent
  presentation `l ^ Bool : T1` with `T1` unfit, which `req_abs` makes a
  presentation of any row), so no program with a sorted row variable at the tail
  could have met it. The three shapes of `rewrite_row` (`rw_shape`): the closed
  end and the lacking-label case give presence `Bool`, which the present front
  entry contradicts; the row-variable case binds one row variable to an entry of
  three fresh variables.

**The Numeric presence hypothesis, as carried.** `fld`'s second half asks `sat DT
k (Sg P) = sat DT k Unit` for each presence variable `P` of a type bound at sort
`k`, which holds exactly for `Any` and `Eq`. `bind_prop` at `Numeric` renames a
presence variable to a `Numeric` one, the extension `S2` has to send that
variable to `Unit`, and `Unit` does not satisfy `Numeric`, so no `S2` respects
the new environment. The hypothesis `NN` is stronger than that corner: it excludes every record
bound to a `Numeric` variable, with presences or not (`{x: 1} + {x: 2}`), and
`Drow` excludes `Numeric` and `Literal` rows. The programs it covers are the ones
whose numerals and operators meet scalars, which is what L3's core constructs
(variable, application, `let`, projection, numerals, comparison) build.
DECISION NEEDED: `NN` and `Drow` are sufficient but not necessary. Options: (a)
accept them as the stage-7.6l result (chosen: they are conditions on `Sg` and the
environment that L3 can read off the typing derivation, and the corner they leave
is the numeric record); (b) state the weaker condition (a `Numeric` or `Literal`
variable is not bound to a type with a presence variable), which needs the
extension `S2` to agree with `Sg` on the old atoms through every leaf, and `NN`
over the atoms of the types in play rather than over the environment.

**What remains of 7.6** (as of 7.6l; stage 7.6m below supersedes it).

1. *Absent entries (waits on #667).* The hypothesis `ps` is the strong side of
   the ratified list. Dropping it brings back (i) to (iv) of the 7.6f ruling as
   predicates on `Sg` at each leaf, the lexicographic measure (an absent entry has
   size 0; `rewrite_row_front`'s absent-pair alternative), the `Empty`/`Maybe`
   swap arm, and `fld_pull`/an occurs analogue to carry them to the recursive
   calls with `S2`; the field condition's first half (`apT S P = Bool -> sat DT k
   (apT S T)`) is vacuous under `ps` and returns with them, and so does `Hfield`
   at a presentation `Sg` makes absent. The conversion question of the 7.6i item
   2 returns too: an image of `Sg` may hold an absent entry, so `reqD` is not
   `req`, and the plain forms of the leaves (`teqX false`, `reqX false`) have to
   give way to `reqD` ones or `Sg` has to be replaced by its normalization. A
   principal-verdicts change in #667 changes how W treats an absent presence, so
   none of this is started.
2. *Groups outside `mu`.* The group arm of `unify_tD` hands its payload to
   `unify_t`, which now succeeds beside it on the fragment, so the call has its
   completeness. What blocks adding `typ_Grp w A` to the fragment is not the
   unifier: `pf` (`GoatCompleteBind.v`) excludes `typ_Grp`, and the sorted leaves
   (`sat_ren_mut`, `sat_reach_mut`, `fld`, `lcb_ap_var`, `ftv_ren`) are stated
   for `pf`, so `bind_prop` of a variable to a type with a group inside has no
   completeness lemma; `po` is `False` at `typ_Grp` and `tsz` is 1, so the occurs
   check cannot be derived for a variable inside a payload, and the measure of
   the induction does not fall from a group to its payload. The extension is
   `pf`/`sat`/`po`/`tsz` for groups (the 7.6e closed fragment has `cp` for
   them), then `ps` and `atT` on a payload and the `nfT` identity on a group
   (`nfT` does not enter one, so `S` is carried as it is, with no `nfS D1 S`).
3. *Statement A's hypotheses, as they stand after 7.6l.* Carried through the
   induction and proved of every step: the occurs-under-present condition (7.6j,
   `ps_po`, `ps_pos_row`), the sorts (`KR`), `Drow` and `NN` (the numeric
   hypothesis above), and the presence variable at `Numeric` (`NN` and `Drow`
   together). Dropped: `Hfield` at the tail of `rewrite_row` (for a present front
   entry). Waiting on #667, because each concerns an entry `Sg` makes absent: the
   four pairs of the 7.6f ruling, `fld` at an absent entry, and `Hfield` at an
   absent presentation.

*As built (stage 7.6m, `GoatCompleteBind.v`, `GoatCompleteBindRow.v`,
`GoatCompleteRows.v`, `GoatCompleteOcc.v`, `GoatCompleteRfRows.v`).* Tag groups
outside `mu` are in the fragment. `unify_tD_complete_full` and
`unify_rD_complete_full` keep their statements; `pf` now admits `typ_Grp w A`.

**What is proved.**

- *The fragment.* `pf (typ_Grp w A)` is `pf A /\ spn w 0 A`. `spn w j A` says the
  payload spells the group's parameters: arrows ending in `Unit`, and slot `j`
  (code `6 + j`) is used by some tag of `gtags w`. `spn_ap` keeps the shape under
  a substitution. `ps S (typ_Grp w A)` is `ps S A`; `atT` needs nothing (the free
  variables of a group are those of its payload); `fld D1 S k (typ_Grp w A)` is
  `fld D1 S k A`.
- *The sort at a group.* `sat D k (typ_Grp w A)` is `True` at `Any`, `spine_sat` at
  `Eq`, `False` at `Numeric` and `Literal`. `spine_sat` asks a component to be `Eq`
  only for a slot some tag uses, and `spn` makes every slot used, so it is the
  conjunction of `sat D Eq` on the components. `sat_ren_mut` and `sat_reach_mut`
  are derived from `sat_ren_aux` and `sat_reach_aux`, whose motive for a type is a
  pair: the original statement, and (at `k = k_Eq`) the same statement for
  `spine_sat D w j` of a payload, proved by induction down the arrows. The group
  case of each is that second half at `j = 0`. The renaming and the reach lemmas
  then serve `bind_prop` of a variable to a type with a group inside
  (`bind_prop_sorted_complete` is unchanged). `lcb_ap_var`, `ftv_ren`, `nf_sz` and
  `ps_nf` needed no group case: they are stated for every type, and `nfT` does not
  enter a group (`nfT D (typ_Grp w A) = typ_Grp w A`), so `S` is carried at a group
  as it is, with no `nfS D1 S`.
- *The measure and the occurs check.* `tsz (typ_Grp w A)` is `S (tsz A)`, so it
  falls from a group to its payload, and `po S vt vr (typ_Grp w A)` is `po S vt vr
  A`, so `po_size` and `bind_prop_occ` reach a variable inside a payload (a
  variable bound to a group that contains it has a strictly larger image).
  `ps_po`, `ps_pos` and `ps_fld` follow the payload; `pf_ap`, `pf_lcb`, `ps_pull`
  and `fld_pull` carry a group through a step.
- *The arm.* The group arm of `unify_tD` and of `unify_t` both call `unify_t` on
  the payloads when the declarations agree. `teq_Grp_inv` gives the declaration
  (`w' = w`) and `teq` of the images of the payloads, the measure falls, and the
  induction hypothesis on the payloads at the same `Sg` returns the plain-unifier
  success it needs (the second conjunct of the induction's `Stable`); the arm
  concludes both unifiers from it, with its `Pkg`. `pkg_bind_prop_nl` has a group
  case (a group satisfies no `Numeric` or `Literal` sort). `pf_group_param` is a
  concrete member of the fragment.

DECISION NEEDED: `spn` requires every slot of a group's payload to be used by a
tag. `bind_prop` pushes the sort of the variable it binds onto every free
variable of the type (`push_sort` over `ftv_typ T`), unused slots included, while
`spine_sat` asks `Eq` only of used slots. A variable `a` of sort `Eq` bound to
`typ_Grp w (b -> Unit)` with slot 0 unused is then bound with `b` renamed to a
fresh variable of sort `Eq`; a substitution `Sg` that sends `b` to a function
satisfies `sat D1 Eq (Sg a)` and unifies, but no extension `S2` respects the new
environment, so the unifier is not complete for it. That is a gap between W and the
declarative rule, not a limit of the proof. Options: (a) accept `spn` as the
stage-7.6m result (chosen: it covers every group whose parameters all appear in a
tag, which is what lists and the tag examples are, and it states the corner); (b)
have `push_sort` skip unused slots, a checker change (and a change to
`infer.rs`, which this plan does not touch) that the owner would have to decide;
(c) declare that a group declaration cannot have an unused parameter, if the
checker already enforces it (not checked here), which would make `spn` a lemma.

**What remains of 7.6.**

1. *Absent entries (waits on #667).* Unchanged from 7.6l: dropping `ps` brings back
   (i) to (iv) of the 7.6f ruling as predicates on `Sg` at each leaf, the
   lexicographic measure, the `Empty`/`Maybe` swap arm, `fld_pull` and an occurs
   analogue with `S2`, the field condition's absent half and `Hfield` at an
   absent presentation, and the conversion of the 7.6i item 2 (`reqD` against
   `req`). A principal-verdicts change in #667 changes how W treats an absent
   presence, so none of it is started.

Nothing else is left of the unifier's completeness. Stage 7.6 can be called done
modulo #667: the groups outside `mu` of the 7.6l list are in, the sorted
environments are in, and the plain unifier runs beside the one W calls. The
hypotheses L3 has to meet are the ones carried through the induction and proved of
every step, none of them open: every entry present (`ps`), `KR`, `Drow` and `NN`
(DECISION NEEDED of 7.6l), and `spn` on each group (DECISION NEEDED above).
`unify_coD` needs no copy: `unify_coD_stable` turns a `unify_tD` success into a
coercion-free `unify_coD` one.

**L3, W's cases.** One lemma per construct, each mechanical once L0 to L2 exist
(the soundness proof has the same case list):

| Construct | Cases | Note |
| --- | --- | --- |
| variable, numeral, `Float`, string, `unit`, booleans | 6 | `T_Num` and the instance `S1 a := Int` or `Float` use `kres` |
| `program`, call | 2 | `T_Abs` opens with a fresh name; closing reverses with `cl` (`GoatClose.v`) |
| `let`, `letrec` | 3 | `gen_mono`; `T_LetMono`; the group case sums the unification sequence of `unify_grp` |
| `if`, operators, `float(e)`, comparison | 4 | `bin_sig` and `generic_sort` (the bin rule picks the principal sort) |
| record, projection, spread, restrict | 4 | rows, presence, `rm` |
| tag, `match`, default arm, list | 3 | `typ_Grp w (spine Ts)`; arm bodies in a context with the payload |

*As built (stage 7.7, `GoatCompleteCore.v`, `GoatCompleteSpn.v`).* L3 is proved for
the constructs whose types are base types, variables and arrows: variables,
numerals, `Float`, string, `unit` and boolean constants, `program`, a call, `if`,
the arithmetic operators, `/`, a comparison, `float(e)` and a `let` whose binding
is not a value. `let` of a value and `letrec` are not proved (below), nor are the
record and tag constructs (stage 7.8).

**Statement.** `infer_complete_core`: from `ctyping Dd Gd e T1`, a state
`(D, G, n)` with `DOk D n`, a substitution `Sg` with `KR D Dd Sg`, `GOk n G` (every
binding of `G` is a record-free type over atoms below `n`) and `CI Dd Sg Gd G` (at
each name, the derivation's type is `teqD Dd` to `Sg` of the algorithm's), the run
of `infer` succeeds from some fuel on (`Stable`) at some `(s, D', T, n', e')`, and
`Sem Dd Sg n s D' n' S2` holds (the 7.6j step: `KR D' Dd S2`, `DOk D' n'`, the
images of the old atoms are record-free over atoms below `n'`, `Sg` factors
through `s` at `teqD Dd`), `T` is record-free over atoms below `n'`,
`teqD Dd (apT S2 T) T1`, and `is_gen_value e' = is_gen_value e`.
`infer_complete_core_closed` is the closed case (`G = nil`, `Sg = sid`) with
`erase e' = e` from `infer_closed_sound`. `core_identity` and `core_comparison` run
it on two programs.

Adaptations, each a change from the sketch above.

1. **The unifier's hypotheses are gone, not met.** The core's types are
   record-free, so each unification is `unify_tD_rf_complete` (7.6j), whose only
   hypotheses are the sorts (`KR`) and the atoms. The hypotheses of
   `unify_tD_complete_full` that L3 was to meet (`ps`, `Dsrt`/`NN`, `Drow`, `spn`)
   do not arise: a numeric variable bound to a record is an `Sg` the induction
   never asks about, because the algorithm's types hold no record. They return with
   the record constructs of 7.8.
2. **`ctyping`, a copy of `typing` for these constructs.** It differs in three
   places. A binder's premise holds at every name fresh for the context and the
   term, because the algorithm opens a binder at the one name `fresh_var` picked and
   the induction hypothesis is about the derivation it was given; `typing`'s
   cofinite premise gives that name only after renaming, and the renaming lemma
   (`typing_rename_var`) is not an induction hypothesis. The context's bindings are
   monomorphic (`C_Var` asks for `sch_mono`). And `sig_quot_rec`, the division of two
   records, is absent: the algorithm unifies the operands of `/` with `Float`, so
   `{x: 1.0} / {x: 2.0}` has a derivation and no run (the corpus skips it as
   "arithmetic on non-primitive operands"). `ctyping_typing` embeds it in `typing`;
   the converse (a `typing` derivation of a core term is a `ctyping` one, by renaming
   the binders, when it does not use `sig_quot_rec`) is the first step of 7.9.
   Stage 7.7b below settles why `sig_quot_rec` stays out.
3. **`teqD`, not `teq`.** The conclusion is `teqD Dd (apT S2 T) T1`, the
   conversion `T_ConvD` uses, because the derivation may reach a type through
   conversion at its environment.
4. **The context relation is `CI`, not `ctx_le`.** `ctx_le`/`sch_le` compare
   schemes by their instances, and an instance of `apS Sg sc` substitutes
   `Sg`'s images under the scheme's binders (`apS` captures). `OkS Sg` rules that
   out (its images are over even atoms), but the derivation's types may hold any
   atom, and the substitutions the unifier's completeness returns carry no such
   fact. With monomorphic bindings there is nothing to capture, and the relation is
   `teqD` of one type.

**`spn` is a lemma (`GoatCompleteSpn.v`).** The ratification of 7.6m (option (c)):
goat has no syntax for an unused group parameter, so `spn` holds for every declared
group. `type_slots_facts`/`cases_slots_facts` show a declaration numbers its `_`
slots `6 .. 6 + m - 1` in order, each in some tag, and `nparams` counts `m`;
`declared_gwf` says every group `decl_entries` reads out has that property
(`gwf`: each `i < nparams w` is used by some tag), and `spn_declared` concludes
`spn w 0 (spine Ts)` for `Ts` of length `nparams w`, which is the spine W builds
(`fresh_tys`). The group constructs of 7.8 use it; nothing in 7.7 does.

**What remains of 7.7** (as of 7.7; stage 7.7c below supersedes it).

1. *`let` of a value and `letrec`.* Both generalize, so the algorithm's context
   holds schemes (`gen_ren`) and the induction compares them with the derivation's
   (`gen`) by `gen_mono_let`. Its hypotheses are the ones the core did not need.
   `OkS S2` (images of even atoms are over even atoms) cannot be had from the
   unifier's step and fails for a derivation whose types hold an odd atom;
   `kres` into the environment the derivation's first premise lives in
   (`extr (ext D V k) ..`) needs `Sg`'s images to avoid the atoms `V` the premise
   re-sorts, which a derivation need not satisfy (its generalized atoms are its own
   choice); and `frozen` is the context relation read through `ctx_le`.
   DECISION NEEDED: how to discharge the first two. Options: (a) rename the
   derivation's atoms to fresh even ones before the induction, a lemma about
   `typing` (substitution of atoms, `typing_tsubst_gen_mut` is the closest) that
   the induction then uses once at the top; (b) carry both as hypotheses of the
   theorem and prove them of the closed case, where the derivation's atoms are the
   program type's alone; (c) state completeness up to a choice of derivation (the
   classical form: some derivation of the same term, with fresh generalized atoms,
   is the instance). (a) is the smallest and keeps the statement. Not started.
2. *The conversion from `typing`* (above, adaptation 2).
3. *Records, spread, restrict, tags, `match`, methods* (7.8), with the
   hypotheses of 7.6 (`ps`, `Dsrt`, `spn`, absent entries waiting on #667).

*As built (stage 7.7b, `GoatInfer.v`, `GoatInferW.v`, `GoatInferSound.v`,
`GoatInferGuard.v`, `GoatCompleteCore.v`).* Stage 7.7b triaged record `/` and
fixed W; the `let` of a value, `letrec` and the conversion are not started.

**Record `/` (`sig_quot_rec`), triaged against the checker.** Ratification of
7.7 ruled: where the checker accepts, W must; where it refuses, tighten the
calculus. `infer.rs` (`type_division`) is neither one nor the other, because its
rule reads the operands' types as they stand when it reaches the operator:

| Program | Checker |
| --- | --- |
| `{x: 1.0, y: 2.0} / {x: 3.0, y: 4.0}` and with `Int` fields | accepts, `{x: Number, y: Number}` |
| a name bound to a record, `a / b` | accepts |
| `f = program(a) do a / {x: 1.0} done`, `f({x: 1.0})`, and with the record on the left | accepts (a record on either side fixes the shape) |
| `{x: 1.0} / 2.0`, `2.0 / {x: 2.0}`, `{x: 1.0} / {y: 2.0}`, `{x: 1.0, y: 2.0} / {x: 3.0}` | refuses |
| `f = program(a) do a / a done`, `f({x: 1.0})` and `f = program(a, b) do a / b done` at records | refuses: no operand is a record at the operator, so `/` fixes `Float` |

So there are two answers. *The record cases the checker accepts: W was
incomplete, and is fixed.* `quot_ty T1 T2` (`GoatInfer.v`) is the type `/` works
at: the record of the same labels at `Float` when the left operand (or, failing
that, the right) is a closed record, and `Float` otherwise. W unifies both
operands with it and returns it; the unifier's coercions turn an `Int` field into
a `Float` one, as the checker widens. `infer_sound` derives it with
`sig_quot_rec` (`quot_ty_facts`: the type is closed under substitution, even and
a `Float` record; `quot_ty_mg` in `GoatInferGuard.v` for the guard invariant). The
corpus reader no longer skips `/` on record operands (it still skips `+ - * // %`
on them), writes no `float(e)` around them, and `HANDWRITTEN` holds the programs
of the table.

*The function cases the checker refuses stay a gap between calculus and checker.*
`program(a) do a / a done` applied to a record has a `typing` derivation (the
parameter at a record type, `sig_quot_rec`) and no checker run, which reads `a`
as a variable at the operator and fixes `Float`. No declarative rule can say "the
operand's head is known here": which names are known depends on the order the
checker walks the term. Tightening `sig_quot_rec` therefore cannot make the
calculus equal the checker. Soundness does not need it (W infers less than the
calculus derives), and the core's L3 is unaffected (`ctyping` has no
`sig_quot_rec`, and `quot_ty_rf` shows that for record-free operand types
`quot_ty` is `Float`, so the division case of `infer_complete_core` changes by one
rewrite). It returns for 7.8: the record constructs' `ctyping` needs a
`sig_quot_rec` rule whose operand type is a record at the operator in W's order
(a closed record literal, or a variable the context binds to one), and
completeness is stated for that rule, not for `typing`'s. DECISION NEEDED: the
owner may prefer instead to make the checker's rule order-independent (join the
operands' shapes after inference, the way `join_operands` joins `+`), which would
let `sig_quot_rec` stand as it is and close the gap; that changes checker
acceptance (`f(a) = a / a` at a record would pass), which this stage does not do.

**The atom-renaming lemma (option (a)), what it has to say.** Renaming a
derivation's free atoms to even ones is `typing_ap` at an injective renaming with
the sorts moved along (`kres`), and is routine. It does not give what the `let`
case needs. The unifier's substitution `Sg` collects the types of every
sub-derivation already walked, so it mentions the atoms a `T_Let` generalizes
inside an earlier `let`, and a later `let` that reuses the same atom as its `V`
meets an `Sg` whose images hold it. The lemma has to produce a derivation in
which every `T_Let`/`T_Letrec` generalized set is disjoint from every atom outside
that binding's own first premise, and even. That is a normal form for `typing`
(prove by induction on the derivation, freshening each generalized set with
`mk_rename`, the way `typing_tsubst_gen_mut` already does for `T_Let`), stated
as a new inductive judgement or as a size-indexed lemma with an avoid set. It is
the first thing 7.7c does.

**Alternatives that lost.** Prove completeness against a separate declarative
principal-type system and show it equivalent to `typing`: it doubles the rule
set and the equivalence needs the same lemmas. Replace W with a constraint-based
inferrer whose completeness is easier: it throws away the soundness proof and the
tie to `infer.rs`, which is W-shaped. Prove completeness only for a decidable
subset of `typing` by a size bound: nothing in `typing` is bounded.

*As built (stage 7.7c, `GoatSound.v`, `GoatCompleteFresh.v`, `GoatCompleteNf.v`).*
Stage 7.7c proved the normal form for `typing` that `let` of a value and `letrec`
need. It did not add those two cases to L3, and it did not prove the conversion
from `typing`; the first section below says why, and the second says what is next.

**The renamer is a parameter (`GoatSound.v`).** `tsubst_gen_core` and
`tsubst_gen_pin` renamed a binder's generalized atoms with `mk_rename`, which
promises only that the new atoms are outside a given set. `renamer P` is the
statement of a renamer whose new atoms all satisfy `P`; `tsubst_gen_core_ren` and
`tsubst_gen_pin_ren` take one, and also say the new atoms are outside the
substitution's support `A`. The originals are the instances at `mk_rename`.

**One binder (`GoatCompleteFresh.v`).** `mk_rename_even` is `mk_rename` with even
fresh atoms (`fresh_even_list`, by pigeonhole on the injection `ea`).
`typing_let_even` and `typing_letrec_even` are the `T_Let` and `T_Letrec` cases of
`typing_tsubst_gen_mut` run at the identity substitution with that renamer: a
binder whose premises hold has another whose first premise is at a renamed type,
whose generalized atoms (type and row) are even and outside any finite set `B`,
and whose body is re-derived under the renamed scheme (`sch_equiv`).

**The normal form (`GoatCompleteNf.v`).** `ntyping Av D G e T` is `typing` with,
at each `T_Let` and `T_Letrec`, generalized atoms that are even and outside
`bg Av G T`, the atoms of the binder's own conclusion and context and of the
set `Av` handed down. Every rule hands its premises the atoms of its own
judgement and of its siblings' types (`bg Av G T` and the premise types), so at a
binder `Av` holds every atom of the judgements that enclose it and of the
siblings beside it. `typing_normal` says a derivation over an environment of
finite support (`supp_ok`) has a normal form at the same judgement and any `Av`;
`ntyping_typing` says a normal form is a derivation, so the judgement is
unchanged. The proof is by induction on the size of the term (`esz`): renaming a
binder's atoms re-derives its premises, so they are not subderivations, and the
induction hypothesis has to be about terms. The binder cases call
`typing_let_even`/`typing_letrec_even` and then the induction hypothesis on the
renamed premise and on the body at each fresh name; every other rule is the
derivation's own induction hypothesis.

Two choices, each a change from the sketch above.

1. **The avoid set is passed down, not a property of the whole derivation.** "Disjoint
   from every atom outside the binding's first premise" would be a set computed
   from the derivation, and a derivation is a proof: no function reads atoms off
   it, so the set cannot be an index of the normal form without a second
   inductive that mirrors `typing`. Handing each premise the atoms of the
   judgements around it gives the atoms that are in play when the binder is
   reached, which is what the induction uses: the algorithm's substitution
   carries the derivation's types for the atoms still in the context and the
   pending types, and those are types of enclosing and sibling judgements. It
   does not give disjointness from atoms deep inside an earlier sibling, which
   the algorithm no longer holds in its context.
2. **No output set.** Threading a set out of each premise would make a
   binder's premise at one name depend on the name, and `typing`'s cofinite
   premises would then need a renaming lemma for the normal form. The passed-down
   set needs none.

**What remains of 7.7** (as of 7.7c; stage 7.7d below supersedes it).

1. *`let` of a value and `letrec` in L3.* Three things stand between the normal
   form and `gen_mono_let`, none of them about the derivation's shape.
   (a) `OkS S2` needs the images of the algorithm's atoms to be over even
   atoms. `unify_tD_rf_complete` returns `S2` existentially and `Sem` says
   nothing about the atoms of its images, so `Sem` has to be strengthened (the
   new images are over atoms of the images already there and of the
   derivation's judgement types) and the derivation's atoms made even. The
   normal form makes the generalized atoms even; the rest are the atoms of the
   judgement types, which a top-level renaming (`typing_ap` at an injective map
   to even atoms) makes even once a finite set holds all of them, and no
   statement in the development bounds a derivation's atoms yet.
   (b) `KR D Dext Sg`, the sorts for the first premise's environment, needs
   `Sg`'s images of the atoms in play to avoid the generalized atoms. That is
   what `Av` gives, once the induction states that the images of the live atoms
   (those in the algorithm's context and pending types) are over atoms of `Av`.
   (c) Working the `let` case through shows that the continuation after the premise runs at `Dd`, not `Dext`, and `S2`
   sends the atoms the binder generalizes (dead once generalized) to types over
   the generalized atoms at their `Dext` sorts, so `KR D1a Dd Sa` fails at them.
   `KR`, `CI` and the factoring `F` have to be restated for the live atoms, the
   ones the context and the result types mention, before a binder can end. This
   changes the statement of `infer_complete_core`, and it is the next stage's
   first step; with it, (a) and (b) are statements about live atoms too.
2. *The conversion from `typing`.* `ctyping` has monomorphic contexts and
   no `let` of a value, so the conversion of a derivation that uses a generalizing
   binder needs `ctyping` to carry schemes (`C_Var` by `inst`, `C_Let`,
   `C_Letrec`, with the normal form's conditions as premises) first; it would
   be the normal form with a binder's premise at every fresh name and no record
   division. DECISION NEEDED (record division): `ntyping`'s `T_Bin` rule takes any
   `bin_sig`, `sig_quot_rec` included. Options: (i) a core normal form whose
   operator rule takes the operand types as record-free (`rf`), which excludes
   `sig_quot_rec` for the whole core and leaves 7.8 to add the head-known rule;
   (ii) keep `typing`'s rule and add a head-known hypothesis to the conversion.
   (i) is the smaller, and is what the conversion should do until 7.8; chosen.
3. *Records, spread, restrict, tags, `match`, methods* (7.8), as before.

*As built (stage 7.7d, `GoatCompleteSorts.v`, `GoatCompleteBind.v`, `GoatCompleteOcc.v`,
`GoatCompleteRf.v`).* Stage 7.7d proved the first of the three things 7.7c's item 1
needs, the bound on the atoms of the unifier's extension `S2`. It did not restate
`infer_complete_core` over live atoms, add `let` of a value or `letrec`, or build
the conversion; the list below says why and what order they go in.

**`Img`, the extension invents no type.** `Img Sg S2` says every image of `S2` is
an image of `Sg`: `forall y, exists z, sT S2 y = sT Sg z`. It is reflexive and
transitive (`Img_refl`, `Img_trans`), and `Img_bound` turns any predicate that holds
of all of `Sg`'s images into one that holds of all of `S2`'s. The unifier's `S2` is
built from `Sg` by `supd` at the fresh atoms `push_sort` makes, each sent to the
image of the atom it renames, so the proof is a conjunct threaded through
`push_sort_complete`, `bind_prop_sorted_complete`, `bind_prop_pres_complete`,
`sem_bind` and `unify_rf_complete_aux` (whose arrow case composes by `Img_trans`).
`unify_tD_rf_complete_img` adds it to `unify_tD_rf_complete` (which keeps its
statement), and `unify_tD_rf_complete_even` is the consequence `OkS` needs: if all
of `Sg`'s images are even, so are all of `S2`'s. `Img` is a conjunct beside `Sem`,
not inside it, because `Sem_supd` takes a step from `supd Sg (ea n) U` to a step
from `Sg`, and `U` is no image of `Sg`; folding `Img` into `Sem` needs a predicate
parameter (`Img` relative to an allowed set of types) that 7.7e introduces with
the live-atom restatement.

**What remains of 7.7.**

1. *Live atoms.* `KR D Dd Sg` is for every atom, but the unifier's completeness
   needs it for every atom and `let` needs it for none of the dead ones: restate
   `KR`, `CI` and the factoring over the live atoms, and rebuild a full `Sg'`
   (agreeing with `Sg` on the live atoms, a witness of each sort elsewhere) before
   each call to `unify_tD_rf_complete_img`. With `Img` relative to an allowed set,
   this is the change to `Sem`, `Done` and the twelve cases of
   `infer_complete_core`; it comes first.
2. *Even derivations.* `OkS S2` needs `Sg`'s images even; the closed case starts at
   `sid`, but `supd Sg (ea n) T1` at an arrow parameter or a `T_Num` instance puts
   the derivation's own types in the images. A top-level renaming of the whole
   derivation to even atoms (`typing_ap` at an injective map, with a bound on the
   derivation's atoms that nothing yet states) is needed.
3. *`let` of a value.* `gen_mono_let` with `frozen` from `ctx_le`, `KR` for the
   premise's environment from the live-atom `KR` and `Av` (7.7c, item 1b), the
   continuation's `KR` at `Dd` (item 1c).
4. *`letrec`.* `T_Letrec`'s premise is `field_typing` at `typ_Record R`, and the
   scheme it binds is over a record type, so a `letrec` is not in the record-free
   fragment; it belongs with 7.8 and needs the hypotheses of 7.6 (`ps`, `Dsrt`,
   `spn`). DECISION NEEDED: the ticket listed `letrec` with 7.7d; it cannot be
   done over `rf` types. Chosen: move it to 7.8.
5. *The conversion from `typing`* through `ntyping` into a `ctyping` with schemes,
   with `rf` operands (so `sig_quot_rec` is out, as ratified); after item 3.
6. *Records, spread, restrict, tags, `match`, methods* (7.8), as before.

*As built (stage 7.7e, `GoatCompleteCore.v`).* Stage 7.7e did the first of the four
items 7.7d listed: `infer_complete_core` is restated over live atoms. The even
derivations, `let` of a value and the conversion are not started; the list at the end
says what each needs.

**Live atoms.** The statement no longer asks the derivation's substitution `Sg` to
respect the sorts at every atom. It takes a finite set `L` of live atoms (the atoms the
context and the pending types mention) and asks `Live P L D D1 Sg`: on each atom of `L`,
`Sg` sends the atom to a type of the sort `D` gives it (read in `D1`) and that `P`
allows. Rows keep the full `rkres`, since the fragment has none. Four notions carry the
restatement.

* `limg s L`, the atoms of the images of `L` under a step `s`, computed from
  `AtomSetImpl.elements` so that membership is decidable (`limg_in`); `lnext s L T`
  adds the atoms of the result type.
* `SemL P L DT Sg n s D' n' S2`, the 7.6j step on `L`: `S2` respects the sorts and `P`
  on `limg s L`, `Sg` factors through `s` by `S2` at `teqD DT` on `L`, and the supply,
  step and row facts as before. It composes (`SemL_comp`, with the middle set a
  superset of `limg s L`, using `limg_scomp`/`limg_chain`), weakens past a fresh atom
  (`SemL_weaken`, `SemL_unfresh`) and restricts to a smaller set (`SemL_mono`).
* `GLive L G`, the context's types lie over `L`; `CI_stepL` and `next_facts` hand the
  next premise its context, live set and `CI` after a step.
* `Done P L D1 G e D n Sg T1` also returns `Live P (ftv T) D' D1 S2`, the sorts at the
  result type's atoms, which the caller adds to its live set.

**The unifier call (`unify_stepL`).** `unify_tD_rf_complete_img` wants a full `KR`.
`restr L Sg` is `Sg` on `L` and `Float` elsewhere; `Float` satisfies every sort (`sat` at
`typ_Float` is `True`; `Int` no longer does, since the `Quot` sort), so `restr L Sg` respects every sort, agrees with `Sg` on `L`
(`restr_in`, `apT_agree`) and has `Float` among its images. The unifier's extension `S2`
then sends every atom to an image of `restr L Sg` (`Img`), so `P` holds of all of `S2`
once `P typ_Float` and `P` on `Sg`'s live images do (`Img_bound`). This is `Img` relative
to an allowed set, inside `SemL`, as 7.7d asked, and no decision on membership in `L`
beyond `AtomSetImpl.mem` is needed (no classical axiom).

**`ctyping P`.** The derivation carries the allowed set: `C_Abs`, `C_Num`, `C_App`,
`C_ToFloat`, `C_Arith` and `C_Cmp` require `P` of the type they invent (the ones the
induction sends a fresh atom to with `supd`). `ctyping_typing` forgets `P`. The closed
case takes `P := fun _ => True`, `L` empty and `Sg = sid`, and its conclusion changes from
`KR D d_any S2` to `Live` on the atoms of the returned type plus `rkres`: the full
`KR` is no longer a consequence, and no caller needed it. With `L` empty the odd
atoms in `sid`'s images are no longer in the way of `P := EvT`.

*As built (stage 7.7f, `GoatCompleteCore.v`, `GoatCompleteCtx.v`, `GoatCompleteDrk.v`,
`GoatCompleteMono.v`, `GoatCompleteLet.v`).* Stage 7.7f did items 1 and 2 of 7.7e's list
except the renaming to even atoms: `ctyping` carries schemes and a `let` of a value, and
`infer_complete_core` proves it.

**`ctyping Av`.** `ctyping` mirrors `ntyping` on the core: each rule hands its premises
the same `bg` set, `C_Var` takes an instance of the context's scheme whose images are
`PEv` (`instP`), and `C_Let` is `N_Let` with `rf T1`. `P` is now fixed: `PEv T` is
`EvT T /\ rf T`, so the derivation's instances and invented types are record-free and
over even atoms. Record-free is what makes `teqD` an equality on everything the
induction compares (`teqD_rf_eq`), which the avoid argument below needs.

**The context carries schemes (`GoatCompleteCtx.v`).** A binding is a monotype or a
scheme `gen_ren` made (`SOk`: well formed, no quantified row, record-free body).
`CI` relates it to the derivation's binding by `teqD` or by `SchI`: `sch_leP` (`sch_le`
on instances whose images are `PEv`) against the algorithm's scheme read at the
substitution with its quantified odd atoms fixed (`sfix`). `SemL` also carries
`OkS s`. Three more invariants ride along: `LEv L` (live atoms are even), `RA D` (every
row variable of the algorithm's environment has the trivial kind), and `Avoid B L Sg`
(the images of live atoms mention only atoms in `B`, the set `ntyping` hands the node).

**Rows.** `unify_tD_rf_drk` (`GoatCompleteDrk.v`): a record-free unification makes no
row variable and changes no row kind. With `RA D`, `rkres` holds at any environment, so
the `let` premise's environment, which re-sorts only type atoms, needs no transfer
lemma for rows.

**`let` of a value.** The premise runs at the derivation's extended environment; the
live atoms' images avoid the generalized atoms, so `Live` moves between the two
environments (`Live_env`, `CI_env`, `SemL_env`). `gen_mono` is restated over what it
uses (`sch_leP`; the quantified atoms fixed; the live images `PEv`), and the body runs
with the extension that fixes the quantified atoms, over the live atoms that are not
generalized. `var_sch_done` is the variable case at a scheme: the extension sends the
fresh instance atoms to the derivation's instance.

**What remains of 7.7.**

1. *Even derivations.* A top-level renaming of a `typing` derivation to even atoms.
   `PEv` must hold of each type a rule invents and of each instance, which is a
   statement about every type in the derivation, not its conclusion. The bound on the
   derivation's atoms that an injective `typing_ap` needs is not stated anywhere; the
   conversion may instead rename on the way down, extending a finite partial renaming
   at each premise.
2. *The conversion* `typing` -> `ntyping` -> `ctyping` for core terms. `C_Let` takes
   `rf T1` and `PEv` instances: a derivation that gives a function a record type
   before generalizing is outside it. `letrec` and records are 7.8.
3. *`let` of a value at a monotype* (`T_LetMono` on a value): the derivation's monotype
   is an instance of the algorithm's scheme, which needs `sch_leP` against `sch_mono`.
4. *`letrec`, records, spread, restrict, tags, `match`, methods* (7.8), as before.

*As built (stage 7.7g, `GoatCompleteConv.v`).* Stage 7.7g did items 1 and 2 of 7.7f's list
for the monomorphic core: the even renaming while descending, and the conversion into
`ctyping`. A `let` of a value is not converted.

**Record-free derivations are a hypothesis.** `typing` lets a derivation choose a record
type for a call's parameter, an operand or a bound variable of a core term (`(fun g => 1)
(fun x => x)` types with `g : {l: Int} -> {l: Int}`), and `ctyping` takes `PEv`, which
includes record-free, at every type a rule invents. Renaming atoms cannot remove a
record, so the conversion's input is the class `rtyping`: the monomorphic core with
`rf` at each invented type. `rtyping_typing` shows it is a restriction of `typing` at
`d_any`. Converting every `typing` derivation of a record-free program would erase the
records of the derivation's inner types, which is not a substitution of atoms; it
belongs with 7.8, where records enter the fragment. DECISION NEEDED: whether 7.8
proves that erasure or extends `ctyping` past `rf`; chosen here: the class.

**Renaming while descending.** The kinding environment of a monomorphic core
derivation is `d_any` throughout, where every atom is sorted `Any`, so any atom map
respects the sorts (`kres_any`) and `rtyping_ren` renames a derivation, context and
all, by `rn g`. At a premise that introduces a type, `swap_even` takes the finite
swap `mk_rename_even` gives for the type's atoms outside the context's and the
judgement's own, and `rtyping_ctyping` renames the premises by it. The renamed
premises are new derivations, not subderivations, so the induction is on the size of
the term (as in `typing_normal`). A binder's premise is renamed per fresh name.

**Record division.** No exclusion remains. `R_Arith` takes `sat d_any (generic_sort o) A`
with `A` record-free, which is the generic `Quot` case for `/`; a record operand is
outside `rf`, so `sig_quot_rec` never arises.

**`T_ConvD`.** `rtyping` has no conversion rule: at record-free types `teqD` is equality
(`teqD_rf_eq`), so a conversion changes nothing.

**What remains of 7.7.**

1. *`let` of a value in the conversion.* `C_Let` needs `rtyping` over a general
   environment (the premise lives at `extr (ext D V k) ..`), a scheme in the context
   and the instance of a scheme at each variable; the swap must fix the sorted atoms
   `V` and the body's context relates to the renamed `gen` by `sch_equiv`, which
   `typing_sch_equiv_ctx` gives for `typing` and is still to be proved for the class.
   `T_LetMono` on a value is likewise not covered.
2. *`typing` to `rtyping`.* Only for derivations that are record-free (above).
3. *`letrec`, records, spread, restrict, tags, `match`, methods* (7.8), as before.

*As built (stage 7.8a, `GoatCompleteHeld.v`).* Stage 7.8 is split; this is its first
piece, the completeness of the discharge of held equations. Records, projection, spread,
restrict, tags, `match` and `letrec` in the L3 induction are not started, and the list at
the end says what each needs.

**The discharge is the unifier iterated.** `dis` skips an equation whose presence is
already `Bool` and otherwise unifies the field variable with the value's type, so
`dis_complete` is `unify_tD_complete_full` down the list, carrying the remaining equations
through each step (`HOkC_step`, by `pkg_ap_T` and `pkg_fac_T`). Its hypothesis on an
equation `dis` unifies is `HEq Sg n h`: field and value are in the fragment (`pf`, `atT`,
`ps`) and `Sg` makes them one type (plain `teq`). The conclusion is the unifier's:
from some unifier fuel on `dis k` succeeds with `(s, D', n')`, and `Pkg Sg n s D' n' S2`
holds, so `Sg` factors through `s` by an extension that respects the environment `dis`
returns. `dis_top_complete` is the case `k = S (length H)`.
`infer_closed_elab_m_held` is the closed entry point: a `Stable` run of `infer gm` that
returns `(s, D, T, n, e', H)`, with `HOkC Sg n H` and `atT n T`, gives a `Stable` run of
`infer_closed_elab_m gm` returning `apT d T`, and `teq (apT Sg T) (apT S2 (apT d T))`.
The `gm` flag needs nothing from the proof: `infer_closed_elab_of_true` says a successful
speculating run is the closed run's answer, and `infer_closed_elab_of_false` that a
successful non-speculating run gives some answer (the speculating run may succeed with a
different one first). A spread-free program holds `nil`, for which `dis_top_nil` is the
identity and the core theorem already reads it.

**What `HEq` leaves out.** An equation that `Sg` solves only because it makes the
presence `Bool`, with the field and value types differing, is outside `HEq`; `dis` meets
it through the failure of `unify_tD` and then `clash_d`, `sat_b` and `rlacksD`, and proving
that branch needs the unifier's failure on a clash, not only its success. The hypothesis
list of statement A therefore keeps, for held equations: (i) the field of an equation
whose presence ends `Bool` is `teq` to its value (`HEq`'s last conjunct, which the first
half of `fld` and `field_blocks_absent` already assumed in a different form), and (ii) the
two W-stricter cases of the `gm` run recorded in the README (a function bound under a
parameter's row whose presence ends present and whose uses need two types; two such
`let`s of different outcome). Nothing in the list shrank: held equations made the
discharge a theorem about `dis`, not the first half of `fld`, which belongs to absent
entries (`ps`) and returns when `ps` is dropped.

*As built (stage 7.8b, step 1: what a step promises about the atoms it mentions,
`GoatCompleteEr.v`, `GoatCompleteSorts.v` and the files that carry `Pkg`).* The
plan's first step was to thread `Img` (the extension `S2` sends each atom to an image
`sT Sg z`) through `Pkg`. `Img` is false at `rewrite_row`: the fresh field variable
takes the field type of the entry that `req (sR Sg r) (Maybe l P0 T0 R0)` presents, a
type `teq` to a field of `Sg`'s image but not an image of any atom, and, because
`req_absf` makes the field of an absent entry free, a type that can mention atoms the
image does not. What `Live` and `Avoid` need is only a bound on the atoms, so the step
now promises `Cov` instead:

- `Bnd E F S` says the images `S` gives to types and rows mention only type variables
  satisfying `E` and row variables satisfying `F`; `Cov Sg S2` says `Bnd E F Sg` implies
  `Bnd E F S2` for every `E` and `F`. `Pkg` carries `Cov Sg S2`; `Pkg_comp` composes it
  (`Cov_trans`). The leaves that rename (`push_sort`, `push_sort_r`, the tail variable of
  `bind_row`) have `Img` and its row analogue `RImg`, and `Cov_of_imgs` reads them as `Cov`.
- `rewrite_row_var_canon` picks the canonical representative `erT` of the presented
  field, presence and rest: `erT` replaces the field of each absent entry by `Unit`
  (`GoatCompleteEr.v`), is `teq` to its argument (`er_teq`), mentions no atom its argument
  does not (`er_sub`), and mentions the same atoms for `teq` types (`er_inv`, by
  induction on `teq` and `req`). So the fresh variables' atoms lie in `ftv_row (sR Sg r)`
  and `frv_row (sR Sg r)`, and `rewrite_row_spec` and `rewrite_row_complete` return
  `Cov`. The presence is present (`is_abs P0 = false`), which also rules out the case
  where the row variable lacks the label; the statement it replaces gave the three
  equalities `apT S2 P' = P0` and so on, which the canonical choice weakens to one
  `req` of the rebuilt entry.

With `Cov`, an invariant of the form "every image mentions only even atoms" or "only
atoms in `B`" survives a step: apply `Bnd` with `E` the even atoms, or the members of `B`.

*As built (stage 7.8c, step 1: the step past record-free types, `GoatCompleteLive.v`,
`GoatCompleteRfRows.v`).* Three of the four items the list below named are done; the
induction itself is not rebuilt.

- *`Quot` (option A, ratified).* `NN D S` covers the sorts `Numeric` and `Quot` (`NQ`), and
  `Drow` drops its `Quot` conjunct. `pkg_bind_prop_nl` takes `Quot` (a `Quot` atom is bound to
  `Float`, never `Int`, never a record), the two `NN` proofs push through `nq_old`, and the
  var-var case of the unifier meets a `Literal` atom against a `Quot` atom with `meet_float`
  (`lit_quot_float`, `Pkg_float`, `Pkg_meet`): the two images are one type that is both
  `Literal` and `Quot`, which is `Float`. Record division is excluded from completeness as a
  stated hypothesis; option B (a `Quot` atom bound only to rows of literal entries) is a
  follow-up.
- *Live row variables.* `RLive LR D Dd S` (a live row variable goes to a row of its kind) and
  the row half of `BndL` replace the global `rkres` of `SemL`, and `restrG L LR Sg` sends the
  other row variables to the empty row (`rkok_empty`), so `KR_restrG` needs nothing off the
  live sets. The allowed set of images `P` becomes two predicates `E` (type atoms) and `F`
  (row variables) on the atoms an image mentions: the extension renames, so a bound on atoms
  survives a step (`Cov`, `Bnd_restrG`) where "the image is record-free" does not. `limgT`
  and `limgR` are the atoms of the images of the live type atoms and row variables.
- *Live presence atoms.* `PLive LP S` says `S` sends the presence atoms `LP` to `Unit`;
  `psA LP T` (the presence of each entry is `Unit` or an atom of `LP`) gives `ps S T`
  (`psA_ps`), and `PLive_step` carries it through a step: the image of a presence atom is
  `Unit` or a variable the extension sends to `Unit` (`pres_shape`), so `limg s LP` is again
  presence atoms. `PLive_fresh` adds a fresh one.
- *The step.* `unify_stepG` is `unify_stepL` on `unify_tD_complete_full`: from `LiveG`, `pf`
  types over live atoms and rows with every entry present under `Sg`, and `teq` images, it
  returns the unifier's run and a `SemG`. `SemG` is `SemL` with `SIg` (the live images are in
  the fragment, atoms below the new supply, entries present under the extension), the
  factoring on live atoms and rows at plain `teq`/`req`, and `CovL` (a bound on the live
  images of `Sg` survives). `SemG_id`, `SemG_comp` (with the one hypothesis `Hm`, that
  `Sg`'s bounds reach the first step's end on the larger live set the second step reads) and
  `SemG_fresh` with `LiveG_fresh` are the structural lemmas the cases use. `DoneG` is `Done`
  over the fragment: the run's `SemG`, `pf`/`atT`/`ps` of its type, and `HOkC` of the held
  equations it returns; `DoneG_const` is the constants case.

*As built (stage 7.8e, partial, `GoatCompleteBound.v`).* The bound-transfer lemma and
the step lemmas the rebuilt induction needs are proved; the induction itself is not
rebuilt, because the rebuild runs into two obstacles the earlier notes did not see.

- `er_ap_sub`: if `pf T` and every entry of `T` is present under `S` (`ps S T`), the
  representative `erT (apT S T)` mentions every atom that `erT (sT S x)` mentions for a
  variable `x` of `T`, and every atom that `erR (sR S r)` mentions for a row variable `r`
  (rows are the second half of the statement). With `er_inv` this moves a bound across a
  conversion. `AvoidE B L LR Sg` is `Avoid` stated on representatives (type atoms of live
  atoms and of live row variables); `AvoidE_limg` and `AvoidE_next` are the two steps the
  induction takes with it, `AvoidE_mono`, `_sub`, `_empty`, `_fresh` and `_agree` the
  structural ones. They replace `Avoid_limg` and `Avoid_next` and use `teqD_rf_eq` nowhere.
- `SemW` is `SemG` without its last clause, the bound that a bound on `Sg`'s live images
  survives (`CovL`). That clause cannot compose: the second step's live set holds the atoms
  of the first step's result type, which are not images of live atoms (a fresh numeral atom
  is sent to whatever the derivation chose), so `SemG_comp`'s hypothesis `Hm` fails for an
  arbitrary bound. `AvoidE` carries the bound the induction needs. `SemW_of_G`, `_id`,
  `_fresh`, `_mono`, `_weaken`, `_unfresh`, `_comp`, `_live_ap`, `_factor` and the lnT/lnR
  pair (`lnT s L LR T`, `lnR s L LR T`: the live type atoms and row variables handed on)
  are the structural lemmas the cases use, with `LR` threaded beside `L`.

*As built (stage 7.8f, `GoatCompleteSchT.v`, `GoatCompleteMonoT.v`, `GoatCompleteCtxT.v`).*
Item 1 of the list below is done; the induction is not rebuilt.

- `sch_leT Pt D sd sa` compares schemes up to conversion. `instT Pt` is `instP` with the
  image class `Pt` in place of `PEv` (`instT PEv` is `instP`), and `sch_leT` says: the free
  atoms of the algorithm's scheme, read on the representatives `erT` and `erR`
  (`ftv_schE`, `frv_schE`), are free in the derivation's, and every instance of the
  derivation's scheme, in an environment that agrees with `D` on those atoms, is `teq` to an
  instance of the algorithm's. It has refl, trans, `_inst`, `_env`, `_ext` and `_extr`, and
  `sch_leP_T` embeds `sch_leP` on record-free schemes.
- `gen_monoT` is `gen_mono` for it. The derivation's type `T1` is only `teq` to the image
  `apT S2 T'`; with `pf T'` and `ps S2 T'` the representatives of the images of `T'`'s
  variables lie inside the representative of the image (`er_ap_sub`, now also on row
  variables of the representatives: `er_ap_sub_frv`), which `er_inv` moves to `T1`
  (`vis_of_ps`). The witness for a quantified atom is the image of its representative, so the
  instance the proof builds differs from the derivation's only inside absent fields, and
  `ap_cong_on` and `teq_ap` show the two instances `teq`. The image class `Pt` is a
  parameter closed under `erT`, `typ_Var` of even atoms and `ap_typ`, so both `PEv` and
  evenness with local closure fit.
- `frozenE` is `frozen` on representatives (`frozen_E`, `frozenE_pin`). `gen_mono_letT`
  restates `gen_mono_let` (`let_frozenT`, `let_pin_frozenT`: a pinned variable's image is a
  number type or a `Literal` variable, which the representative of the image mentions).
- `CIT` is `CI` over `sch_leT`, with a monotype binding compared at plain `teq`. `CIT_env`
  needs no environment hypothesis on monotypes. `CIT_frozen` reads `frozenE Sg G G1` off
  `CIT` given `GPsT Sg G` (well formed schemes whose bodies are `pf` and whose entries are
  present under `Sg` with the quantified atoms fixed) and evenness of the images. `SchIT_inst`
  is the scheme step of `var_sch_done`.

*As built (stage 7.8g, `GoatCompleteCtxW.v`, `GoatCompleteCoreW.v`).* The core's induction is
rebuilt on `SemW`, `LiveG`, `AvoidE` and `CIT`, and the old `SemL`, `CI`, `Done`,
`unify_stepL`, `unify_stepL_G` and the unifier's record-free induction
(`unify_tD_rf_complete_img` and its wrappers) are gone.

- `SemC L DT Sg n s D' n' S2` is a `SemW evA evA L {} DT Sg n s D' n' S2` (no live row
  variable), together with two facts the record-free core reads off a conversion: the step
  sends each live atom to a record-free type, and `Live PEv (limg s L) D' DT S2` holds. A
  convertible pair of record-free types is equal (`teq_rf_eq`), so these two facts are what
  replaces `teqD_rf_eq`. `SemC_id`, `SemC_fresh`, `SemC_unfresh`, `SemC_comp`, `SemC_env`,
  `SemC_agree` and `SemC_sid_after` are the calculus of `SemL`, over `SemW_id`, `SemW_comp`
  and the rest; `unify_stepC` is `unify_stepG` read at record-free types (`rf_back`,
  `unify_tD_rf_rr`).
- `CI_stepW` is the step on `CIT`. A scheme's bodies `apT (sfix q S2) (apT s body)` and
  `apT (sfix q Sg) body` are `teq` by `ap_factor` (`sfix_step_teq`), and `sch_leT_conv` moves a
  `sch_leT` across two schemes with the same quantifiers and `teq` bodies, because `er_inv`
  fixes the atoms of the representatives. `CIT_ftv` is `CI_ftv` over representatives (the
  bodies and images are record-free, so `erT` is the identity: `er_rf`).
- `DoneW` returns the run's step as a `SemC`, `TOk n' T`, `EvT T`, `Live PEv (ftv T)` and
  `teq (apT S2 T) T1`. It does not return `HOkC`: the run holds no equation (its `infer` result
  ends in `nil`), `DoneW_frag` states the `pf`/`atT`/`ps`/`HOkC S2 n' nil` facts of the type, and
  the `let` of a value needs only `dis_nil`. `var_sch_doneT` is `var_sch_done` from
  `SchIT_inst`; `gen_mono_letT` closes the `let`.
- `infer_complete_core_closed` keeps its statement. Its `rkres` conclusion replaces the
  extension's row substitution by the empty row, which satisfies every row kind.

*As built (stage 7.8h, partial, `GoatCompleteCtxP.v`).* The invariants of the core's
induction are generalized past `rf`; the induction itself is not yet rebuilt on them.

- A step needs no new definition: `SemW evA evA L LR` already carries `pf`/`atT`/`ps` of the
  images of the live atoms and the live row variables (`SIg`), and `LiveG evA evA` carries
  their evenness. `DoneP` is `DoneG` with `SemW` in place of `SemG` (which does not compose,
  7.8e) and returns `HOkC` of the equations the run holds; `DoneP_const` is its constants
  case and `DoneP_of_DoneW` embeds the record-free core's conclusion, so the record-free
  theorem will be a corollary of the rebuilt induction rather than a second proof.
- `sfixS sc S` fixes the atoms and the rows `sc` quantifies (`sfix` fixed only atoms). The
  derivation's substitution is `restrG`-shaped off the live sets, so it sends a quantified
  row to the empty row; `SchIP` and `CIP` compare through `sfixS`. `sfixS_step` is
  `sfix_step_teq` for atoms and rows: on the body's atoms and rows `Sg` is the extension after
  `s` up to conversion, because `OkS s` fixes what is odd and the images of live atoms and rows
  are even.
- `SOkP`/`GOkP` (well formed scheme, `pf` body, free atoms and free rows below the supply),
  `GLiveP L LR` (free atoms in `L`, free rows in `LR`) and `GPsP Sg` (each body's entries
  present under `sfixS sc Sg`) replace `SOk`/`GOk`/`GLive`/`GPsT`, with `GOkP_of_GOk` as the
  embedding. `SOkP_apS` keeps a binding inside them under a step; `ps_stepP` moves the
  presence of a body's entries along the step with `ps_pull`; `CI_stepP` is `CI_stepW` on all
  four, and `next_factsP` is `next_factsW` with the row sets `lnT`/`lnR`.

*As built (stage 7.8i, partial, `GoatCompleteVarP.v`).* `var_sch_doneP` is the variable case over the
fragment, concluding `DoneP`. It takes the derivation's instance unpacked (`st`, `sr`, with the
sorts, kinds and evenness `instT` records) and `teq T (ap_typ st sr (apT (sfixS sc Sg) body))`.
`fsubP` is `fsub` for atoms and rows. `SemW_ext` is the identity step to a larger environment and
substitution.

- Under `GPsP` an instance re-holds nothing. `GPsP` asks `apT (sfixS sc Sg) P = Unit` for every
  entry's presence `P`, and `sfixS` sends a quantified atom to itself, so no entry's presence is a
  quantified atom; `rh_t` then returns the instance unchanged (`rh_none_mut`) and `DoneP`'s `H` is
  `nil`. The brief's re-held equations with fresh field variables cannot occur under this invariant.
- DECISION NEEDED: a generalizing `let` of a record with a presence atom outside the context
  would quantify that atom, and `GPsP` fails for the new scheme. Either `GPsP` skips entries whose
  presence is quantified (then `rh_t` does re-hold, and the derivation's instance must send the
  quantified presence to `Unit`, which `instT` does not record), or the `let` pins such atoms.
- DECISION NEEDED: `instT`/`sch_leT` do not record that a quantified `Numeric`/`Quot` atom is not
  sent to a record (`NNL`), nor the kind of each quantified row; `var_sch_doneP` takes both as
  hypotheses. They belong in the class `Pt` or in `sch_leT`.
- DECISION NEEDED: `HOkC` does not step along a `SemW` (it needs `Pkg`), because an equation's
  atoms need not be live (a re-held equation's value atoms may occur only in the equation).
  Proposal: return the type packed with the equations' types (`ftv`/`frv` of the pack are the
  live set), so `next_factsP` and `SemW_factor` apply unchanged.

**What remains of 7.8.**

Stage 7.8d did the unifier half: `unify_stepG` (`GoatCompleteLive.v`) gives the step in every
case that unifies, and 7.8g's `unify_stepC` reads it at record-free types. `SemG_fresh_row`
and `LiveG_fresh_pres` (`GoatCompleteLiveRf.v`) are the row-variable and presence-atom
analogues of `SemG_fresh`.

1. *Schemes over the fragment* (done in 7.8f).
2. *The induction past `rf`.* Done: the context invariants and their step (7.8h,
   `GoatCompleteCtxP.v`). Left:
   - `var_sch_doneP`: done for the instance that re-holds nothing (7.8i); the quantified-presence case waits on the decisions above. Originally: a variable at a scheme that quantifies rows and presences. It differs
     from `var_sch_doneT` in three places: `instantiate` also gives the quantified rows fresh
     variables (`inst_den` and the row half of `fsub`, with `rkok` of the derivation's rows), the
     run returns the equations `rh_t (inst_pres sc n)` holds (one `Heq` per entry whose
     presence is a fresh quantified presence, with a fresh field variable the extension sends
     to the entry's field), and `HOkC` of them is the `HEq` clause at that extension.
   - The `ctyping` of `GoatCompleteCore.v` rebuilt over the fragment: `PEv` becomes `EvT` with
     `pf`, `rf T1` in `C_Let` becomes `pf`, and the `Live PEv` and `TOk` clauses of the cases
     become `LiveG evA evA` and `pf`/`atT`/`ps`. Each existing case then reads `SemW` for
     `SemC` (the rf facts `SemC` adds are the part that goes) and `next_factsP` for
     `next_factsW`; `DoneW` becomes `DoneP`, and a general `let` discharges the held equations
     it receives with `dis_complete`.
3. *Constructs* (next). Record literal and projection (`C_Rec`, `C_Proj` over `ps` types, rows with
   a tail variable by `rewrite_row_complete`; the projection's row unification is
   `unify_tD_complete_full`), spread (`spread_present`'s equation, discharged by `dis_complete`
   at a `let` or the top), restrict, tags and `match` (`spn` is a lemma), then `letrec` through
   `V_letrec`'s shape. `ctyping` extends past `rf` (ratified) instead of proving an erasure.
4. *The conversion from `typing`.* Unchanged from 7.7g, extended with the new rules; it also
   chooses the presence atoms of `PLive`.
5. *`Quot` on records.* Option B, above.

## 5. Staged PR plan

Sizes are estimates in lines of Coq (Rust or YAML where stated), counting churn in
the files a signature change touches. Stages 7.1 to 7.4 change the rules or W and
are gated by ADR 0037 (they change `GoatDefs.v` or `GoatInfer*.v` and carry
proofs); 7.10 is independent of all of them.

| Stage | Content | Size | Depends on |
| --- | --- | ---: | --- |
| 7.0 | this note | docs | none |
| 7.1 | Tighten `T_Let` with the pin premise; audit every other rule for a side condition looser than the checker (`T_Letrec`'s sort function `k`, `T_Num`, `T_Spread`'s presence, `T_Match`'s defaults) and record the audit in the README; re-prove the substitution lemma and W's `let` case against the premise | ~250 | none |
| 7.2 | Row kinding environment (`rden`: a sort on each row variable, `Eq` and a set of absent labels), covering #564 and Q4-B together: extend `sat`, `kres`, `inst` and `casch_inst` to row variables; `T_Spread` and `T_Restrict` use `lacks` of a row variable; W carries the sets in `rewrite_row` | ~1,300 | none |
| 7.3 | Sort propagation, #623: `unify_t`, `unify_r`, `unify_k` and `unify_co` return the updated environment; adds the five hand-written programs to the corpus | ~900 | 7.2 (they share the row environment) |
| 7.4 | `sat_b` is complete: `sat_b D k T = true <-> sat D k T`, adding the `mu` and `Grp` cases, so the stub is gone; the corpus reader's tag programs run through it as phase 3's corpus work lands | ~350 | 7.2 (the iff covers row tails) |
| 7.5 | L0 and L1: fuel monotonicity, `ctx_le`, `typing_ctx_le`, `gen_mono` | ~1,150 | 7.1, 7.3 |
| 7.6 | L2: types, rows with scoped labels and presence, sorts (mu-free) | ~2,000 | 7.3, 7.5 |
| 7.7 | L3 for the core: variables, constants, `program`, call, `let`, `letrec`, `if`, operators, comparison | ~1,500 | 7.6 |
| 7.8 | L3 for records, spread, restrict, tags and `match` | ~1,200 | 7.7 |
| 7.9 | Close statement A: `infer_complete_plain`, the corollaries, `GoatAssumptions.v` (the list grows by 1), the README and ADR 0037 amendment (what is proved, the section 3 table), the corpus skip counts, `make differential` unchanged | ~300 | 7.8 |
| 7.10a | Fuzz step 1: the driver's `--serve` mode, the `coq.yml` upload of the extracted W (section 7c) | ~200 | none |
| 7.10b | Fuzz step 2: the bolero target and the byte-driven generators | ~500 Rust | 7.10a |
| 7.10c | Fuzz step 3: the nightly job, the planted-divergence self-test, the allowlist, docs | ~150 | 7.10b |
| 7.11 | Statement B: knots, coercions and methods (section 6); optional, decided by owner question 1 | ~2,500 to 3,500 | 7.9 |

Order. 7.10a to c can start today and run beside everything else; they pay for
themselves early because the fuzzer finds gap classes the corpus does not. 7.1 is
first on the proof side (a rule change before any completeness lemma mentions the
rule). 7.2, 7.3, 7.4 are a chain: each leans on the row environment and the
reworked unifier signature of the one before. 7.5 can begin once 7.3's signature
is fixed. 7.6 to 7.9 are a chain. Total for statement A (7.1 and 7.2 to 7.9):
about 9,000 lines of Coq, of which the unifier lemmas (7.6) and the row
environment (7.2) are the risk. For scale: `GoatInferSound.v`, the whole
soundness proof, is 1,581 lines, and the whole W development is about 4,000.

## 6. Statement B: what the recursive types need

Statement A skips every program that needs a `mu`, which is the point of splitting
it off. Statement B needs three pieces beyond A:

1. **The unifier is complete for `unroll_eq`.** `unify_k_sound` says a successful
   run gives `s T1 ~~[m] s T2` for some `m`; completeness is the converse for
   some `m`, and it is not a routine extension. Unification of regular trees (the
   checker's equi-recursive types) is unitary (Courcelle 1983). The calculus's
   equality is the finite-budget iso-recursive one, `unroll_eq`, whose chains may
   unfold on either side. I know of no principal-type result for it, and the
   non-unitary case is real: a variable meeting a recursive type can bind to the
   knot or to its unrolling, and the two choices give incomparable elaborations
   when a coercion must follow. The stage opens with a spike (a pen-and-paper
   statement and a counter-example search over small terms, about a week) before
   committing lines. If the spike finds two incomparable principal candidates,
   statement B weakens to "W accepts, with a type of which some derivation's type
   is an instance up to `unroll_eq`", which keeps the typable-if-and-only-if
   corollary and drops uniqueness.
2. **`unroll_eqb` is complete** (or is replaced by a coinductive equality `T ~ T'`
   with `unroll_eq n T T' -> T ~ T'`, plus the reverse direction for guarded
   types): the bounded search W uses must find a chain whenever one exists.
3. **Coercions and methods.** `coerce_dec` produces exactly the head coercions a
   derivation has; `tie_obj` and `T_Obj`'s `meths_shared` agree on the shared
   receiver; `unify_grp` agrees with `T_Letrec` on a group.

Two residuals of stage 7.6d belong to this tier, ratified on the 7.6d review:
`nfT` does not go under `mu` or a tag group (a binder's body has bound indices
`rlacksD` cannot read), so an absent entry inside a recursive type or a tag
payload converts as plain `teq` does; and method literals and the members of a
recursive group still meet their slots through the plain `unify_t`, because a
method's type is related to its slot's by `unroll_eq`, which has no environment.
The group arm of `unify_tD` hands its payload to `unify_t` for the same reason, so
statement A's completeness for tag groups (the 7.6e adaptation) needs the plain
unifier's completeness beside the environment-reading one.

If the spike's result or the cost is bad, ADR 0037's amendment records that
completeness holds on the plain fragment (statement A) and is measured, not
proved, for recursive types, as decision 6 accepts. That is owner question 1.

## 7. The nightly fuzz differential

### 7a What it compares

Programs a fuzzer generates, through the Rust checker and through the extracted
W, with the same oracle the per-PR corpus uses: acceptance, and for an accepted
program the inferred type up to renaming of variables (the driver's existing
comparison, a bisimulation with assumed pairs for recursive types). A program
outside the fragment (the corpus reader's skips) is not compared. A program the
checker accepts and W rejects, or the reverse, or two types that differ, fails the
target.

### 7b Why a long-lived child process, not a file

Two designs were weighed.

- **Dump, then compare (rejected).** The bolero target writes each program's
  corpus line to a file; after the budget the OCaml driver reads the file. It is
  simple, but bolero's coverage guidance and shrinking see only the Rust side, so
  a disagreement is found after the run, unminimized, and the fuzzer never steers
  toward programs W is bad at.
- **A serve loop (chosen).** The bolero target spawns the extracted driver once, as
  a child process, and exchanges one line per program on its stdin and stdout. A
  disagreement panics inside `for_each`, so bolero minimizes the input and saves
  it under `tests/__fuzz__/<target>/crashes/` exactly like the existing targets,
  and the existing `Upload crashes` and `report` steps handle the rest. Cost: one
  pipe round trip per input (tens of microseconds), small against the checker.

### 7c Pieces

**The driver gets a `--serve` mode** (`differential/driver.ml`). It reads one line
in the corpus format (`MODE <TAB> SEXP <TAB> VERDICT`) and writes one reply:
`OK`, `SKIP <reason>` (a mode W's comparison skips, such as a recursive type W
refuses), or `MISMATCH <detail>`. The comparison code is the same function the
batch run uses. A watchdog (`Unix.setitimer`) turns a run longer than 10 seconds
into `SLOW`, which the target logs and does not fail on: a W that runs out of
patience is a different finding from a wrong answer, and the fuel (100,000) is
the proof's `exists fuel` made concrete.

**The extracted W reaches the nightly job as an artifact.** The nightly job runs
on `ubuntu-latest` (the existing exception to the self-hosted rule, which this
plan keeps) and cannot build the 1 GB Rocq switch. `coq.yml` already runs `make
-C proofs ci` on the self-hosted runner on every push to `master` that touches
what the proofs depend on, which is `proofs/`, `differential/`, `checker/`,
`prelude/`, `parser/`, `examples/` and the grammar. On a `push` to `master` it
uploads `proofs/_differential/goat_infer.ml`, `goat_infer.mli` and
`differential/driver.ml` as the artifact `goat-w-extracted` (OCaml source, not a
binary, so the runner's libc and architecture do not matter). The nightly job
downloads the latest such artifact with `gh run download` (needs `actions: read`),
installs `ocaml-nox` and `ocaml-findlib` with `apt`, and builds the driver with
`ocamlfind ocamlopt -package unix`. Staleness is bounded: any push that could
change what the checker or W does reruns the extraction, so the artifact always
matches the last such push. GitHub keeps artifacts 90 days; a repository quiet for
longer finds no artifact, and the step fails with a message saying to dispatch
`coq.yml` (a red nightly is the right outcome for a differential that cannot run).

**The target** `fuzz/tests/w.rs`, `differential_checker_vs_w`, joins the nightly
matrix. It reuses the corpus's reader by including the example with
`#[path = "../../checker/examples/core_corpus.rs"]` (the way `differential.rs`
already includes `cli/tests/support/mod.rs`), after making `line` visible: `line`
turns a source into `MODE <TAB> SEXP <TAB> VERDICT <TAB> SOURCE` or a `Skip`. Three
input sources, chosen by the first byte:

1. **The typed generator** (`TypedGen`, `GroupGen`, `SpreadGen` of the corpus),
   with their `Rng(u64)` replaced by a reader of the fuzz bytes, so the fuzzer
   mutates the choices and not a seed. Programs are mostly well typed, which tests
   the accept direction.
2. **`support::generate`** (the terminating well-typed generator the wasm
   differential uses) for programs with more variety of shape.
3. **A mutation** of a program from 1 or 2: delete, duplicate or swap a token, or
   replace a name or numeral. Most mutants the checker rejects, which tests the
   reject direction (W must reject too); many fail to lower and are skipped by the
   reader, which is the checker's own rejection before typing.

**What counts as a failure, during the proof and after.** The corpus already
carries the known classes as counted skips. The fuzzer reaches new programs in the
same classes, so the target starts with an allowlist keyed by the gap table of
section 3, each entry a predicate over the program and a reference to its stage:

| Allowed until | Class |
| --- | --- |
| 7.3 | the driver's `sort_gap.sh` classification: W refuses only because a sort does not reach an inner variable |
| 7.2 | W refuses only because a row variable has no sort |
| 7.4 | the program compares a tag group or `mu` type (W's `sat_b`) |
| 7.11 | a recursive-type program (`R` and `K` modes) W refuses |
| never (outside) | `SplitGroup`, and the corpus reader's other skips, which are not compared at all |

A stage removes its row when it lands, and the target then fails on that class.
Statement A closes with the plain-fragment rows gone, so any plain disagreement
after 7.9 is a bug the theorem says cannot be in W.

**Per-PR tier.** A bounded run needs OCaml and the artifact, so it stays out of
`cargo test` (the existing `fuzz_check.rs` and `fuzz_differential.rs` need neither).
A `coq.yml` self-test covers the harness instead, as `planted_divergence_is_caught`
does for the wasm target: `driver --serve --plant` flips one verdict and the self-test
requires `MISMATCH`, so the check cannot go vacuous. It also feeds a malformed line and
requires a clean error and not a hang.

**Corpus cache and issue reporting** work as for the other targets: the
`actions/cache` entry is keyed per target, and the existing `report` job opens or
bumps the `nightly-fuzz` issue on a failing leg. A crash the artifact makes
reproducible: the failing leg uploads the extracted sources beside the crash, so a
developer replays the input without rebuilding Rocq.

### 7d What it will and will not tell us

It finds W refusing, or typing differently, a program neither the corpus nor the
proof's cases thought of; it cannot find a mistake the corpus reader makes in the
same way for every program (the trusted bridges), and it adds nothing a proof of
statement A does not subsume for the plain fragment, which is why the allowlist
shrinks to the recursive-type classes. Its lasting job is statement B's gap, the
reader, and the Rust checker's changes after the proof closes.

## 8. Interactions

- **#606, #623, #564, #626.** Absorbed as stages 7.2, 7.3 and the section 3 table;
  closing them is part of 7.9's definition of done.
- **Phase 8 (parser).** Independent. `GoatShape.v` and the reader's fragment may
  grow as phases 3 and 8 land; each new term form adds cases to L3 (7.7, 7.8) and
  a generator weight in 7.10b.
- **ADR 0037 decision 6.** 7.10 is what makes "the fuzzer's programs nightly" true.
  The amendment in 7.9 states that completeness holds for the plain fragment and,
  if owner question 1 goes the cautious way, that recursive types stay measured.
- **`proof-gate`.** 7.1, 7.2, 7.3, 7.4 change `GoatDefs.v` or `GoatInfer*.v` and
  need no label: each changes `proofs/`. 7.10a to c touch no gated file (they edit
  `differential/`, `fuzz/` and workflows), so they need neither `proofs/` changes
  nor the `no-semantics-change` label; the `coq.yml` edit in 7.10a triggers the
  `coq` check's build, which is the check.

## 9. Owner questions

Nothing here changes which programs the language accepts: every stage either adds
a derivation the checker already accepts (7.2, 7.3, 7.4) or narrows the rules to
the checker's behavior (7.1, ADR 0038's addendum). Two questions remain, each
about scope or intent.

1. **Must statement B (recursive types and methods) be proved?** ADR 0037 decision
   2 says "complete for every program the rules accept". Statement A covers every
   plain program and costs about 9,000 lines. Statement B adds 2,500 to 3,500 and
   opens with a research spike whose result I cannot predict (section 6). Options:
   (a) prove A now, run B's spike, and prove B only if the spike is clean; record
   in the ADR amendment that recursive-type completeness is measured by the
   differential and the fuzzer until then; (b) require B before calling phase 7
   done. I recommend (a): A is the part with a known proof and the part ADR 0037's
   "tied to the Rust checker by differential testing" already covers for the
   rest.
2. **Is the checker's monomorphic use of a group member before the group's last
   member intended?** (`SplitGroup`, 65 corpus programs.) The checker types that
   use at the member's monomorphic type, as Haskell types a binding group's
   members inside the group; the reader's hoisted `letrec` types it at the
   generalized type, which is more permissive. If the checker is right, the
   calculus needs a rule for a `letrec` with value bindings between its members
   (a `T_LetrecSplit`, about 600 lines with its preservation case) or these
   programs stay outside the proofs, as the plan assumes. If the checker is wrong,
   changing it changes what the language accepts. I recommend leaving them
   outside and recording the gap, because a mutually recursive group split by a
   value binding is rare in the corpus (65 of 44,380, all from the group
   generator).

## 10. Risks

Most serious first.

1. **The row unifier proof (7.6).** Scoped labels make termination non-structural
   and the presence variable adds a case to `req`'s inversion. Mitigation: follow
   Leijen's proof, whose measure is known; if the inversion fights, restrict `T_Spread`
   and `T_Restrict` derivations to rows whose labels are distinct (the checker's
   rows never repeat a label, ADR 0033 decision 5) by adding that premise, a rule
   narrowing like 7.1's.
2. **7.2 and 7.3 churn.** Every `unify_*` statement and each caller in `infer`
   changes signature, across ten files, as phase 6 stage 1a already did. Mitigation:
   land 7.2 and 7.3 as separate PRs and keep the soundness proof green at each.
3. **Statement B is research.** Section 6. The split makes it a separate decision
   and a separate budget.
4. **The allowlist rots.** A predicate that matches too much hides a real bug.
   Mitigation: each predicate names the stage that deletes it, and the nightly
   counts allowlisted programs per class so a class that grows is visible.
5. **The artifact path is a second moving part.** If `coq.yml` skips the build
   (nothing relevant changed) the artifact is the last one built, which is correct;
   if the 90-day retention lapses the nightly goes red with instructions. Cheaper
   than a second Rocq install on a hosted runner.
6. **Fuel as a stand-in.** The theorem says `exists fuel`; the driver's 100,000 is a
   guess. The `SLOW` and fuel-exhaustion counts in the nightly report say when it
   is too low.

**Record `/` after the principality decision (2026-11-23).** The `quot_ty` rule
above made a verdict depend on unification order (`(program(a) do a / a done)({x:
1.0})` was refused). `/` is now decided like `+`: its operands share one fresh
variable of the sort `Quot`, so `quot_ty` and `float_head` are gone, `sig_quot`
takes the sort, and the checker's `type_division` joins the operands
(`join_operands`). See ADR 0012 and ADR 0038 (amendments).
