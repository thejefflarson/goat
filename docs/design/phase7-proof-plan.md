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
  absent with different field images (`field_blocks_absent`, triaged above: the
  checker refuses it too).
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

**What remains of 7.6.**

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

**Alternatives that lost.** Prove completeness against a separate declarative
principal-type system and show it equivalent to `typing`: it doubles the rule
set and the equivalence needs the same lemmas. Replace W with a constraint-based
inferrer whose completeness is easier: it throws away the soundness proof and the
tie to `infer.rs`, which is W-shaped. Prove completeness only for a decidable
subset of `typing` by a size bound: nothing in `typing` is bounded.

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
