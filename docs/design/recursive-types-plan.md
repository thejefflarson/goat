# Iso-recursive types in the calculus: design pass

Status: DECIDED and implemented in #488 (ADR 0037 amendment, 2026-11-20). The owner accepted every recommendation below: Q1 A, Q2 A, Q3 B, Q4 A, Q5 A, Q6 E3, Q7 A, Q8 A, Q9 no parser work, Q10 C with A as the intended reading. Sections 2 to 6 are the design as drafted; section 7 records what the implementation changed and what phase 3 needs from it. Issue #488, part of #435, governed by ADR 0037 (decision 3) and ADR 0038. Written against `master` at 590d6b5 (PR #485, the kinding environment `D`, is merged). Reads the phase-3 note (`docs/design/phase3-proof-plan.md` on `ticket/452-phase3-design`, Q5 and risks). The spike is `docs/design/spikes/MuSpike.v`.

## 1. What the checker does today

- `Ty::Rec(binder, body)` is a named binder over `TypeVar` ids, equi-recursive: a type equals its unrolling. `unfold` is `body[binder := self]`; `unify_ty` unfolds a `Rec` at the head and keeps a set of assumed pairs so unification terminates.
- Knots are tied by the occurs check (`tie_ty_knot`, `tie_row_knot`). A mention is guarded (`Guard`) when it sits under a variant payload, or under both a record field and a function type (ADR 0032 decision 1). `x(x)`, `{a: x}` with no function, and unguarded cycles stay rejected.
- Recursive variants (`mu t. Empty | Link({0: a, 1: t})`) and recursive records (`mu t. {moved: (t) -> t | r}`, the receiver of ADR 0034 methods) use the same `Ty::Rec`. Values are acyclic (ADR 0034 decision 5); recursion lives only in types.
- A knot's body can contain a free row variable `r`, and the checker's unifier may solve `r` to a row that mentions the knot's own binder. Under a binder that is the "mention carries the binder in its prefix" case (ADR 0032, known hole).

## 2. Calculus additions (draft, subject to section 3)

### 2.1 Syntax and the binder

`typ` gains `T ::= ... | mu T | bv n`: the first binder inside `typ`. Free type and row variables stay atoms and `ap_typ` stays a total-map substitution.

Binder encodings weighed (Ott 0.34 was run on each in a scratch directory; only the output shapes are reported):

| Encoding | What Ott generates | Cost |
| --- | --- | --- |
| E1: `mu a. T (+ bind a in T +)` with `typvar` made `repr-locally-nameless` | `typ_Var_b`/`typ_Var_f`, `open_typ_wrt_typ`, cofinite `teq_mu` | renames every `typ_Var` (about 85 sites in 15 files); `teq_mu` is cofinite, see below |
| E2: a second metavar `muvar` bound by `mu` | `typ_MVar_b`/`typ_MVar_f`, cofinite `teq_mu` | a stray free constructor `typ_MVar_f` that needs a "never occurs" invariant; no substitution to reuse |
| **E3: de Bruijn index written into the grammar** (`typ_Bvar n`, `typ_Mu T`, no `bind` clause), `open_typ` and `lct` hand-written in `GoatDefs.v` | two new constructors, plain congruence `teq_mu : teq T T' -> teq (Mu T) (Mu T')` | about 30 lines of hand-written open/lc; Ott's lc/open for types unused |

Why E3 (recommended, not decided): with a cofinite `teq_mu` (E1, E2), the type-substitution lemma `teq_ap` needs, in the `mu` case, a fresh atom `a` with `st a = typ_Var a`. `st` is an arbitrary total map in today's files (`GoatSubst.v` `teq_ap`), so every lemma that reaches `T_Conv` would gain a finite-support hypothesis, or a renaming detour. I did not mechanize that failure; it is reasoned from the rule shape. E3's `teq_ap` case is the same congruence as `arrow` (spike `teq_ap_mut`, no hypothesis on `st`).

Effect on existing definitions (all mechanical):

- `ftv_typ`, `frv_typ`, `ap_typ`: `Mu T` recurses, `Bvar` is empty/identity. `ftv` of a mu is `ftv` of its body, since the bound variable is an index, not an atom.
- `gen`, `inst`, schemes: unchanged. A scheme's quantified atoms are free atoms; a mu-bound variable is never quantified.
- Local closure `lct k T` (computable, like `lc_at`) becomes a premise of `T_Fold` (or a regularity lemma); `lc_sub st sr` (every `st a` has no free index) becomes a hypothesis of the substitution lemma.
- Files that match on `typ`: about 100 `typ_Record` sites across 13 files (`GoatDefs`, `GoatMeta`, `GoatSubst`, `GoatSound`, `GoatRows`, `GoatInfer*`, `GoatPhase*`) each gain `Bvar` and `Mu` cases. `GoatInfer*` can answer "no" on `Mu` (the algorithm never infers one), keeping soundness.
- Parser fragment: no impact. `mu` has no surface syntax.

### 2.2 Terms and rules (draft)

```
e ::= ... | fold e | unfold e            v ::= ... | fold v

T_Fold    lct 0 (mu T),  G |- e : T[mu T / bv 0]   =>   G |- fold e : mu T
T_Unfold  G |- e : mu T                            =>   G |- unfold e : T[mu T / bv 0]
teq_mu    T ~= T'  =>  mu T ~= mu T'     (no unrolling equation: that is what "iso" means)
bvar      bv n ~= bv n

ST_UnfoldFold   unfold (fold v) --> v
ST_Fold1, ST_Unfold1   congruence
gen_value (fold v) when gen_value v
```

`D` and sorts (ADR 0038): the bound variable has no atom, so it has no sort. A mu type satisfies only the `Any` sort (`sat` falls into the `_ => k = k_Any` case), which is right: a recursive type is never `Numeric` or `Literal`. Substituting `mu T` for `bv 0` goes through `open_typ`, not through `kres`, so the substitution lemma's sort side conditions are untouched. A free row variable inside a mu body keeps whatever sort treatment rows have today.

### 2.3 How mu is exercised before phase 3

Variants and tags are not in the calculus yet. Records are, and a record type is recursive through a function type exactly in ADR 0032's receivers:

```
P    = mu t. {moved: (t) -> t; x: Int; nil}
ball = fold {moved: program(s) do s done, x: 1}        : P
step = program(p) do (unfold p).moved(p) done          : (P) -> P
```

`(unfold p).moved(p)` passes the receiver explicitly (ADR 0031). So phase 3's worked examples for mu are records with a method-shaped field, plus the vacuous `mu t. t` (typed, has no value). Phase 3 adds variants, where lists are `mu t. <Empty: Unit; Link: {0: a; 1: t}; nil>`: tag and `match` rules need nothing from mu except that `Link(x, xs)` is `fold`ed by elaboration and `match` scrutinizes `unfold xs`. Phase 3's `Delta` (tag signature) mentions closed payload types, which may now include `bv n` under a mu; `Delta` stays stable under `ap` because closed types contain no free atoms.

### 2.4 Lemmas that change

| Lemma | Change |
| --- | --- |
| L1 (`teq`/`req` equivalence, congruence) | new `teq_mu`, `teq_bvar` constructors; reflexivity gains two cases |
| L2 (`teq_shape`, head tags) | `thead_tag` gains two tags; new `teq_Mu_inv` (spike) |
| L4/L5 `typing_tsubst_gen_mut` | new `ap_open` (spike `ap_open_mut`), `ap_lc`; two typing cases |
| L6a/L6b term substitution | one congruence case per new term |
| canonical forms (L7) | new: a closed value whose type is `~=` a mu is a fold (spike `canon_mu`) |
| progress / preservation | cases for fold, unfold, `ST_UnfoldFold` (spike) |
| `typing_regular`, `gen_value`, `step_gen`, `is_gen_subst` | one case each |

## 3. Decisions the owner must make

Each is a semantics, proof-model or theorem-statement question. The recommendation is mine and decides nothing.

### Q1. Fold and unfold: explicit terms, or coercions the elaborator inserts?

```goat
xs = Link(1, Empty)        # calculus: fold (Link ...) : mu t. <Empty | Link: {0: Int, 1: t}>
length = program(l) do match l do ... done done   # calculus: match (unfold l) ...
```
- **A. Explicit `fold e` / `unfold e` terms** with typing rules and a reduction `unfold (fold v) --> v`. A real term form; progress and preservation cover them; the spike proves exactly this.
- **B. Typing-level coercion only**: `mu T` and `T[mu T/0]` are interconvertible in a rule (`T_Roll`), no term, no reduction. That is the equi-recursive rule restricted to one step; `teq` inversion is no longer syntax-directed in the types of values, and the elaboration theorem has nothing to insert.
- **C. Fold/unfold built into constructors and destructors**: `Link(..)` folds, `match` unfolds, no standalone terms. Smallest term syntax, but records (no constructor or destructor) have nowhere to fold.

Recommend **A**: ADR 0037 decision 3 says "explicit fold and unfold", and C cannot cover recursive records.

### Q2. Does `fold` carry its type?

- **A. Unannotated** `fold e` (typing is declarative: any `mu T` whose unrolling matches). Terms stay type-free, so type substitution acts on judgments only. A term can have several types, as with `float(e)` today.
- **B. Annotated** `fold [mu T] e`: terms mention types, so `ap` must act on terms and the substitution lemma gains a term traversal.

Recommend **A**. The spike uses it.

### Q3. Contractiveness (guardedness): which `mu` types does the calculus admit?

```goat
mu t. {moved: (t) -> t}      # checker: accepted (field + function)
mu t. <Empty | Link: t>      # checker: accepted (tag)
mu t. (t) -> t               # checker: rejected (x(x))
mu t. t                      # checker: rejected; vacuous
```
- **A. No restriction.** Soundness needs none (spike: preservation and canonical forms never use it). The rules accept `mu t. (t) -> t`, which types the untyped lambda calculus' self-application through fold/unfold, so the rules accept programs the checker rejects. The later completeness theorem (ADR 0037 decision 2) is stated against the rules; extra accepted programs do not break the checker-sound direction but make "the checker matches the rules" false in the other direction.
- **B. A `guarded` predicate on `mu` bodies mirroring `Guard`** (a bound index reached through a variant payload, or through both a record field and a function type), a premise of `T_Fold`. Faithful to ADR 0032, at the cost of the predicate and its preservation under `open` and `ap`.
- **C. Variant payloads only; recursive records excluded.** Contradicts ADR 0032/0034.

Recommend **B**, with the predicate stated on the index form. If the owner prefers a cheaper first cut, **A** is sound and B can be added later without changing the metatheory, only the premise.

### Q4. Where does the elaboration theorem land?

ADR 0037 decision 3: every program the checker's algorithm accepts elaborates, by inserting folds and unfolds, into an iso-typed program with the same behaviour.
- **A. Stays in phase 5**, as the ticket text says. This ticket proves the calculus sound only.
- **B. A statement-only version here**: define the elaboration relation and write the theorem as a comment-level statement in the docs. No Coq statement, since `_CoqProject` allows 0 admits.
- **C. Prove it here for the checker-free fragment**: the calculus' own equi-recursive typing (a model of the checker's `unfolds_to`) elaborates into the iso calculus.

Recommend **A**. The theorem needs variants, methods and the algorithm model, none of which exist yet; one specific obstacle is recorded under risks (item 2).

### Q5. Type equality under mu

- **A. Congruence only** (`mu T ~= mu T'` when `T ~= T'`): iso-recursive; `mu t. {x: t}` and its unrolling are different types. Spike proves inversion and `teq_open`.
- **B. Add alpha-equivalence of bound names**: not needed with indices.
- **C. Add folding equations** (`mu T ~= T[mu T/0]`): equi-recursive; contradicts ADR 0037 decision 3 and loses syntax-directed inversion.

Recommend **A** (B is vacuous under E3).

### Q6. Binder encoding

See section 2.1: **E3** (index in the grammar, hand-written `open`/`lct`, structural `teq_mu`) versus **E1** (Ott binder on `typvar`, cofinite rule, finite-support hypothesis on substitutions) versus **E2** (separate `muvar`). Recommend **E3**. E3 sidesteps Ott's generated lc/open for types, so Ott no longer documents the binder; `goat.ott` (typeset) can still state `mu a. T` by name.

### Q7. Do sorts (ADR 0038) cover a mu-bound variable?

- **A. No sort; a mu type is `Any`-sorted** (it satisfies only `k_Any`). Follows from E3: the bound variable is an index.
- **B. Allow a sorted mu variable** (`mu t:Numeric. ...`): meaningless, since a mu type is never numeric.

Recommend **A**. Unfolding substitutes a type, so `kres` is not involved.

### Q8. Algorithm W

- **A. Follow-up ticket** (like #483): W never infers a mu; its soundness is preserved by failing on `Mu`; completeness for recursive programs waits for the elaboration theorem.
- **B. Inside this ticket.**

Recommend **A**.

### Q9. Parser fragment

None expected: no surface syntax for mu, fold or unfold. Confirm that no grammar change in this ticket means the `proof-gate` job needs a `no-semantics-change`-style waiver only if the checker is touched (it is not). Recommend **no parser work**.

### Q10. Recursive records: what is the type of an open-extensible receiver?

```goat
ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}
big = {...ball, size: 10}; big.moved()      # ADR 0034 decision 3
```
- **A. Polymorphism through the scheme**: `ball : forall r. mu t. {moved: (t) -> t; x: Int | r}`, instantiated at `r := {size}`; the elaborator unfolds, spreads, and refolds at the new type. Works with no calculus feature beyond mu and rows; relies on `ball` being generalized (a value, ADR 0027).
- **B. Row-polymorphic fields** (a field whose type is itself `forall r.`): rank-2; the owner has closed that (memory: no type annotations, rank-2 won't-do).
- **C. Out of scope until phase 5** (methods, `self`).

Recommend **C** for the rules and **A** as the intended reading; the spike covers a record inside mu (rows under the binder) but not row-variable instantiation at the mu.

## 4. Spike result

`docs/design/spikes/MuSpike.v` compiles under Rocq 9.1.1 with **0 admits and no axioms** (`Print Assumptions` prints "Closed under the global context" for `typing_tsubst`, `preservation` and `progress_unfold`). It is a stripped calculus with the real shapes: mutual `typ`/`row`, atoms substituted by total maps, a de Bruijn `mu`, locally nameless terms with fold and unfold. It proves:

- `ap_open_mut`: substitution commutes with unrolling (needs `lc_sub`: substituted types have no free index). This is the hardest lemma; it closed in a dozen lines once `open_closed` and `lc_mono` were in place.
- `teq_ap_mut`: no finite-support hypothesis on the substitution.
- `teq_open`: type equality respects unrolling in body and argument; `teq_Mu_inv`.
- `typing_tsubst`: the type-substitution lemma through `T_Fold` and `T_Unfold`.
- `canon_mu`, `preservation` (for `unfold (fold v) --> v` and the congruences), `progress_unfold`.

What the spike does not cover: schemes, `D`/sorts and `gen` (argued in 2.2, not mechanized), `letrec`, `T_Let` freshening, term-substitution (L6), the full `teq_shape` for rows, row-variable instantiation inside a mu body, and contractiveness (Q3). The E1/E2 failure of `teq_ap` is reasoned, not run.

## 5. Size estimate

Calibrated against phase 1 (+2630/-645, 37 files) and phase 2 (+1279, 25 files).

| File | Change | Lines |
| --- | --- | --- |
| `goat_ln.ott`, `goat.ott`, `Goat_ott.v` | `bv`, `mu`, `fold`, `unfold`, `teq` rules, values, steps | 80 |
| `GoatDefs.v` | `open_typ`, `lct`, `lc_sub`, typing and step rules, `gen_value` | 120 |
| `GoatRows.v` | `thead_tag`, `teq_Mu_inv`, `teq_open` | 80 |
| `GoatSubst.v`, `GoatBij.v`, `GoatHM.v` | `Mu`/`Bvar` cases, `ap_open`, `ap_lc` | 150 |
| `GoatMeta.v` | `lc`, regularity, canonical forms, progress | 150 |
| `GoatSound.v` | L4/L5/L6 and preservation cases | 250 |
| `GoatInfer*.v` | `Mu`/`Bvar` cases only (algorithm fails on them) | 120 |
| `GoatPhase3`-style examples (`GoatRecTypes.v`) | recursive record, vacuous mu, a ill-typed fold | 200 |
| `docs/semantics.md`, README, ADR 0037 amendment | prose | 200 |
| **Total** | | **~1350** |

If Q3 is B, add about 150 for `guarded` and its closure under `open` and `ap`. The parser fragment is untouched.

## 6. Risks and dead ends

1. **Churn, not difficulty.** About 100 `typ_Record` sites in 13 files each gain two cases; budget build time.
2. **Row variables inside a mu body (elaboration theorem, phase 5).** The checker's unifier can solve a row variable inside a knot to a row that mentions the knot's binder (ADR 0032's multi-prefix hole). A locally closed substitution cannot express that, so the elaborator must fold at the right type rather than substitute. This is the likeliest dead end of the elaboration theorem; it does not threaten this ticket's soundness.
3. **Cofinite binder trap (E1/E2).** Choosing Ott's binder makes `teq_ap` need finite-support substitutions across the whole development. Choose the encoding before any port work.
4. **Phase-2 repeat.** If a guard predicate (Q3) or `Delta` is added after the first lemma is written, statements change. Fix Q3 first.
5. **Without Q3 restriction**, the rules type self-application; soundness still holds (spike), but the later completeness statement must say "the rules accept more than the checker".
6. **Interaction with `Delta` (phase 3):** payload types may now contain indices under a mu; `Delta` lemmas must use `lct`-closedness, not "no free variables".

## 7. As built, and what phase 3 needs

The implementation follows the recommendations; where it differs from the draft:

- **Guarded recursion (Q3 B)** is `gd r f k T` in `GoatDefs.v` on the index form: `r` and `f` record whether the traversal has passed a record field and a function type, and an index `k` is reachable only when both hold. Both `T_Fold` and `T_Unfold` take `guarded B` as a premise, so `mu t. (t) -> t` has no `fold` and no `unfold`. The predicate is closed under substitution (`guarded_ap`) and under `teq` (`guarded_teq`), the second so a conversion cannot dodge it. The spike did not cover it; it cost about 40 lines.
- **Substitution needs closed images.** The draft said `lc_sub st sr` becomes "a hypothesis of the substitution lemma". In the real development it is part of `inst` (a generic instance), of `tr_supp` (and so of the algorithm's `OkS`), and of `casch_inst`, because a generic instance, a renaming and an algorithm substitution each feed `typing_tsubst_gen_mut`. Algorithm W stays sound by never binding a variable to a type with a free index (`occT` and `occR` check `lcb`), which never fires on a type the algorithm builds; `fold` and `unfold` are rejected outright.
- **Guard and rows.** A row variable under a `mu` body is untouched by the guard (it has no index), so `mu t. {moved: (t) -> t | r}` is guarded and the open-extensible receiver of Q10 is expressible; its rules wait for methods.
- **Size.** About 1000 lines added and 80 removed in 29 files under `proofs/`, against the draft's 1350 to 1500 (the draft counted an `Infer` rewrite that the closed-index occurs check made unnecessary). Much of the churn is in files that case on `exp` (the parser, printer and denotation proofs each gained a case for `fold` and `unfold`) and in threading `lc_sub`.

### What phase 3 needs from this (the `Delta` hooks)

Phase 3's tag signature `Delta` maps each tag to a payload type. With `mu` in the calculus:

1. **Closed payloads are `lct 0`-closed, not variable-free.** A payload under a `mu` mentions an index (`mu t. <Empty | Link: {0: a, 1: t}>` has the payload `{0: a, 1: #0}` under the binder). A `Delta` lemma that says "the payload has no free variables" is wrong; it must say `lct k` for the depth the tag is read at. `Delta` is stable under `ap` when its payloads are closed in this sense and `lc_sub` holds, by `ap_lc`.
2. **A variant payload guards on its own.** `gd` gains one case, a payload (a tag's argument) sets both flags, exactly as ADR 0032 has it. `guarded_ap` and `guarded_teq` extend by one case each.
3. **Tags and `match` need nothing else from `mu`.** `Link(x, xs)` is elaborated with a `fold` and `match` scrutinizes `unfold xs`; that is the elaboration theorem, phase 5. In the calculus a list value is `fold(Link ...)`, and `canon_mu` plus the variant canonical form give the shape of a closed value of `mu t. <...>`.
4. **`teq` and `thead_tag`.** A variant type adds a head tag and an inversion lemma next to `teq_Mu_inv`; `teq_mu_shape` is a template.
5. **The sorts.** A variant type satisfies only `Any`, like a `mu` (`sat` falls into the `k = k_Any` case).

### Follow-ups opened by #488

- Algorithm W for `mu` (Q8): infer `fold` and `unfold` where the checker's equi-recursive types need them. Opened as an issue mirroring the generic-operator follow-up.
- The elaboration theorem and the open-extensible receiver (Q4, Q10): phase 5.
