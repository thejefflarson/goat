# Algorithm W and iso-recursive types: design pass

Status: DRAFT for the owner's decision. Issue #497 (part of #435), governed by ADR 0037 (decisions 2 and 3, and the 2026-11-20 amendment) and ADR 0032. Written against `master` at decace4 (#498, iso-recursive types in the calculus, is merged). It builds on `docs/design/recursive-types-plan.md`. The spike is `docs/design/spikes/KnotSpike.v`. Nothing in `proofs/`, `checker/` or the ADRs changes in this PR.

Terms used throughout. **W** is the Coq model of inference (`infer`, `infer_closed_env`, extracted to OCaml for the differential test). A **mu type** is `typ_Mu B`, a recursive type whose body `B` refers to itself by a de Bruijn index (`typ_Bvar 0`). **Unrolling** is `open_typ 0 (typ_Mu B) B`, the body with the whole mu put in place of the index. **Iso-recursive** means a mu and its unrolling are different types, and the terms `fold(e)` and `unfold(e)` convert between them. **Equi-recursive** means they are the same type, which is how the Rust checker treats `Ty::Rec`. A **knot** is what the checker builds when a variable would have to equal a type that mentions itself: it solves the variable to a recursive type (`tie_ty_knot`, `tie_row_knot` in `checker/src/infer.rs`). **Elaboration** is ADR 0037 decision 3: rewrite a program the checker accepts into one with explicit folds and unfolds that the iso rules accept.

## 1. What W does today

- **Terms.** `infer` has no case for `e_fold` or `e_unfold`; both fall to `None`.
- **Types.** `unify_t` has cases for the base types, `typ_Var`, `typ_Arrow` and `typ_Record`. A `typ_Mu` or `typ_Bvar` on either side falls to `_, _ => None`, except that a variable may be bound to a mu type if the mu is closed.
- **Occurs check.** `occT a T` is true when `a` is free in `T` or when `T` has a free index (`lcb 0 T` is false). So W never binds a variable to a type with a loose index, and every substitution it builds has closed images (`lc_sub`), which the substitution lemmas need. When `a` occurs in `T`, W fails; it does not tie a knot. The checker does.
- **Soundness.** `infer_closed_sound`: every type W returns is derivable by `typing` in the returned kinding environment. This holds today with the two changes above and needs no work for #497.
- **Completeness.** Not proved for any feature, with or without mu. ADR 0037 decision 2 states it as a goal; `GoatInferSound.v` proves only the sound direction. This note states what completeness would say but does not depend on it.
- **Differential test.** `checker/examples/core_corpus.rs` writes a type only for `Int`, `Float`, `Str`, `Unit`, `Bool`, `Var`, `Func` and plain `Record` rows; its `ty` function returns `None` on anything else, including `Ty::Rec`, and the program is skipped. The recursive programs the checker accepts (`step = program(p) do p.moved() done`) are also outside the fragment for another reason: dot calls, `self` and tags are skipped. I did not count how many corpus programs the checker types with a `Rec` today; the README does not say, and the answer matters for decision 1.

### Why W cannot simply infer an `unfold`

Take a receiver written with an explicit argument (ADR 0031's `(r.f)(x)` escape), in goat:

```goat
step = program(p) do (p.moved)(p) done
```

The checker gives `p` the type `P = mu t. {moved: (t) -> s | r}` (`s` the result, `r` an open row; expected from `structural_recursion.rs`, I did not run this exact program). Elaborated into the calculus:

```goat
step = program(p) do ((unfold p).moved)(p) done      # step : (P) -> s
```

W walks `unfold p` with `p : a` for a fresh variable `a`. To type it, `a` must become `mu B` for some body `B`, and the result `open B (mu B)` must come out equal to what `.moved` needs, `{moved: (a) -> s | r}`. So the unknown is a body with a hole under a binder, a second-order unknown, and first-order unification cannot bind it. Recovering `B` from the result means abstracting every occurrence of `mu B` back to the index, which is exactly what `tie_ty_knot` does with its `plug` function. Two consequences:

1. W cannot check an *unannotated* `unfold` on a lambda-bound variable. Either the site names its mu type, or W discovers the mu by tying a knot while unifying, and the folds and unfolds are *output*, not input.
2. Whichever route is chosen, `a` is solved by `knot a T`, and the lemma that makes that solution right is in the spike.

## 2. The options

### Option A. Check an elaborated program: the fold and unfold sites carry their mu type

W's input is the elaborated, fold-annotated program (what the reader of the differential test would write, as it writes `float(e)` today). Each site names its mu type; W checks it.

Where the annotation lives is a sub-choice:

- **A1. In the calculus**: `fold[B](e)` and `unfold[B](e)`. Reverses #488's Q2 (A, unannotated). Type substitution then acts on terms, and every file that cases on `exp` (parser, printer, denotation proofs; #488 touched about 29 files) gains the type field.
- **A2. In a side table**: `infer` takes a function `hint : exp -> option typ` keyed by the argument of the fold or unfold. No change to the calculus. Two sites whose argument is the same term but whose mu types differ cannot be told apart; the reader then skips that program.

An annotation's free variables are not W's variables (the checker's type variables mean nothing to W), so each site renames them to fresh variables, as `instantiate` does for a scheme, and unification relates them through the terms that flow between sites. A shared `s` and `r` at two sites become equal when `p` flows from one to the other and `unify_t` compares `mu B1` with `mu B2` by comparing the bodies.

Example, the same `step`:

```goat
step = program(p) do ((unfold[P] p).moved)(p) done     # P = mu t. {moved: (t) -> s | r}
```

Theorem it proves (A2 form, with `H` the hint function):

```
infer_closed_sound_at : forall H fuel e D T,
  infer_closed_env_at H fuel e = Some (D, T) -> typing D nil e T.
```

Lemmas it needs:

- `unify_t` gains `Mu`/`Mu` (unify the bodies) and `Bvar n`/`Bvar n` (equal indices). Soundness is congruence: `apT s (typ_Mu B) = typ_Mu (apT s B)`, which is `ap_typ`'s own clause.
- `guarded_b`, a decidable check of `guarded`, with `guarded_b B = true -> guarded B`. The `T_Fold` and `T_Unfold` premises are `lct 0 (typ_Mu B)` and `guarded B`; W must test both on the renamed annotation. `lcb` already decides the first.
- A renaming lemma: the fresh-variable renaming of an annotation has closed images, so `guarded_ap` and `ap_open` apply (`lc_sub` for a renaming is `lc_sub_id`-shaped).
- The new `infer` cases for `e_fold`/`e_unfold`, through the existing `infer_sound` induction, reusing `typing_ap_G`.

Differential-test change: the reader of `core_corpus.rs` writes the elaboration itself. For each node whose checker type is a `Rec` where the context expects the record (or the reverse) it inserts `fold`/`unfold` with the `Rec` printed as a mu type; `ty` gains a `Rec` case (binder id to de Bruijn index) and the s-expression grammar gains types inside terms. `driver.ml` compares W's type with the checker's, as now. A program whose mismatch lies deeper than the head (see the dead-end below) is skipped and counted.

Size: about 3 PRs, 900 lines. A1 adds another 400 lines of churn across the `exp` matchers.

Dead ends and costs:

- **Throwaway.** Option B's W is a different algorithm. Of A's work only `guarded_b` and the `Mu`/`Bvar` unifier cases are reused.
- **The reader becomes an elaborator**, untrusted and unproved, and the differential test then checks the reader and W together. A disagreement says "something is wrong" and no more.
- **Deep mismatch.** An equi-recursive unifier equates `mu B` with a record `R` by unfolding at the head, and then equates their components, which may again be one side `mu B` and the other an unrolled record. The checker's resolved types do not rewrite the unrolled record back into the mu. Reconciling them in the iso calculus needs a coercion under a function type, which is an eta-expansion (`program(y) do f(fold y) done`), not a single fold at a use site. Option A would show how often this arises (the reader counts the programs it skips) but cannot fix it.
- **Annotations with a row variable inside the knot** (plan section 6 item 2): the reader may not be able to write the annotation at all, and those programs are skipped.

### Option B. W infers the mu: unification ties the knot, mirroring `tie_ty_knot` and `tie_row_knot`

W's input is the fold-free program, exactly what the checker sees. When `unify_t (typ_Var a) T` finds `a` free in `T`, W does not fail. If every mention of `a` in `T` is guarded (under a record field and a function type, `gd`), it binds `a := knot a T` where `knot a T = typ_Mu (abs_typ a 0 T)` and `abs_typ` replaces `a` by the index (the spike defines it). The row knot, where the cycle is a row variable's mention with a given prefix, is the same with `abs_mention` in place of `abs_typ`.

Example, the same `step` with no annotation (`p.moved` forces `p : {moved: (a) -> s | r}`, so unifying `a` with that record finds `a` inside it, and W ties the knot):

```goat
step = program(p) do (p.moved)(p) done      # W infers (mu t. {moved: (t) -> s | r}) -> s
```

For the soundness theorem, W's result type is not derivable for the fold-free term (the iso rules need the fold and unfold), so the statement is relative to elaboration:

```
infer_closed_sound_mu : forall fuel e D T,
  infer_closed_env fuel e = Some (D, T) ->
  exists e', erase e' = e /\ typing D nil e' T.
```

where `erase` deletes `fold` and `unfold`. Two ways to get `e'`: W returns it (W outputs an elaborated term, with coercion placeholders resolved once the final substitution is known), or it is only proved to exist. The first is constructive and is what ADR 0037 decision 3 means by "elaborates"; the second is easier to state and harder to prove, since the proof must build `e'` anyway.

Lemmas it needs:

- **Knot lemma** (the spike): `open_typ 0 (knot x T) (abs_typ x 0 T) = ap_typ (sub1 x (knot x T)) idr T`. The solution `x := knot x T` makes `x` and `T` differ by exactly one unrolling.
- `knot_lc`: `lct 0 T -> lct 0 (knot x T)`, so the solution is closed and `lc_sub` is preserved.
- `abs_guarded`: if every mention of `x` in `T` is guarded, `guarded (abs_typ x 0 T)`, so `T_Fold` and `T_Unfold` apply.
- `abs_no_x`: the body no longer mentions `x`, so the substitution terminates and mirrors the checker's `!occurs(x, &body)`.
- An **equi-recursive equality** `~~` (the least congruence containing `mu B ~~ unrolling`), stated by a bounded unrolling relation or coinductively; and: if `unify_t` succeeds with `s` then `apT s T1 ~~ apT s T2`. This is the unifier's new specification.
- The **coercion lemma**: if `T ~~ T'` through knot steps, a term of type `T` can be coerced to `T'` by folds and unfolds. At the head it is one `fold` or `unfold` (spike `knot_fold_types`, `knot_unfold_types`). Under a function type it is an eta-expansion. This lemma is the heart of the elaboration theorem and is not spiked.
- The row-knot version of the knot lemma and of `abs_guarded` (variants make it common).
- Re-proving `infer_sound` with the new unifier specification and the output term.

Differential-test change: small. The reader does not elaborate; W takes the same fold-free terms it takes today. `ty` gains a `Rec` case (binder to de Bruijn index; guarded `Rec` only, else skip), and `driver.ml` compares W's mu type with the checker's. Because de Bruijn indices have no names, "equal up to renaming of variables" stays what it is today; but the *shape* of a knot must agree: both solve `x := mu v. T[x := v]` abstracting every mention, and the row knot abstracts only the mentions with the same prefix, so the corpus should include row-knot cases early to catch a mismatch.

Size: about 6 PRs, 2500 to 3500 lines. Rough breakdown: knot lemma, `abs`, guarded and the unifier with its specification (1 to 2 PRs); equi-recursive equality and the coercion lemma (1 to 2); W returns the elaborated term and the soundness restatement (1); the row knot and variants (1); reader and driver (1).

Dead ends and costs:

- **The deep-mismatch eta problem** above is the likeliest dead end, and it is the elaboration theorem's. A mitigation to examine: canonicalize types so that every node's type is its mu form wherever the checker's unifier assigned a knot, which makes every mismatch head-level. Whether the checker's resolved types allow that is the question Option A's skip count would answer.
- **The row variable inside a knot** (plan section 6 item 2). When a row variable `r` already sits inside a formed `mu B` and later unification solves `r` to a row that mentions that very mu, the solution is cyclic through a mu that already exists: `r = R[(mu B[r])]`. `abs_typ` handles a knot over a *free* variable at any depth (it goes under binders with `S k`), but this case needs a binder shared between two mus, which a single `abs_typ` does not give. W's occurs check refuses it (`None`); the checker ties it. This is the residual incompleteness of W; it is the multi-prefix hole of ADR 0032. I did not build a goat program for it.
- **Fuel and termination.** The checker caps knots (`MAX_KNOTS_PER_UNIFY`); W's `unify_t` is fuel-bounded already, so a knot step must also spend fuel.

### Option C. W stays `None` on fold, unfold and every mu; completeness is stated relative to the mu-free derivations

No algorithm change. Add one lemma, `infer_mu_free : infer ... = Some (..., T, ...) -> mu_free T` (W never produces a mu, so the incompleteness is stated exactly), and state completeness, when it is proved, for derivations in which no `typ_Mu`, `e_fold` or `e_unfold` appears. The differential test counts, rather than silently drops, the programs whose checker type has a `Rec`, and `differential/README.md` says W is incomplete on them.

Theorem: `infer_mu_free` above, plus soundness, unchanged.

Differential-test change: a counter in `core_corpus.rs` for programs skipped because the checker's type is recursive, printed to stderr and required to be non-negative; the README gains a paragraph. About 100 lines.

Size: 1 small PR, about 150 lines.

Dead ends: none. It does not meet the ticket's "infers `fold` and `unfold`" and leaves the question for the elaboration theorem.

## 3. The spike

`docs/design/spikes/KnotSpike.v` compiles against master's `proofs/` (`coqc -R proofs Goat`, Rocq 9.1.1) with **0 admits and no axioms** (`Print Assumptions` prints "Closed under the global context" for `knot_fold_types`, `knot_unfold_types` and `abs_no_x`). It imports the real `GoatDefs`, `GoatRows` and `GoatMu`, uses the real `ap_typ`, `open_typ`, `lct`, `gd`, `guarded` and the real `T_Fold` and `T_Unfold`, and proves the tie-a-knot step of Option B for a type variable:

| Lemma | What it says |
| --- | --- |
| `abs_lc` | replacing an atom by an index keeps a type locally closed, one binder deeper |
| `open_abs` (the hardest) | unrolling the abstracted body at a closed `U` equals substituting `x := U` |
| `knot_unrolls` | the corollary: `open_typ 0 (knot x T) (abs_typ x 0 T) = ap_typ (sub1 x (knot x T)) idr T` |
| `abs_guarded` | if every mention of `x` is under a record field and a function type, the body is `guarded` |
| `abs_no_x` | the abstracted body has no free `x` |
| `knot_fold_types`, `knot_unfold_types` | `T_Fold` and `T_Unfold` give one `fold`/`unfold` between `x` and `T` once `x := knot x T` |

The hardest lemma is `open_abs`: it holds because `U` is closed (no shifting under binders, the same reason `ap_open` needs `lc_sub`) and because `T` has no index at or above the depth where `abs_typ` puts one. It closes in a dozen lines. What the spike does not cover: the row knot (`tie_row_knot` abstracts a *mention*, a record or variant with a prefix, not an atom); the equi-recursive equality `~~` and the coercion lemma (where the eta problem lives); the unifier specification and the changed `infer_sound` induction; fuel.

## 4. Recommendation

**Option B is the destination; do Option C now; do not do Option A.**

- B is what ADR 0037 decision 3 asks for: the checker stays equi-recursive and needs no annotations, and W models the checker's own knot-tying. A's W is a different algorithm that annotates what the checker never sees.
- Option B's differential change is small because the reader does not elaborate, while A's makes the reader an unproved elaborator.
- Today's calculus has records and functions only, so the only programs in the differential fragment that tie a knot are explicit-receiver forms like `(p.moved)(p)`. Dot calls, `self` and tags are skipped, and tags are where knots arise in practice (lists). Building B before variants means writing the row-knot lemma twice. Schedule B with the variants and elaboration phase (ADR 0037's phases 4 and 6), where the knot lemma is stated once for the type knot and the row knot.
- Option C costs one small PR now and makes the gap visible and counted.

The spike supports B: the type-variable knot is a short, assumption-free lemma against the real rules, so the unifier half of B is not the risk. The risk is the coercion lemma and the row-variable-in-a-knot case, both in the elaboration theorem, and neither is answered by this note.

## 5. Decisions for the owner

1. **Does W infer a mu?** (a) Yes, by tying knots, over the fold-free program (Option B); (b) only checks a program that carries its mu types (Option A); (c) neither for now (Option C). Recommendation: (c) now, (a) later.
2. **When?** Before variants (the knot lemma is then written for types only and again for rows), or with the variants-and-elaboration phase (written once). Recommendation: with that phase.
3. **If Option B: does W return the elaborated term, or only a type with an existence statement?** Returning the term is constructive and matches ADR 0037 decision 3 ("elaborates"). Recommendation: return the term.
4. **If Option A: annotate in the calculus (A1, reverses #488 Q2) or in a side table (A2)?** Recommendation: A2, if A at all.
5. **What equality justifies the unifier?** An equi-recursive `~~` defined by bounded unrolling (decidable, matches the checker's assumed-pairs set) or coinductively (simpler statement, harder proof). Recommendation: bounded unrolling.
6. **The deep-mismatch eta problem.** Accept that the elaboration inserts eta-expansions under function types, or require a canonical form (every node typed in its mu form) and skip programs that need more? Recommendation: first measure it with a reader prototype that counts the programs needing it; do not decide in advance.
7. **The row variable inside a knot (plan section 6 item 2).** Stay incomplete there (W returns `None` where the checker ties a knot), say so in the README, and make the differential driver treat "checker accepts, W refuses on a cyclic row" as a known skip; or extend the model with a shared-binder mu. Recommendation: stay incomplete and count the cases.
8. **Differential reporting.** Whatever else is chosen, count and print the programs skipped because the checker's type is recursive (Option C's change). Recommendation: yes, now.
9. **Does the ticket stay one ticket?** #497 as written ("infers `fold` and `unfold` terms and `mu` types, prove soundness, extend the differential test") is Option A or B. Recommendation: close #497 into the Option C PR plus a new ticket "W ties knots (Option B)" blocked by the variants phase.
