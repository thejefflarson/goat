# ADR 0037 — The proofs cover the whole language, and CI blocks a feature without one

- Status: accepted (2026-11-13)
- Amends: ADR 0030 ("the parser is verified for the core fragment only"), ADR 0032
  §5 ("neither proof route is needed now").
- Context: issue #435. `proofs/goat.ott` and `goat_ln.ott` define the core
  calculus; `proofs/GoatSound.v` proves `progress`, `preservation` and
  `soundness` for it with 0 admits; ADR 0030's T1–T3 verify the parser for the
  same fragment.

## Context

The core calculus has numbers, booleans, n-ary functions, let-generalization,
and records as scoped-label rows with construction and projection. Everything
else goat ships is outside it: Unit, strings, `if`, arithmetic, comparison,
recursion, the value restriction (ADR 0027), tags, variants, `match`, lists,
spread update-or-extend (ADR 0033), inferred recursive record types (ADR 0032),
methods and `self` (ADR 0034), dot calls on any receiver (ADR 0031) and
structural ordering (ADR 0036). The proofs say nothing about any program that
uses them, which is nearly every program a kid writes.

A completeness proof (decision 2) would have caught the method-chaining refusal
(#432) before merge: the checker rejected programs its own rules (ADR 0033) say
are well typed.

## Decision

1. **Scope: the whole language.** Every construct in `grammar/goat.peg` is in
   the calculus, with its typing rules and a small-step semantics. Out of scope:
   reference counting and memory layout (Perceus), mono and codegen
   correctness. Those are compiler-correctness claims, not type-system claims.
2. **Two theorems per feature.**
   - **Soundness of the rules.** A program the typing rules accept can't get
     stuck (progress and preservation), as `GoatSound.v` proves for the core.
   - **The checker matches the rules.** A formal model of the checker's
     inference algorithm is sound (every type it infers is derivable from the
     rules) and complete (it infers a principal type for every program the
     rules accept). A checker that refuses a well-typed program, as in #432,
     breaks completeness.
3. **Recursive types are iso-recursive in the calculus, with an elaboration
   theorem.** The calculus has `mu a. T` with explicit fold and unfold. The
   checker keeps its equi-recursive types (a type equals its unrolling), which
   need no annotations. The theorem that aligns them: every program the
   checker's algorithm accepts elaborates, by inserting folds and unfolds, into
   a program the iso-recursive rules accept, with the same behaviour. That is
   where the checker and the proof meet, and the checker-model proof of
   decision 2 is stated over that elaboration.
4. **Hard gate in CI.** Once this ADR is accepted:
   - the `coq` workflow runs on every PR, not only on PRs that touch
     `proofs/` (a PR that touches nothing it builds finishes in seconds), and
     becomes a required check on `master`, because a path-filtered required
     check never reports on other PRs and blocks them;
   - a `proof-gate` job, also required, fails a PR that changes
     `grammar/goat.peg`, the checker's typing (`checker/src/infer.rs`,
     `lower.rs`, `ty.rs`) or the prelude's language surface without changing
     `proofs/`, unless the PR carries the `no-semantics-change` label and its
     body says why (for example a diagnostic-wording change);
   - a PR that changes the grammar, a typing rule, or the evaluation semantics
     must update the `.ott` files, `docs/semantics.md` and the proofs in the
     same PR, with 0 admits (`make -C proofs ci`, `EXPECTED_ADMITS = 0`);
   - the existing gaps are a backlog worked in the phase order below; until
     a phase lands, a PR that touches a construct in it must close that phase
     first. A change that only rejects more programs for a host reason (for
     example ADR 0035's "the model can't hold a plain function") is outside the
     calculus and not gated.
5. **Phase order**, each phase a ticket that ends with both theorems for its
   constructs and the parser fragment extended to match:
   1. Unit, strings, `if`, arithmetic, comparison of base types.
   2. Recursion and the value restriction.
   3. Tags, variants, `match`, lists.
   4. Spread update-or-extend with presence variables.
   5. Iso-recursive types, the elaboration theorem, methods, `self`, `.` and
      `::` on any receiver. (Amended 2026-11-20, below: the calculus half of
      iso-recursive types moves ahead of phase 3.)
   6. Structural ordering as a typed primitive.
   7. The algorithm proof for the core (decision 2's second theorem), then
      extended phase by phase; and the parser over the full grammar.

6. **The proven algorithm is tied to the Rust checker by differential testing.**
   The algorithm proof of decision 2 covers a model of inference written in
   Coq. That model is extracted to an executable and run against
   `checker/src/infer.rs` on the whole test corpus in CI and on the fuzzer's
   programs nightly (`nightly-fuzz.yml`). Any disagreement, in accept or reject
   or in the inferred type up to renaming, fails the run. A disagreement is
   caught only on programs that are tested; that is the accepted gap.
   - Rejected for now: replacing the Rust checker with the extracted Coq one
     (it must build for `wasm32-unknown-unknown`, keep spanned kid-facing
     diagnostics and match today's speed, a large rewrite), and verifying the
     Rust directly (the tools for Rust code of this kind are immature). The
     first is reconsidered once the algorithm proof covers the whole language.

## Amendment (2026-11-20): iso-recursive types move ahead of phase 3

Decision 3 put iso-recursive types in phase 5. Issue #488 moves the *calculus*
half forward, so the phase order reads:

1. Unit, strings, `if`, arithmetic, comparison of base types.
2. Recursion and the value restriction.
3. **Iso-recursive types in the calculus** (decision 3's `mu`, `fold` and
   `unfold`, with guarded recursion). Done in #488.
4. Tags, variants, `match`, lists.
5. Spread update-or-extend with presence variables.
6. **The elaboration theorem**, methods, `self`, `.` and `::` on any receiver.
7. Structural ordering as a typed primitive.
8. The algorithm proof for the core, then extended phase by phase; and the
   parser over the full grammar.

Why the reorder: tags and lists are recursive (`mu t. <Empty | Link: {0: a, 1: t}>`),
and a phase that adds a binder to `typ` after the tag rules exist would change
their statements (the phase-2 lesson: a type-system change made late rewrites
every lemma already written). Doing it before tags costs one pass over the
existing files. Decision 3's elaboration theorem needs variants, methods and the
algorithm model, so it stays with the later phase.

What #488 settled, with the owner (`docs/design/recursive-types-plan.md` has the
options weighed):

- `fold(e)` and `unfold(e)` are explicit terms, `fold` is unannotated, and
  `unfold(fold(v)) ⟶ v` is the only new redex.
- Recursion is **guarded**, as ADR 0032 has it (under a record field and a
  function type): `T-Fold` and `T-Unfold` require it, so `mu t. (t) -> t` has no
  term. A variant payload will guard on its own in the tag phase.
- Type equality on `mu` is congruence only: no unrolling equation, so the
  recursion is iso.
- The binder is a de Bruijn index in the grammar (`typ_Bvar n`, `typ_Mu T`),
  with unrolling and closure written by hand. The bound index has no sort, and a
  `mu` satisfies only `Any`.
- The parser fragment does not change: `mu`, `fold` and `unfold` have no surface
  syntax.
- Algorithm W does not produce a `mu`: it rejects `fold` and `unfold`, and its
  occurs check refuses to bind a variable to a type with a free index. Extending
  it is a follow-up (#497).
- The type of an open-extensible recursive receiver (ADR 0034 decision 3) waits
  for methods and `self`; the intended reading is `forall r. mu t. {moved: (t) -> t;
  x: Int | r}`.

## Amendment (2026-11-22): what the elaboration theorem states

Decision 3's "with the same behaviour" is made precise, in `proofs/GoatElab.v`
and `docs/design/phase5-proof-plan.md` section 2.3.

- **The theorem is the soundness of W, with W returning the elaborated term.**
  `infer_elab fuel e = Some (D, e', T)` implies `typing D nil e' T` and
  `erase e' = e`. There is no second, equi-recursive typing relation.
- **`erase` drops `fold` and `unfold`.** `erase_step` says a step of an
  elaborated term is a step of its erasure, or an `unfold(fold v) --> v` that
  erasure cannot see; `erase_traps` says the same of a trap.
- **Head coercions only.** A mismatch between a mu type and its unrolling is
  repaired by one `fold` or `unfold` at the node (`coerce_typing`), so
  `erase e' = e` holds exactly. A program that needs a coercion below a function
  type or a record field would need an eta-expansion; it is outside the theorem
  and counted under `DeepCoercion`. The measurement behind this choice is in the
  plan, section 3, Q3.
- **The equality W's unifier decides** is the bounded-unrolling relation
  `T ~~[n] T'`, not a coinductive bisimulation.

## Amendment (2026-11-22): what phase 5 proved, and what it did not

Phase 5 (#454, stages 1 to 7) landed the elaboration theorem as the amendment
above states it, with these additions that the work settled.

- **W ties knots and returns the elaborated term.** `infer_elab_sound` and
  `infer_guarded` (every recursive type W returns is guarded) are checked closed
  in `GoatAssumptions.v`, 19 theorems in all, with 0 admits and no axioms.
  `unify_grp` ties the members of a recursive group, and `unify_pw` is gone.
- **Head coercions, as the amendment chose.** A difference below a function type
  or a record field is refused, not eta-expanded.
- **Methods are in the rules.** `T_Obj` gives every method of a literal one
  receiver (ADR 0034 decision 2, the owner's answer to the plan's question 1),
  and W's literal case infers each method with that receiver in scope.
- **The parser fragment covers a dot call on any receiver** (ADR 0031 decision 2),
  and `::`.
- **The differential test compares the result.** Of the 42 recursive-type programs
  in the corpus, 31 are compared with 0 mismatches. `proofs/README.md` holds the
  per-feature skip counts.

Not proved, and still open. Each is sound (W or the calculus refuses more than the
checker accepts) and the differential test counts it:

- 11 recursive programs W refuses (#606; corpus lines 7, 18, 291, 254, 299, 300,
  288, 292, 301, 312, 315): a row variable meeting a row that contains it (3) and
  a tail variable inside the other row (3), both refused after a prototype row
  knot because the sides differ by an unrolling below a record with an open row,
  which has no coercion; a deep coercion (3); two mus for one regular tree
  (`step(ball).x`), which needs a coinductive equality (1); and a group member
  that needs a `fold` around its whole lambda (1).
- No `lacks` sort on a row variable, so a spread over a row-variable tail has no
  derivation (#564).
- No theorem that `{...lit, x: 1}.a()`, a method literal spread and then called,
  has no derivation; the checker and W both reject it.
- (Closed by #628.) The 65 programs with a recursive group a value binding uses
  before its last member are compared: the checker now infers and generalizes
  the group before it types that value.

Decision 3's elaboration theorem is therefore proved for the programs W accepts,
and W's completeness against the checker is measured and not proved, as
decision 6 accepts for the algorithm.

## Consequences

- Language work slows by the cost of each proof, and the first PR to touch a
  construct in an unproven phase carries that phase.
- `docs/semantics.md` becomes the single readable statement of the language,
  kept in lockstep with the `.ott` files by the gate.
- Making `coq` a required check makes the Coq Docker job's time and flakiness
  part of every merge.
