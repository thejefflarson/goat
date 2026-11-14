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
      `::` on any receiver.
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

## Consequences

- Language work slows by the cost of each proof, and the first PR to touch a
  construct in an unproven phase carries that phase.
- `docs/semantics.md` becomes the single readable statement of the language,
  kept in lockstep with the `.ott` files by the gate.
- Making `coq` a required check makes the Coq Docker job's time and flakiness
  part of every merge.
