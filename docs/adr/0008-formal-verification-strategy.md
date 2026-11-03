# ADR 0008 — Formal verification strategy: Coq for the type-system proof, Kani for bounded unit proofs

- Status: accepted (2026-11-02)
- Context: Formal-verification research sprint (parallel to docs/plan.md phases),
  CLAUDE.md, docs/plan.md "Known limitation", ADR 0001–0007

## Context

goat's type system has a documented sharp edge (docs/plan.md "Known
limitation"): lambda-bound parameters are monomorphic, so a generic function
passed as a parameter cannot be used at two types inside the body. The candidate
fixes — rank-2 intersection inference, or polymorphic fields on named types —
are easy to make subtly unsound. We want to change the type system without
silently reintroducing unsoundness, so this sprint builds a mechanized model and
proof that de-risks the fix. The sprint produces the model and proof; it does not
change the Rust checker — that is a downstream follow-up.

Three verification techniques are available and do three different jobs:
property-based differential fuzzing (bolero, exists) *falsifies* end-to-end
interp-vs-wasm; a bounded model checker *verifies* small pure functions; a proof
assistant *proves* the type system sound. They are complementary, not
substitutes.

## Decision

### Proof assistant: Coq (Rocq), over Lean

- Progress + preservation for a typed λ-calculus extended to HM + scoped-label
  rows is the most well-trodden path in Coq (Software Foundations PLF).
- Mature binder tooling: **Ott** generates both the typeset spec and the Coq
  definitions from one source (no drift), paired with **metalib/LNgen** for the
  locally-nameless substitution infrastructure.
- Existing mechanized HM and row-polymorphism developments to crib from.
- Lean's PL-metatheory/binder corpus is thinner, and the compiler being in Rust
  gives Lean no same-language synergy.
- Redex / property-testing the metatheory was considered and rejected as the
  wrong tier for a "be sure" research proof: it falsifies, it does not prove.
  (That tier is already served by the bolero differential fuzzer.)

### Proof scope: declarative soundness, RC abstracted, smallest core

- We prove soundness of the **declarative type system** (progress +
  preservation: well-typed closed terms do not get stuck), **not** soundness or
  completeness of the inference algorithm. The fix changes what is typeable; a
  sound declarative system makes any faithful algorithm sound. Proving Algorithm
  W / unification against the declarative system (termination, principal types)
  is a strictly larger, separate effort, explicitly out of scope.
- **Reference counting is abstracted away.** The operational model is standard
  substitution-based small-step over immutable values. RC is a
  compilation/memory strategy that cannot make a well-typed term get stuck;
  modeling it is large and buys the sharp-edge theorem nothing. Memory-safety of
  RC insertion (Phase 6) is a distinct obligation this proof does not cover.
- **Smallest meaningful core** = λ/`program` + application + HM
  let-generalization + two base types + records as scoped-label rows. Variants,
  `match`, recursive/μ-types, strings, numeric constraints, closures-as-data,
  and mono are out; each is a later delta on the proven core.
- **Binder discipline: locally-nameless via Ott + metalib/LNgen**, not Autosubst
  — it maximizes crib-ability from the locally-nameless PL-metatheory corpus and
  keeps the generated spec readable. Term binders (λ) use locally-nameless;
  type/row variables are a free-variable set with type-substitution over the
  context, not term binders.
- For declarative soundness, row **unification** termination is not proven (it is
  algorithmic); the proof burden is Leijen's row-**equivalence** theory and
  canonical forms. The μ-type unification-termination hazard does not arise
  because variants are out of the core.

### Sharp-edge fix to prove: rank-2 intersection inference

- The proof targets **rank-2 intersection inference** as the fix. It fixes the
  sharp edge in full — including the no-record case
  `both = program(f) do f(1)  f(true) done` — with **no annotations anywhere**,
  which keeps goat's kid-facing, structural, no-type-declarations character
  intact. This is the directional choice for the language: the sharp edge is
  removed for ordinary code, not only for a named-types tier.
- This is deliberately the **ambitious, research-grade** target, chosen with eyes
  open. Rank-2 intersection systems are individually sound in the literature
  (Jim '96; Kfoury–Wells '99; Damiani), but **rank-2 intersection combined with
  scoped-label rows appears unexplored** (docs/plan.md), so B4 is a genuine
  research spike: higher variance, little to crib, and it may require developing
  metatheory rather than adapting it. We accept that cost because the payoff — a
  sound, annotation-free fix — is worth proving before it touches the checker,
  and proving it is precisely how we avoid shipping a subtly unsound inferencer.
- **Documented fallback:** if the rank-2 + scoped-label-rows combination proves
  intractable to mechanize within a time-boxed exploration, fall back to proving
  **polymorphic record fields** (annotation-driven boxed System F on the planned
  named-types tier) — a tractable, cribbable delta that fixes the record/field
  form of the sharp edge. The fallback is recorded so B4 ends in a proven delta
  either way, not an open-ended search.
- The proven core (B3) plus whichever delta lands establish a
  delta-on-proven-core method for validating future type-system changes.

### Kani's explicit scope limit

- The Kani bounded-verification tier (bolero's Kani backend, or native
  `#[kani::proof]` harnesses) runs **only** on small, pure, self-contained
  functions where a bounded proof is tractable: object-header/field-offset/layout
  math (ADR 0002), the number/bool formatters, individual pure MIR rewrites, pure
  checker row helpers (occurs-check, substitution).
- **Kani cannot prove end-to-end interp-vs-wasm equivalence**: wasmtime cannot
  live in the solver. End-to-end equivalence stays the job of the bolero
  differential fuzzer (falsification). Kani verifies units; Coq proves the type
  system; the fuzzer falsifies the whole pipeline.

## Consequences

- The proof lives in a new top-level `proofs/` directory, outside the cargo
  workspace and the wasm32-unknown-unknown build, built by a separate opam/coq
  CI job. The Kani tier is a separate nightly/non-required CI job off the
  per-PR critical path. The existing invariants are unchanged: user-facing errors
  still come only from the checker, and the Rust gates (fmt, clippy -D warnings,
  test) are untouched.
- `docs/semantics.md` (Ott-authored) becomes goat's first written formal
  semantics — a durable asset even if the proof never completes.
- The row-equivalence theory is the core proof's main schedule risk, and the
  rank-2 extension (B4) is a research spike whose size is unknown; sizes are
  research estimates, not commitments, and B4 is time-boxed with a fallback.
- The Rust checker change that implements the fix is a downstream follow-up,
  filed separately after the model proof lands.
- What the soundness proof does **not** cover, recorded to prevent over-claiming:
  the inference algorithm, RC memory-safety, and any feature outside the core.
