# goat proofs

The mechanized soundness development for goat's type system (ADR 0008, issue
#70). This directory is **outside** the cargo workspace and the
`wasm32-unknown-unknown` build on purpose: it holds no Rust and no manifest, so
`Cargo.toml`'s `members` never lists it and the wasm32 job's explicit `-p` list
never reaches it. It is built by its own CI job (`.github/workflows/coq.yml`),
independent of the Rust `check`/`wasm32` jobs and the Kani `verify` job.

B2 (this directory's first cut) stands up the pipeline and lands two
infrastructure lemmas end-to-end. The soundness proof itself (progress +
preservation) is B3 (#71).

## Files

| File | Role |
| --- | --- |
| `goat.ott` | The typeset spec: the lockstep twin of `docs/semantics.md` (n-ary program/application, n-ary arrow). Source for the typeset rules, **not** for Coq. |
| `goat_ln.ott` | The mechanization source: the locally-nameless core that Coq is generated from. See "Why two Ott files". |
| `Goat_ott.v` | Generated from `goat_ln.ott` by Ott. Committed (see "Generated, committed"). |
| `GoatProofs.v` | Hand-written locally-nameless infrastructure lemma (`subst_exp_fresh_eq`) and derived row-equivalence reflexivity. |
| `GoatRows.v` | Row-equivalence theory: L1 (equivalence + congruence), L2 (head-shape "no confusion" + arrow/record inversion up to `≅`), L2′ (the §3 per-label characterization, soundness direction), L3 (row surfacing). Over `typ`/`row`/`teq`/`req` only. |
| `GoatDefs.v` | The declarative type system and operational semantics (`docs/semantics.md` §4–§6), hand-written over the generated syntax: type/row substitution, free-variable predicates, schemes, contexts, instantiation, generalization, values, small-step reduction, typing. |
| `GoatMeta.v` | The metatheory: locally-nameless infrastructure (via a computable `lc_at`), `typing_regular`, canonical forms (L7), typing inversions, **Progress**, **Preservation**, **Soundness**. |
| `_CoqProject`, `Makefile` | Build. |

## Records and projection in the Ott source

`goat_ln.ott` adds the record literal `{ fs }` and projection `e.l` to the term
grammar. The field sequence `fs` is a **mutually-recursive cons-list** baked
into the same inductive block as `exp` (`fs_nil`, `l : e ; fs`), *not* a Coq
`list (label * exp)`. This is deliberate: given a `list`-valued subterm, Ott
0.34 aborts its locally-nameless `lc`/`fv`/`subst` code generation (it prints
`only native lists supported`, then fails with `Not_found`). The mutual
cons-list is the same finite ordered field sequence and lets Ott emit the full
`open`/`subst`/`fv`/`lc` companions (`open_fields_wrt_exp`, `fv_fields`, …) that
the metatheory needs. Type and row variables remain a free-variable set
(`nat`), not binders, exactly as B2 chose.

## Build

Needs an opam switch with Coq 8.20.1, Ott 0.34, and metalib (not on opam —
pinned from `github.com/plclub/metalib`). With those on `PATH`:

```
make        # regenerate Goat_ott.v from goat_ln.ott, then compile under coqc
make ci     # check the committed Goat_ott.v matches the source, then compile
```

metalib installs onto Coq's `user-contrib` path, so no extra `-R` is needed for
it; `_CoqProject` maps this directory to the logical name `Goat`.

## Why two Ott files

`goat.ott` is the readable typeset spec and must stay in lockstep with
`docs/semantics.md`. The Coq generation needs two things that spec does not
carry, which `goat.ott` itself flags as "realized in B2, not here":

1. The term-variable metavar must be marked `repr-locally-nameless` for
   metalib/LNgen.
2. The n-ary multi-binder needs a concrete encoding.

Putting those in a separate `goat_ln.ott` keeps the typeset spec clean and lets
the mechanization make its encoding choice explicitly.

## The n-ary binder: internal currying to a single-binder lambda

`docs/semantics.md` §10 names two encodings for `program(x1,...,xk)`: (a)
internal currying to a single-binder lambda, or (b) a telescope /
simultaneous-substitution encoding. **B2 chooses (a).**

Why: metalib/LNgen's locally-nameless machinery — `open`/`close`/`subst`/`fv`
and the cofinite `lc` predicate, plus the full suite of lemmas LNgen emits — is
built for **single** binders. A single-binder core is the one encoding where all
of it, and the large locally-nameless PL-metatheory corpus ADR 0008 wants to
crib from, applies unchanged. In `goat_ln.ott` `program` binds one parameter,
application is unary, and the arrow `(T1) -> T2` is unary; Ott generates exactly
the standard `open_exp_wrt_exp` / `subst_exp` / `fv_exp` / `lc_exp` from it.

The cost, as §10 says, is a surface/core gap. goat's surface function is
genuinely k-ary: `program(x1,...,xk)`, `e(e1,...,ek)`, `(T1,...,Tk) -> T`, and
the sharp-edge examples depend on that arity. The curried core is the k-fold
iteration of the unary core, reconnected to the surface by uncurry/arity lemmas.
B2 does not need that bridge (its lemmas are stated on the core); B3 carries it.

Type and row variables are **not** binders (ADR 0008): a free-variable set with
named substitution. In this B2 core they are `nat`; refining them to metalib
`atom` with atom-set free-variable functions is a B3 step. Neither lemma below
depends on that choice.

## Generated, committed

`Goat_ott.v` is generated but **committed**, so the development builds without
Ott present and so diffs are reviewable. The generation command lives in the
`Makefile`; `make ci` (and the CI job) regenerate into a scratch file and
`diff` against the committed copy, failing on drift. CI pins `ott.0.34` so the
diff is byte-reproducible.

LNgen — which would *emit* the infrastructure lemmas rather than our proving
them — is a Haskell tool not packaged on opam, so it is not in the pipeline.
The one infrastructure lemma below is therefore hand-proved; wiring LNgen in (it
needs a Haskell toolchain in CI) is a later step.

## What is proved (B3, issue #71)

The soundness statements of `docs/semantics.md` §7 are mechanized here. By
`Print Assumptions`:

- **`progress`** — *closed under the global context*: no axioms, no admits.
- **`preservation`** and **`soundness`** — closed except they rest on the two
  term-substitution lemmas below.

Fully closed, no admits:

- The row theory (`GoatRows.v`): L1, L2 (incl. arrow/record inversion up to
  `≅`), L2′, L3. The §3 characterization is proved in the **soundness
  direction** — `req` respects the tail-and-per-label-list reading — which is
  exactly L2′ and is what the record cases of canonical forms, L3, and
  `ST-ProjRec` need. The *completeness* direction (the characterization implies
  `req`, the swap-congruence obligation ADR 0008 names as the schedule risk) is
  **not** needed for progress/preservation and is not proved.
- Locally-nameless infrastructure (`open`/`subst` commutation, `subst_intro`),
  `typing_regular`, canonical forms (L7), the T-Conv-aware typing inversions,
  **Progress**, all **Preservation** congruence cases, and `ST-ProjRec`.

The **two `Admitted` lemmas** (`GoatMeta.v`), on which Preservation's `ST-Beta`
and `ST-LetV` cases (hence Soundness) rest:

- `typing_subst` (L6a, monomorphic term substitution);
- `typing_subst_poly` (L6b, polymorphic term substitution).

Both are the standard Hindley–Milner substitution lemmas. Closing them needs the
type/row-substitution-preserves-typing lemma (L5) together with weakening under
binders, whose let case turns on generalization commuting with type substitution
— i.e. capture-avoidance over the `nat`-indexed quantifier sets. `docs/semantics.md`
§10 flags L6b's interaction with L5 as the subtlest case, and ADR 0008 budgets
this HM substitution theory separately. They are stated at full strength (no
theorem is weakened).

### Infrastructure (`GoatProofs.v`)

- `teq_refl` / `req_refl`: reflexivity of `≅`, derived by mutual induction (the
  relation states symmetry, transitivity, and label swap but no reflexivity).
- `subst_exp_fresh_eq`: `y ∉ fv_exp e → subst_exp u y e = e`, over the
  generated `subst_exp`/`fv_exp` (now mutual with the `fields` spine).

## CI

`.github/workflows/coq.yml` builds this directory under `coqc` in the
`coqorg/coq:8.20` image, installing Ott and metalib first. It triggers only on
changes under `proofs/**` (or to the workflow), plus manual dispatch, so
ordinary Rust PRs do not pay for a Coq image. It is intended as an
informational check, not a required one — promote it in branch protection once
the development stabilizes.
