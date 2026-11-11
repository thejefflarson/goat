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
| `GoatMeta.v` | The metatheory: locally-nameless infrastructure (via a computable `lc_at`), `typing_regular`, canonical forms (L7), typing inversions, and **Progress**. |
| `GoatSubst.v` | The Hindley–Milner substitution-algebra groundwork: the type/row-substitution algebra and `teq_ap`, the structural L4 lemmas (`typing_sch_equiv_ctx`, `typing_ftv_mono`), bijective renaming (`typing_rename`), and `gen_antimono`. What `GoatBij`/`GoatHM`/`GoatSound` build on. |
| `GoatBij.v` | Freshening infrastructure (finite-atom permutations, `mk_rename`, scheme/context alpha-renaming) feeding the T-Let freshening (#151). |
| `GoatHM.v` | Capture-avoiding scheme substitution `casch` and its instance-preservation `casch_inst` (#151). |
| `GoatRank2.v` | B4 (issue #72): the rank-2 intersection examples. The sharp-edge programs `both` (no-record) and `use2` (scoped-label rows) now type under `T_AppPoly`, and the extended `soundness` shows they never get stuck. |
| `GoatSound.v` | The two canonical HM lemmas — `typing_weaken` (L4) and `typing_tsubst_fix` (L5) — via the general substitution lemma `typing_tsubst_gen_mut` (freshening the let-generalized variables so `gen` commutes with a capturing substitution, `casch_gen_sch_equiv`); then term substitution **L6a/L6b**, **Preservation** and **Soundness**. All axiom- and admit-free. |
| `GoatGrammar.v` | Generated from `grammar/goat.peg` by `parser/examples/emit_coq.rs` (`make gen-grammar`); `make check-grammar` fails on drift. Never hand-edited. |
| `GoatPeg.v` | Ford-style relational PEG semantics of the generated grammar over a token stream, and **T2** `peg_deterministic`. |
| `GoatDen.v` | The denotation of core-fragment parse trees as Ott terms (curried, locally nameless via `close_exp`, labels interned by first occurrence), and its local closure. |
| `GoatShape.v` | The forests the core rules can produce, the shape of each core node's children, and totality: every valid, complete core tree has a denotation. |
| `GoatParse.v` | **T1** `parse_denotes_lc`. |
| `GoatExample.v` | A fuel-bounded PEG interpreter, sound for the relation, parsing two small programs; T1 applied to one of them. |
| `GoatAssumptions.v` | `make check-assumptions` fails unless T1 and T2 print "Closed under the global context". |
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

**Status:** Progress, Preservation and Soundness are all proved, assumption-free.
The two canonical Hindley–Milner lemmas — general weakening (L4,
`typing_weaken`) and type/row substitution (L5, `typing_tsubst_fix`) — that the
term-substitution lemmas L6a/L6b rest on are now **closed** (#151), so the whole
development is unconditional.

The soundness statements of `docs/semantics.md` §7 are mechanized here. By
`Print Assumptions`, **`progress`**, **`preservation`** and **`soundness`** are
all *closed under the global context*: no axioms, no admits.

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
- **Term substitution** (`GoatSound.v`): `typing_subst` (L6a, monomorphic, for
  `ST-Beta`) and `typing_subst_poly` (L6b, polymorphic, for `ST-LetV`), by mutual
  induction on the typing derivation, prefix-generalized over the context so the
  induction goes under binders. Their `let` cases need no new theory: dropping a
  binding from the context only makes `gen` more general with no new free
  variables (`gen_antimono`), the good direction for `typing_ftv_mono`. Also
  `typing_inst_gen` (every instance of a generalization is derivable).

- **The two canonical HM lemmas** (`GoatSound.v`), on which the term-substitution
  lemmas (hence Preservation's `ST-Beta`/`ST-LetV` and Soundness) rest:
  - `typing_weaken` (L4): inserting a middle block of bindings preserves typing;
  - `typing_tsubst_fix` (L5): substituting the type/row variables *not* free in
    the context preserves typing.

  Both follow from one general lemma, `typing_tsubst_gen_mut`: a type/row
  substitution applied to a derivation, with the context substituted
  capture-avoidingly (the `ctx_subst` relation, which also allows **extra**
  target bindings, so the identity substitution gives weakening). Every case is
  structural except `T-Let`, whose hard point is that generalization does not
  commute with a *capturing* substitution. The fix (approach (a) of the #151
  analysis) is a derivation-level freshness step carried out in the proof, not in
  the typing rule: at each `T-Let` the let-generalized variables are renamed to
  atoms fresh for the substitution and the target context (`mk_rename`), so the
  capture-avoiding substituted scheme (`casch`, `GoatHM`) both preserves the
  instance set (`casch_inst`) and equals `gen` of the substituted body over the
  target context (`casch_gen_sch_equiv`, `GoatSound`). The typing rules are
  untouched, so the set of accepted programs is unchanged.

`make ci` runs a frozen-admit guard (`make check-admits`) with
`EXPECTED_ADMITS = 0`: it fails if any `Admitted.` reappears in `proofs/*.v`.

## B4 (issue #72): rank-2 intersection inference, as a delta on the closed core

The core (B3) binds a lambda parameter monomorphically (`T_Abs` uses
`sch_mono T1`), so goat's sharp edge — a generic function passed as a parameter
and used at several types — is untypeable: `both = program(f) do f(1) f(true)`
fails. ADR 0008's chosen fix is **rank-2 intersection inference**. We add it as
one hand-written typing rule in `GoatDefs.v`, leaving the generated syntax
(`Goat_ott.v`) and the row theory untouched:

```
T_AppPoly :  typing G (e_let g e) T  ->  typing G (e_app (e_abs e) g) T
```

It types the redex `(program(e) done)(g)` **exactly as** `let x = g in e`: the
argument `g` is generalized against `G` and the parameter is usable at every
instance of that scheme inside the body. This is rank-2 (a quantifier only to
the left of the application arrow) realized as HM generalization of the
argument. The rule is a **conservative, additive** extension: every previously
well-typed program still types (the typing relation only gains derivations), and
it adds exactly the rank-2 power.

**Why this closes with no new theory.** `T_AppPoly`'s premise is an existing
`let`-typing at the *same* context and type, so every metatheory obligation for
the new rule reduces to the one already proved for `T_Let`:

- Preservation's `st_beta` on the rank-2 redex is the polymorphic substitution
  lemma `typing_subst_poly` (L6b) — the very lemma `ST-LetV` uses.
- The type/row-substitution lemma (`typing_tsubst_gen_mut`, L5, the Barendregt
  freshening step) gets a **one-line** new case: substitution does not touch the
  term, so the substituted derivation is the IH re-wrapped by `T_AppPoly`.
- Progress, regularity, weakening, renaming, and term substitution each get a
  short case cribbed from `T_Let`.

This is what lets the rank-2 **+ scoped-label-rows** combination (ADR 0008's
"appears unexplored") go through: `use2` (`getx = program(p) do p.x done` used at
two record widths) types because the argument's principal type is generalized
*including its row variable*, so its soundness is the already-closed row-aware
polymorphic substitution — no new row metatheory.

`Print Assumptions` on `soundness`, `progress`, `preservation`, `both_types`
and `use2_types` all report **"Closed under the global context"**:
axiom-free and admit-free, with `EXPECTED_ADMITS` still `0`.

**Honest boundary (not done in this pass).** The examples are stated in
direct-application form `(program(f) ...)(g)` — what the surface form
`f = program(...) ... f(...)` reduces to under `ST-LetV`. Typing a rank-2
function as a *stored first-class value* (`both = program(f) ...; both(g1); both(g2)`,
where `both`'s own lambda must receive a standalone type before being bound)
needs rank-2 **types** in the grammar, a heavier change to `typ`/`teq` and every
`match` over them. That is a separate, larger delta; `T_AppPoly` covers the
parameter-meets-argument site, which is where goat's sharp edge actually bites.

### Infrastructure (`GoatProofs.v`)

- `teq_refl` / `req_refl`: reflexivity of `≅`, derived by mutual induction (the
  relation states symmetry, transitivity, and label swap but no reflexivity).
- `subst_exp_fresh_eq`: `y ∉ fv_exp e → subst_exp u y e = e`, over the
  generated `subst_exp`/`fv_exp` (now mutual with the `fields` spine).

## The parser claim (ADR 0030)

`peg_deterministic` (T2): a token stream has at most one parse. `parse_denotes_lc`
(T1): every parse of the top rule `goat` whose tree is in the core fragment
denotes a term that is both `lc` (the local closure the soundness proof uses)
and the generated `lc_exp`.

Boundary:

- **Core fragment only.** The rules of `grammar/goat.peg` that `goat_ln.ott` has
  a production for (`core_rule` in `GoatShape.v`, checked against
  `parser/tests/rule_map.rs` by a Rust test), minus the shapes ADR 0030 excludes
  (`Complete` in `GoatShape.v`): `program()`, an empty body, a call with no
  arguments, an empty program, a block that ends in a binding.
- **The lexer is trusted.** The input is a list of tokens; nothing is said about
  how characters become tokens. A text terminal matches a punctuation or keyword
  token, never a name, so the words `from`, `to`, `in` and `foreign` (names
  elsewhere) cannot be matched as keywords by the model. No core rule spells them
  out.
- **Recovery annotations are not in the generated grammar.** They change nothing
  about valid input.
- **Not verified:** the Rust interpreter `parser/src/interp.rs`, the lowering
  `checker/src/lower.rs`, and every rule outside the fragment. Connecting them to
  these theorems stays a testing argument (`rule_map.rs`,
  `checker/tests/core_roundtrip.rs`).

Side conditions. The front end and `goat_ln.ott` disagree in three places (ADR
0030): function bindings are recursive and a block's functions form a group, and
duplicate record labels or repeated parameters are lowering errors. `goat_ln.ott`
is unchanged; they are conditions on the term, to be hypotheses of the
round-trip theorem T3 where they matter. T1 does not need them: `close_exp`
yields a locally closed term whatever names repeat, so T1 is stated without them
rather than with unused hypotheses.

## CI

`.github/workflows/coq.yml` builds this directory under `coqc` in the
`coqorg/coq:8.20` image, installing Ott and metalib first. It triggers only on
changes under `proofs/**` (or to the workflow), plus manual dispatch, so
ordinary Rust PRs do not pay for a Coq image. It is intended as an
informational check, not a required one — promote it in branch protection once
the development stabilizes.
