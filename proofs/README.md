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
| `GoatNum.v` | The integer and rational arithmetic behind whole-number and decimal literals, kept apart because ZArith and QArith define notations that clash with Metalib's `x ~ T`. |
| `GoatLit.v` | Reads the argument of `e_num` as an integer, so `e_num 3` works in a file that never imports ZArith (and in the generated printer table). |
| `GoatPhase1.v` | Phase 1 of ADR 0037: worked examples for `Unit`, strings, `if`, and the operators on `Int`, `Float`, `String` and `Bool`: which programs type, what they evaluate to, which trap, and which have no derivation (`1.5 // 2`, `1 < "a"`, `true + true`, `if 1 then ...`). |
| `GoatSound.v` | The two canonical HM lemmas — `typing_weaken` (L4) and `typing_tsubst_fix` (L5) — via the general substitution lemma `typing_tsubst_gen_mut` (freshening the let-generalized variables so `gen` commutes with a capturing substitution, `casch_gen_sch_equiv`); then term substitution **L6a/L6b**, **Preservation** and **Soundness**. All axiom- and admit-free. |
| `GoatGrammar.v` | Generated from `grammar/goat.peg` by `parser/examples/emit_coq.rs` (`make gen-grammar`); `make check-grammar` fails on drift. Never hand-edited. |
| `GoatPeg.v` | Ford-style relational PEG semantics of the generated grammar over a token stream, and **T2** `peg_deterministic`. |
| `GoatDen.v` | The denotation of core-fragment parse trees as Ott terms (curried, locally nameless via `close_exp`, labels interned by first occurrence), and its local closure. |
| `GoatShape.v` | The forests the core rules can produce, the shape of each core node's children, and totality: every valid, complete core tree has a denotation. |
| `GoatParse.v` | **T1** `parse_denotes_lc`. |
| `GoatPegTac.v` | Helper tactics (`pok`, `pfail`) that build derivations of the PEG relation. No theorem lives there. |
| `GoatPrint.v` | The printer: a closed core term to its parse tree and token stream, binders named by depth (`v0`, `v1`, ...), mirroring the curried style of `checker/tests/core_roundtrip.rs`. |
| `GoatPrintChain.v`, `GoatPrintPrim.v`, `GoatPrintBlock.v`, `GoatPrintParse.v` | The parse side of T3: a printed chain, each primary and postfix, records and bindings, and every printed block, each with the ordered choices that could commit wrongly shown not to. |
| `GoatPrintDen.v`, `GoatPrintLabels.v`, `GoatPrintTop.v` | The denotation side: the printed tree denotes the term, the label table is the first-occurrence table of the term's labels, the top rule parses it. |
| `GoatRoundtrip.v` | **T3** `print_parse_roundtrip`. |
| `GoatRoundtripExample.v` | A term meeting T3's hypotheses, and one failing the label hypothesis. |
| `GoatPrinterTable.v` | Generated by `checker/tests/core_roundtrip.rs`: 200 terms with the token streams the Rust printer writes; Coq checks its printer agrees. |
| `GoatExample.v` | A fuel-bounded PEG interpreter, sound for the relation, parsing two small programs; T1 applied to one of them. |
| `GoatAssumptions.v` | `make check-assumptions` fails unless T1, T2, T3, `progress`, `preservation` and `soundness` print "Closed under the global context". |
| `_CoqProject`, `Makefile` | Build. |

## Phase 1: Unit, strings, `if`, and the operators on Int, Float, String, Bool (ADR 0037)

`goat_ln.ott` has the types `Int`, `Float`, `Unit` and `String`, the terms
`unit`, a whole-number literal `n` (an integer), a decimal literal `d` (a
numerator over a positive denominator), a string literal, `if e1 then e2 else e3`
and `e1 o e2`, and the operator syntax `o`. `GoatDefs.v` adds:

- the typing rules `T_Num` (an `Int`), `T_NumFloat` (the same literal settled as
  a `Float`), `T_Dec`, `T_Unit`, `T_Str`, `T_If` and `T_Bin`, where `T_Bin` asks
  the operator signature `bin_sig` (ADR 0017, ADR 0036) which operand types the
  operator takes and what it gives;
- the reduction rules for `if` and operators, with the value of an operator
  given by the relation `bin_step`: integers are signed and unbounded, `//` and
  `%` floor, a `Float` is an exact rational, and `Int` widens to `Float` at an
  operator;
- a trap: `traps e k` says evaluation reaches an integer `//` or `%` by zero.
  `progress` says a closed well-typed term is a value, steps, or traps, and
  `soundness` carries that along any run.

`progress`, `preservation` and `soundness` hold with 0 admits, and
`make check-assumptions` checks all six theorems (T1, T2, T3 and these).

What the model leaves out, each checked against `goat check` and `goat run`
(`docs/semantics.md` section 9): integer overflow and the target's width, IEEE
rounding and infinities (a `Float` quotient by zero steps to an unspecified
decimal), widening of an `Int` argument at a call, the `trap()` builtin, and the
`Eq`, `Numeric` and `Ordered` constraints (an operator applies at concrete
types; constraint-polymorphic operators are phase 2).

The parser fragment widens in step: a string, a conditional with an `else`, and
one operator between two chains. `GoatShape.v` counts operator nodes
(`count_ops`) and `Complete` allows at most one, with no dot call;
`GoatDen.v` reads `c1 o c2` as `e_bin` (`Den_math`); the printer parenthesises
the operand of an operator when it is a binding or another operation.

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

Needs an opam switch with Rocq 9.1.1 (the opam `coq.9.1.1` package), Ott 0.34,
and metalib (not on opam — pinned from `github.com/plclub/metalib` at
`144ddcd0fff6717229140314cf559d85fad6eae0`). Rocq 9.2 and 9.3 fail to build
metalib. With those on `PATH` (or under `opam exec --switch=rocq-9 --`):

```
make        # regenerate Goat_ott.v from goat_ln.ott, then compile under Rocq
make ci     # check the committed Goat_ott.v matches the source, then compile
```

metalib installs onto Rocq's `user-contrib` path, so no extra `-R` is needed for
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

## Rank-2 inference is not part of the language

An earlier pass added a rank-2 typing rule (`T_AppPoly`) and `GoatRank2.v`. Both
are deleted: goat has no type-annotation syntax and ADR 0027 declines
annotation-free rank-2 inference, so the sharp-edge programs `both` and `use2` stay
untypeable, which `docs/semantics.md` section 8 states as the language's limit.

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

`print_parse_roundtrip` (T3): for a closed core term `e` (`scoped 0 e`) whose
labels are numbered by first occurrence in the printed text (`Interned e`), and
a `var_of` that gives the printer's binder names `v0`, `v1`, ... distinct atoms
(`names_distinct`), the PEG relation parses `print e` to a tree `t` and
`Den_goat var_of t e` holds, so `t` denotes exactly `e`.

- **Printer.** The curried style of the Rust printer. A call's callee and a
  projection's base are parenthesised when they are a binding or a number; a
  binding's value is parenthesised when it is a binding. The grouped style is
  not mirrored.
- **Side conditions.** ADR 0030's three (recursive function bindings, groups of
  functions, duplicate labels or parameters) are not hypotheses of T3. The
  printer names each binder by its depth, so no name repeats and a binding is
  never read as recursive; the model's `Den` reads a binding as the Ott
  non-recursive `let` and accepts duplicate labels. They concern the Rust front
  end, which `checker/tests/core_roundtrip.rs` covers by testing.
- **Label table.** `labels` (T1) now lists each distinct label once, in order of
  first occurrence, the numbering lowering gives. Before, it kept repeats, so a
  label after a repeat got a larger index than lowering assigns.
- **Printer alignment.** `GoatPrinterTable.v` is generated: the Rust test fails
  when the committed file differs from what the Rust printer writes
  (`UPDATE_PRINTER_TABLE=1 cargo test -p goat_checker --test core_roundtrip`
  rewrites it), and the Coq build fails when the Coq printer disagrees with a
  row.
- **Not covered.** Free variables (T3 is for programs), the grouped style,
  everything T1 leaves out.

## CI

`.github/workflows/coq.yml` builds this directory under Rocq on the self-hosted
runner image, in its baked `rocq-9` opam switch (Rocq 9.1.1, Ott 0.34, metalib).
The job fails with the expected versions when the switch is missing. It triggers only on
changes under `proofs/**` (or to the workflow), plus manual dispatch, so
ordinary Rust PRs do not pay for a Coq image. It is intended as an
informational check, not a required one — promote it in branch protection once
the development stabilizes.
