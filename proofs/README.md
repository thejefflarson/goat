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
| `GoatMu.v` | The type algebra of the one binder in `typ`: unrolling `open_typ`, local closure `lct`, how substitution commutes with unrolling (`ap_open_mut`), how type equality respects unrolling (`teq_open`, `teq_unroll`), and the guard `gd`/`guarded` with its closure under substitution and `teq`. |
| `GoatRecTypes.v` | Iso-recursive types: worked examples. `P = mu t. {moved: (t) -> t; x: Int}`, a `fold`ed ball, a `step` that unfolds its receiver, a run, and what has no derivation (a fold missing its `x`, self-application, a record with no function). |
| `GoatMeta.v` | The metatheory: locally-nameless infrastructure (via a computable `lc_at`), `typing_regular`, canonical forms (L7), typing inversions, and **Progress**. |
| `GoatSubst.v` | The Hindley–Milner substitution-algebra groundwork: the type/row-substitution algebra and `teq_ap`, the structural L4 lemmas (`typing_sch_equiv_ctx`, `typing_ftv_mono`), the free-variable facts of a bijective renaming, and `gen_more_gen` (generalizing over a smaller context quantifies more, at the sorts the extra atoms already had). What `GoatBij`/`GoatHM`/`GoatSound` build on. |
| `GoatBij.v` | Freshening infrastructure (finite-atom permutations, `mk_rename`) feeding the T-Let freshening (#151). |
| `GoatHM.v` | Capture-avoiding scheme substitution `casch` and its instance-preservation `casch_inst` (#151). |
| `GoatNum.v` | The integer arithmetic behind whole-number literals and the 64-bit `Int` range, kept apart because ZArith defines notations that clash with Metalib's `x ~ T`. |
| `GoatLit.v` | Reads the argument of `e_num` as an integer, so `e_num 3` works in a file that never imports ZArith (and in the generated printer table). |
| `GoatPhase1.v` | Phase 1 of ADR 0037: worked examples (and the inference algorithm run on a few of them) for `Unit`, strings, `if`, the operators on `Int`, `Float`, `String` and `Bool`, and the Int-to-Float coercion; and the generic operators: a numeral at `Float`, `float(1.5)`, and a `let`-bound function used at `Int` and `Float` but not at `String`. Which programs type, what they evaluate to, which trap (division by zero, overflow), and which have no derivation (`1.5 // 2`, `1 < "a"`, `true + true`, `if 1 then ...`, a numeral-sorted function used at `String`). |
| `GoatPhase2.v` | Phase 2 of ADR 0037: worked examples for the value restriction (which terms `is_gen_value` accepts), a generalized binding used at two types, a recursive group (its typing, its unrolling, a run) and a group member that is not a function (no derivation). |
| `GoatSound.v` | The general substitution lemma `typing_tsubst_gen_mut` (freshening the let-generalized variables so `gen` commutes with a capturing substitution, `casch_gen_sch_equiv`, and so the sorts they carry survive), with `typing_weaken` (L4) and `typing_denv_agree` / `typing_inst_gen` (a derivation moves between two kinding environments); then term substitution **L6a/L6b** (`typing_subst_gen_mut`), **Preservation** and **Soundness**. All axiom- and admit-free. |
| `GoatGrammar.v` | Generated from `grammar/goat.peg` by `parser/examples/emit_coq.rs` (`make gen-grammar`); `make check-grammar` fails on drift. Never hand-edited. |
| `GoatPeg.v` | Ford-style relational PEG semantics of the generated grammar over a token stream, and **T2** `peg_deterministic`. |
| `GoatDen.v` | The denotation of core-fragment parse trees as Ott terms (curried, locally nameless via `close_exp`, labels interned by first occurrence, a block's leading function bindings grouped as a `letrec` by `bind_group`), and its local closure. |
| `GoatShape.v` | The forests the core rules can produce, the shape of each core node's children, and totality: every valid, complete core tree has a denotation. |
| `GoatParse.v` | **T1** `parse_denotes_lc`. |
| `GoatPegTac.v` | Helper tactics (`pok`, `pfail`) that build derivations of the PEG relation. No theorem lives there. |
| `GoatPrint.v` | The printer: a closed core term to its parse tree and token stream, binders named by depth (`v0`, `v1`, ...), mirroring the curried style of `checker/tests/core_roundtrip.rs`. |
| `GoatPrintChain.v`, `GoatPrintPrim.v`, `GoatPrintBlock.v`, `GoatPrintParse.v` | The parse side of T3: a printed chain, each primary and postfix, records and bindings, and every printed block, each with the ordered choices that could commit wrongly shown not to. |
| `GoatPrintDen.v`, `GoatPrintLabels.v`, `GoatPrintTop.v` | The denotation side: the printed tree denotes the term, the label table is the first-occurrence table of the term's labels, the top rule parses it. |
| `GoatRoundtrip.v` | **T3** `print_parse_roundtrip`. |
| `GoatRoundtripExample.v` | A term meeting T3's hypotheses, and one failing the label hypothesis. |
| `GoatPrinterTable.v` | Generated by `checker/tests/core_roundtrip.rs`: 200 terms (strings, `Float` literals, `if` with and without an `else`, and operators included) with the token streams the Rust printer writes; Coq checks its printer agrees. |
| `GoatExample.v` | A fuel-bounded PEG interpreter, sound for the relation, parsing small programs; T1 applied to three of them, and the recursive-group program `countdown` shown to denote the `GoatPhase2.v` term that types as an `Int`. |
| `GoatAssumptions.v` | `make check-assumptions` fails unless T1, T2, T3, `progress`, `preservation`, `soundness` and `infer_closed_sound` print "Closed under the global context". |
| `_CoqProject`, `Makefile` | Build. |

## Phase 1: Unit, strings, `if`, and the operators on Int, Float, String, Bool (ADR 0037)

`goat_ln.ott` has the types `Int`, `Float`, `Unit` and `String`, the terms
`unit`, a whole-number literal `n` (an integer), a `Float` value `d` (opaque),
a string literal, `if e1 then e2 else e3`, `e1 o e2` and the coercion
`float(e)`, and the operator syntax `o`. `GoatDefs.v` adds:

- the typing rules `T_Num` (an `Int`), `T_Dec` (a `Float`), `T_Unit`, `T_Str`,
  `T_If`, `T_ToFloat` and `T_Bin`, where `T_Bin` asks the operator signature
  `bin_sig` (ADR 0017, ADR 0036) which operand types the operator takes and
  what it gives. Both operands of an arithmetic or comparison operator have one
  type, so an `Int` meets a `Float` only through `float(e)`;
- the reduction rules for `if`, operators and the coercion, with the value of
  an operator given by the relation `bin_step`;
- `Int` is a signed 64-bit integer: `+ - *` and `//` `%` step only when the
  result is in `[int_min, int_max]` (`in_int`), `//` and `%` floor, and a zero
  divisor or a result outside the range is a trap;
- `Float` is opaque. `e_dec d` carries a payload no rule reads, and every
  `Float` operation (`+ - * /`, `float(n)`) relates its operands to every
  `Float`, and a `Float` comparison to either boolean. That is an unspecified
  function written as a relation, so it needs no axiom or parameter, and a
  theorem about it holds for any function a compiler computes;
- a trap: `traps e k` says evaluation reaches an integer operation that divides
  by zero (`trap_div_zero`) or leaves the 64-bit range (`trap_overflow`).
  `progress` says a closed well-typed term is a value, steps, or traps, and
  `soundness` carries that along any run.

The coercion `float(e)` is what elaboration inserts wherever the checker accepts
an `Int` for a `Float`: a call whose parameter is a `Float`, an operator with a
`Float` on one side, a literal settled as a `Float`. The calculus has no
subtyping, so the rule is `T_ToFloat`: `float(e)` is a `Float` when `e` is an
`Int`. Preservation and progress cover it like any other term. That the
elaborator inserts it exactly where the checker accepts an `Int` for a `Float`
is not a theorem: the differential test checks it (`differential/README.md`),
by writing `float(e)` from the checker's own node types and requiring the
proven algorithm to accept the result with the checker's type.

`progress`, `preservation` and `soundness` hold with 0 admits, and
`make check-assumptions` checks all seven theorems (T1, T2, T3, these three and
the inference algorithm's soundness).

What the model leaves out, each checked against `goat check` and `goat run`
(`docs/semantics.md` section 9): the embedded target's 32-bit `Int`, IEEE
rounding, infinities and NaN (a `Float` is opaque), the `trap()` builtin,
comparison of `Unit` (phase 6), and the `Eq` and `Ordered` constraints (a
comparison applies at concrete types; a generic comparison waits for those
sorts). `+ - *` and numerals are generic over the sorts `Numeric` and
`Literal`, below. The inference algorithm (`GoatInfer.v`) covers the
whole of phase 1: `Unit`, strings, Float values, `if`, `float(e)` and the
operators, besides functions, bindings and records. `infer_closed_sound` keeps
its statement. An operator unifies both operands with one type taken from
whichever operand type is already known (`bin_arg`), so `x * 1.5` fixes `x` to
`Float`, and an operator whose two operands are both still variables is
rejected: inferring the generic operators of the calculus is a follow-up, so the
algorithm is sound for them (it infers only derivable types) and not complete.

The parser fragment widens in step: a string, a `Float` literal (a `TDec` token
that denotes the opaque `e_dec`), a conditional with or without an `else` (the
missing branch is `e_unit`), and one operator between two chains. `GoatShape.v` counts operator nodes
(`count_ops`) and `Complete` allows at most one, with no dot call;
`GoatDen.v` reads `c1 o c2` as `e_bin` (`Den_math`); the printer parenthesises
the operand of an operator when it is a binding or another operation.

## Phase 2: recursion and the value restriction (ADR 0037)

`goat_ln.ott` has one new term, `letrec x = { fs } e2`: a recursive group. The
group's name `x` is one locally-nameless binder over the record of the group's
functions `fs` and over the body `e2`; a member `f` of the surface group
`letrec f1 = e1, ..., fn = en in e` is the projection `x.l` of its label. The
surface form is the n-ary letrec of `docs/semantics.md`; the single binder is
what the locally-nameless infrastructure handles, as the curried single-binder
`program` is for `program(x1, ..., xk)`. `GoatDefs.v` adds:

- `is_gen_value`, the value restriction's predicate (ADR 0027): unit, literals,
  names, functions, and records of those, with `float(v)` of a value and a
  `letrec` around a value (what substituting an unrolled group for its name
  needs);
- `T_Let` generalizes only when `is_gen_value e1`; `T_LetMono` types any `let`
  with a monomorphic binding, and a computed binding has no other rule;
- `T_Letrec`: the members (`fn_group`: all `program` literals) are typed with
  the group's name at the record type of the members, and the body with the
  name generalized against the context, so each use of a member instantiates
  the group afresh;
- `st_letrec`: the group unrolls at once, replacing its name in the body by
  the record of its members, in each of which the name is the group again.

`progress`, `preservation` and `soundness` cover the new terms with 0 admits.
`step_gen` (a syntactic value stays one when it steps) keeps `T_Let` after
`st_let1`; `is_gen_subst` keeps it under the term substitutions of `ST-Beta`,
`ST-LetV` and `ST-Letrec`; `tsubst_gen_core` is the capture-avoiding renaming
that `T_Let` and `T_Letrec` share in the type-substitution lemma.

The inference algorithm covers these forms (`GoatInfer.v`, `GoatInferRec.v`,
`GoatInferSound.v`): a `let` of a computed value is typed monomorphically
(`T_LetMono`), and a `letrec` infers its members with the group's name bound
to a row of fresh variables, unifies each member's type with its variable
(`unify_pw`), and generalizes the group's record type for the body
(`T_Letrec`). The grammar has no new
form, but the parser fragment now reads the surface group: the function
bindings that lead a block (`f = program(x) do ... done`, ADR 0003) are one
`letrec`, each member named by its position (`GoatDen.v`, `DB_group`). Every
occurrence of a member's name in the members and the rest of the block becomes
the projection of that member from the group (`bind_group`). A function binding
after a value binding in the same block is outside the fragment (decided: the
group would have to be placed after the values its members read, which needs
name resolution). A binding
whose value is a parenthesised function is a plain `let`, so the printer
parenthesises a function that is a binding's value. T1 covers groups, and
`GoatExample.v` shows one program parsing to the group `GoatPhase2.v` types. T3
does not (decided: deferred to the tail of phase 8): the printer does not write a
`letrec`, which would need the group's projections printed as bare member names.
The lexer stays trusted until phases 3 to 6 land, then is verified once (decided).

## Phase 3 (ADR 0037, amended): iso-recursive types

`goat_ln.ott` has two new types, `bv i` (the index of an enclosing `mu`) and
`mu T` (the body counts the `mu` as index 0), and two new terms `fold(e)` and
`unfold(e)`; a `fold` of a value is a value. `GoatDefs.v` adds:

- `open_typ k U T` (replace the index `k` by `U`, lower the ones above), the
  closure predicate `lct k T`, and the guard `gd`/`guarded`: every mention of
  the index sits under a record field and under a function type (ADR 0032);
- `T_Fold`: `fold(e) : mu B` when `mu B` is closed, `B` is guarded and `e` has
  the unrolling `open_typ 0 (mu B) B`; `T_Unfold` is its converse. `fold` carries
  no type annotation, so terms stay free of types;
- `st_unfold_fold` (`unfold(fold(v)) --> v`) and the two congruences.

`teq_mu` is congruence only. There is no unrolling equation: that is what makes
the recursion iso, and it keeps `teq_Mu_inv` (a type equal to a `mu` is a `mu`)
a plain induction. The binder is a de Bruijn index written into the grammar, not
an Ott binder: a cofinite `teq_mu` would make `teq_ap` (type equality under
substitution) need a fresh atom the substitution fixes, and so a finite-support
hypothesis on every substitution that reaches `T_Conv`. The index has no sort
(ADR 0038), and a `mu` satisfies only `k_Any`, so `kres` is untouched.

One price: `ap_open_mut` (substitution commutes with unrolling) needs the
substituted types closed. `lc_sub st sr` says so, and it rides along where a
substitution did already: in `inst` (a generic instance has closed images), in
`tr_supp` (so in `OkS`, the algorithm's substitution invariant) and in
`casch_inst`. `GoatInfer.v` stays sound by construction: it rejects `fold` and
`unfold`, and its occurs check (`occT`, `occR`) refuses to bind a variable to a
type with a free index (`lcb`), which never fires on a type the algorithm
builds. Extending the algorithm to produce a `mu` is a follow-up.

`progress`, `preservation`, `soundness` and `infer_closed_sound` hold with 0
admits. `canon_mu` (a value typed at a type equal to a `mu` is a `fold`) joins
the canonical forms; `teq_unroll` (equal `mu`s have equal unrollings) retypes a
fold at an equal type. `GoatRecTypes.v` shows the guard doing its job
(`no_fold_at_self_application`: a `fold` has no type equal to
`mu t. (t) -> t`, through any conversion). The parser fragment is unchanged:
`mu`, `fold` and `unfold` have no surface syntax, so T1 to T3 only gained the
cases that say a printed term is never one.

What waits: the elaboration theorem (every program the checker's algorithm
accepts elaborates into an iso-recursive one), which needs variants, methods and
the algorithm model; the type of an open-extensible recursive receiver; and
phase 3's tag signature, which must keep closed payload types in the sense of
`lct`, since a payload under a `mu` mentions an index.

## Generic operators: sorted type variables (design Q)

The typing judgment carries a kinding environment `D` (`typing D G e T`): a
total map from type variables to a **sort** (`k_Any`, `k_Numeric`,
`k_Literal`), `k_Any` outside a finite support. A type satisfies a sort
(`sat D k T`) when it is `Int` or `Float`, or a variable whose sort in `D` is at
or above `k`. A scheme records the sort of each quantified variable
(`Sch tq rq body sk`), so `gen G T k` quantifies the free variables of `T` not in
`G` at the sorts `k`. `T_Let` and `T_Letrec` type the bound term under
`ext D V k`, `D` extended on the generalized set `V` by `k`, which is why the
sort of a variable lives in the environment and a type variable stays a plain
`typ_Var a`. A numeral has any `k_Literal` type, `float(e)` takes any
`k_Numeric` operand, and `+ - *` take two operands of one `k_Numeric` type. A
substitution respects the sorts when `kres D D' st`: each `a` goes to a type
that satisfies `D a` in `D'`.

The substitution lemma needs three things the plain calculus did not.
`sch_subst` and `ctx_subst` quantify over all pairs of environments the
substitution respects, so renaming the generalized variables moves the
environment by the renaming (`dperm`). The target and source environments are
`k_Any` outside a finite set (`supp_ok`), so a fresh name a `let` is renamed
onto is `k_Any` and carries any sort. And a derivation moves between two
environments that agree on the free variables of its context and type
(`typing_denv_agree`), sending the variables it uses internally to `Int`, which
satisfies every sort; term substitution under a `let` needs exactly that, because
the bound term is typed in an extended environment. `sch_more_gen` (for
`typing_ftv_mono`) is indexed by the environment for the same reason.

The program judgment is `typing d_any nil e T` with `d_any` the all-`k_Any`
environment. Defaulting (ADR 0017: a `Literal` variable left unconstrained is
`Int`; `Numeric` has none) is therefore a choice among derivations, not a rule:
in `d_any` a closed derivation instantiates each generalized `Literal` variable
at `Int` or `Float`, and `numeral_binding_is_generic` in `GoatPhase1.v` shows
both choices.

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
  `ST-Beta`) and `typing_subst_poly` (L6b, polymorphic, for `ST-LetV`), both
  instances of one lemma `typing_subst_gen_mut`, by mutual induction on the typing
  derivation, prefix-generalized over the context so the induction goes under
  binders. Their `let` cases need no new theory: dropping a binding from the
  context only makes `gen` more general with no new free variables
  (`gen_more_gen`), the good direction for `typing_ftv_mono`. Also
  `typing_inst_gen` (every instance of a generalization is derivable).

- **The two canonical HM lemmas** (`GoatSound.v`), on which the term-substitution
  lemmas (hence Preservation's `ST-Beta`/`ST-LetV` and Soundness) rest:
  - `typing_weaken` (L4): inserting a middle block of bindings preserves typing;
  - `typing_tsubst_fix` (L5): substituting the type/row variables *not* free in
    the context preserves typing (in the all-`k_Any` environment, where
    algorithm W works).

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
  arguments, an empty program, a block that ends in a binding, a function binding
  after a value binding in the same block, a function binding that is an operand
  (`1 + f = program(x) do x done f(2)`).
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

Side conditions. Duplicate record labels and repeated parameters are lowering
errors that `goat_ln.ott` allows (ADR 0030). `goat_ln.ott` is unchanged; they are
conditions on the term, to be hypotheses of the round-trip theorem T3 where they
matter. T1 does not need them: `close_exp` yields a locally closed term whatever
names repeat, so T1 is stated without them rather than with unused hypotheses.
Recursive function bindings and a block's function group are no longer a
disagreement: `DB_group` is that reading.

`print_parse_roundtrip` (T3): for a closed core term `e` (`scoped 0 e`) whose
labels are numbered by first occurrence in the printed text (`Interned e`), and
a `var_of` that gives the printer's binder names `v0`, `v1`, ... distinct atoms
(`names_distinct`), the PEG relation parses `print e` to a tree `t` and
`Den_goat var_of t e` holds, so `t` denotes exactly `e`.

- **Printer.** The curried style of the Rust printer. A call's callee and a
  projection's base are parenthesised when they are a binding, a number or a
  `Float`; a binding's value is parenthesised when it is a binding or a function
  (a bare function would be a group member). A conditional whose else is the
  unit value is printed without an `else`. The grouped style is not mirrored.
- **Side conditions.** Duplicate labels or repeated parameters are not
  hypotheses of T3. The printer names each binder by its depth, so no name
  repeats; the model's `Den` accepts duplicate labels. They concern the Rust
  front end, which `checker/tests/core_roundtrip.rs` covers by testing.
- **Label table.** `labels` (T1) now lists each distinct label once, in order of
  first occurrence, the numbering lowering gives. Before, it kept repeats, so a
  label after a repeat got a larger index than lowering assigns.
- **Printer alignment.** `GoatPrinterTable.v` is generated: the Rust test fails
  when the committed file differs from what the Rust printer writes
  (`UPDATE_PRINTER_TABLE=1 cargo test -p goat_checker --test core_roundtrip`
  rewrites it), and the Coq build fails when the Coq printer disagrees with a
  row.
- **Not covered.** Free variables (T3 is for programs), the grouped style, a
  `letrec` (T1 reads one; the printer does not write one), the unit value on its
  own, `float(e)`, everything T1 leaves out.

## CI

`.github/workflows/coq.yml` builds this directory under Rocq on the self-hosted
runner image, in its baked `rocq-9` opam switch (Rocq 9.1.1, Ott 0.34, metalib).
The job fails with the expected versions when the switch is missing. It triggers only on
changes under `proofs/**` (or to the workflow), plus manual dispatch, so
ordinary Rust PRs do not pay for a Coq image. It is intended as an
informational check, not a required one — promote it in branch protection once
the development stabilizes.
