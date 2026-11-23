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

**L1, instance order on contexts and schemes.** `sch_le s' s`: every instance of
`s'` (under the sorts the scheme records) is an instance of `s`; `ctx_le G' G` is
the pointwise order. Two lemmas: `typing_ctx_le` (a derivation under a context of
more general schemes stays a derivation under any instance of it) and `gen_mono`
(generalizing a more specific type over a more specific context gives a scheme
that is no more general, with the recorded sorts carried by `kres`). The `Tm` pin
joins both: `pin_ctx Tm G` is a context with one more binding, so `gen_mono` is
proved for `gen (pin_ctx Tm G)`. This is where the rewritten `T_Let` of stage 7.1
helps: its premise says which variables the pin holds. About 900 lines.

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
