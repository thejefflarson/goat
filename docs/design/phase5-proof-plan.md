# Phase 5 proof plan: the elaboration theorem, methods, `self`, dot calls and `::` (design pass)

Status: stages 0 to 7 are done (the close-out is the last row of section 8). The
owner answered section 9; see ADR 0037's 2026-11-22 amendments and `proofs/README.md`
for what was proved and what is open. Issue #454,
part of #435, governed by ADR 0037 (decision 3 and the 2026-11-20 amendment),
ADRs 0031 to 0034. Written against `master` at 49ca7d8, after #488 (iso-recursive
`mu` in the calculus), phase 3 (tags), phase 4 (spread) and `docs/design/w-recursive-types-plan.md`
(#505). The owner delegated the proof-model choices to this pass; each is recorded
in section 3 with the alternatives it beat. No `proofs/`, `checker/` or ADR file
changes in this PR.

Terms. A **mu type** is `typ_Mu B`, a recursive type whose body `B` names itself
by the de Bruijn index `bv 0`. **Unrolling** is `open_typ 0 (mu B) B`.
**Iso-recursive** means a mu and its unrolling are different types and the terms
`fold(e)` and `unfold(e)` convert between them (the calculus today).
**Equi-recursive** means they are the same type (the Rust checker's `Ty::Rec`).
A **knot** is what the checker builds when a variable would have to equal a type
that mentions it: it solves the variable to a recursive type (`tie_ty_knot`,
`tie_row_knot`). **Elaboration** is ADR 0037 decision 3: rewrite a program the
checker accepts into one with explicit folds and unfolds that the iso rules
accept. **W** is the Coq model of inference (`GoatInfer*.v`). **A coercion** is a
chain of folds and unfolds applied to a term. A **head coercion** converts a term
whose type differs from the type it is used at in the outermost constructor only.
**Erasure** `erase e` deletes every `fold` and `unfold`.

## 1. What the checker does today

Read from `checker/src/infer.rs` (`infer_record`, `tie_methods`, `tie_ty_knot`,
`tie_row_knot`, `unify_ty`), `checker/src/lower.rs`, `checker/src/ty.rs` and
ADRs 0031 to 0034.

- **Recursive types are equi-recursive.** `Ty::Rec(binder, body)` equals its
  unrolling. `unify_ty` unfolds a `Rec` at the head when the other side is not
  one, and keeps a set of assumed pairs so unification of two regular trees
  terminates. When a variable `x` would have to equal a type that mentions `x`,
  `tie_ty_knot` solves it to `Rec(v, t[x := v])`, and `tie_row_knot` does the same
  for a row variable whose solution mentions a record or variant with a given
  prefix. A mention is allowed when it is **guarded**: under a record field and a
  function type, or under a tag. At most `MAX_KNOTS_PER_UNIFY` (16) knots per
  top-level unify; a type that outgrows `MAX_UNFOLDED_TERMS` is a spanned "program
  too complex" error, which CLAUDE.md names as the one resource-limit exception
  to "errors come only from the checker".
- **Tags are not recursive types in the calculus.** Phase 3 gave a tag group a
  declaration-named type `grp w T`; `T_Con` and `T_Match` are the fold and unfold
  of a group, built in. So `mu` is needed for records only: ADR 0032's receivers,
  ADR 0034's methods and the "infinite" results some functions have
  (`g = program(p) do {lab0: p, lab1: g(p)} done`).
- **Dot calls and `::` are rewrites in lowering.** `r.f(a1, …)` is `(r.f)(r, a1, …)`;
  a receiver that is a variable or a path of field accesses is repeated, any other
  is bound once to a hidden name (ADR 0031 decisions 1 and 2, `ReceiverKind`).
  `r::f(a…)` is `(r.f)(a…)` and bare `r::f` is `r.f` (ADR 0034 decision 5).
  Lowering records each node in the side tables `Lowered::dot_calls` and
  `Lowered::takes`. After lowering the checker sees only `Proj`, `App` and `Let`.
- **`self` is a name the checker reserves.** A function whose first parameter is
  `self` and that is written directly as a field of a record literal is a method
  (`is_method`). The parser, grammar and proofs read `self` as an ordinary name
  (ADR 0034 implementation addendum 2).
- **A record literal with methods is typed like a `letrec` over its fields**
  (ADR 0034 addendum 3, `infer_record`). Each field gets a slot variable; the
  literal gets one receiver variable `s` and one row variable `ρ`. `s` stands for
  `{l1: slot1, …, ln: slotn | ρ}`, is never bound while the bodies are inferred
  (`self_defs`: unifying `s` with a record unifies that record and keeps `s`),
  and afterwards `tie_methods` binds it once to `μs. {fields | ρ}`. The literal's
  own type is the **closed** row of those fields, each mentioning `s`. `ρ` is
  generalized with a `let`, so each use instantiates its own extension.
  `{x: 1, moved: program(self) do {...self, x: self.x + 1} done}` has the type
  `{x: Int; moved: (S) -> S}` with `S = μs. {x: Int; moved: (s) -> s | ρ}`.
- **The method flag.** `Row::Extend` and `Row::Maybe` carry a `method` type, a
  variable bound to `METHOD` or `PLAIN` (two constants, as presence is `PRESENT`
  or `ABSENT`). `r.f(a)` unifies `f`'s flag with `METHOD`; `r::f`, `(r.f)` and
  plain projection leave it alone; unifying `METHOD` with `PLAIN` is an error
  that names the field. Mono and codegen erase it.
- **Parameter receivers.** A dot call on a parameter (`step = program(p) do p.moved() done`)
  has no literal to tie its receiver, so ADR 0032's occurs-check knots do it, one
  knot per distinct view of the receiver. #433 (PR #567 is its first, size-only
  part) wants one knot per parameter receiver, through a receiver variable with an
  open row closed at generalization, "like `self_defs`". #567's body says that
  changes generalization and is an ADR 0032 amendment under the proof gate.

What the corpus skips today (`cargo run -p goat_checker --release --example
core_corpus`, 40496 programs written):

| Skip | Count | What it holds |
| --- | --- | --- |
| "methods, self or dot calls" | 69 | `r.f(a)`, `r::f(a)`, a `self` parameter, `r::f` as a value; mostly the docs and tests of ADRs 0031 to 0034 and the `closure_shapes` example |
| "the checker infers a recursive type" | 11 | a parameter used as its own argument (`program(v1) do v1({lab1: v1}) done`), a receiver passed to its own field (`program(v2) do (v2.lab2)(v2).lab0 done`), a function whose result nests itself (`{lab0: p, lab1: g1(p)}`) |
| "a recursive group split by a value binding" | 1554 | a block `f = …; v = …; g = …` where `f` and `g` call each other |

The 1554 programs have nothing to do with `mu`, dot calls or methods; section 6
says why the ticket lists them and where they are fixed.

## 2. How the calculus models it

**The route is the one ADR 0037 decision 3 chose: iso-recursive types, and the
checker's equi-recursive types elaborate into them.** This note adds three
readings that the ADR leaves open.

**2.1 Dot calls, `::` and `self` need no new term and no new typing rule.**
Lowering rewrote them to `proj`, `app` and `let` before the checker ran, so the
calculus already has every form. `r.f(a)` on a path receiver is
`app(app(proj(r, f), r), a)`; on any other receiver it is
`let t = e_r in app(app(proj(t, f), t), a)` with `t` a fresh binder (locally
nameless: the arguments are closed, so no shifting). `r::f(a)` is
`app(proj(r, f), a)`. `self` is the first parameter of a `program`. The proof
work is the type side: the recursive types these programs need, and the
elaboration that puts folds and unfolds in.

**2.2 What a method literal elaborates to.** Take `ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}`
and write `S_ρ = mu. {x: Int; moved: (bv 0) -> bv 0 | ρ}`. The elaborated term,
which `GoatRecTypes.v` already types for a one-field `moved`, is

```
ball = {x: 1, moved: program(self) do fold(spread(unfold(self), x, unfold(self).x + 1)) done}
                                  -- self : S_ρ, the body returns S_ρ
ball.moved()  ==>  (ball.moved)(fold(ball))   : S_nil     -- after ρ := nil at the let's instantiation
```

`ball` has the type `{x: Int; moved: (S_ρ) -> S_ρ}`, a closed row whose method
mentions `S_ρ`; `ρ` is a free row variable that `T_Let` generalizes, because the
literal is a syntactic value. At the call `ρ := nil` makes the unrolling of
`S_nil` equal `ball`'s type, so one `fold` passes `ball` as the receiver. A
`big = {...ball, size: 10}` instantiates `ρ := {size: Int}`, which is how
ADR 0034 decision 3's "open to extension" appears in the iso calculus. Every
`self.f` is `(unfold self).f` and every returned `{...self, …}` is folded. Nothing
here needs a rule the calculus lacks; `ap_open_mut` already commutes substitution
with unrolling, so a free row variable inside a mu is harmless.

**2.3 The elaboration theorem is the soundness of W with knots, with an output
term.** ADR 0037 decision 3 says "every program the checker's algorithm accepts
elaborates … into an iso-typed program with the same behaviour", and decision 2
says the algorithm proof is stated over that elaboration. The checker's algorithm
is not in Coq; W is its model, tied to the Rust code by the differential test
(decision 6). So the theorem to prove is about W:

```
infer_elab : forall fuel e D e' T,
  infer_elab fuel e = Some (D, e', T) ->
  typing D nil e' T  /\  erase e' = e
```

W (extended with knots, #508) returns an elaborated term `e'` that the iso rules
type at the type W reports and whose erasure is the input. The second conjunct is
"the same behaviour" made precise: `erase` commutes with evaluation (section 5,
`erase_step`), so `e'` and `e` reach the same value or trap, and one diverges iff
the other does. This needs **no second declarative typing relation** for the
equi-recursive system. Completeness, when the algorithm phase proves it, reads
"if some `e'` with `erase e' = e` has an iso derivation, W accepts `e`", which
quantifies over the placement of folds and unfolds and is the declarative
specification of what a kid's program may be (every program for which folds could
be written). It is the easy direction in reverse: erasing an iso derivation gives
an equi derivation.

**2.4 Where the coercions come from, and the one hard question.** W's unifier
never rewrites the term: after unification each node has a type, and two nodes
that must have the same type may have trees that are equal but iso types that are
not (a `mu B` on one side, its unrolled record on the other). A **head coercion**
repairs that: one `fold` or `unfold` at the node (the spike's `knot_fold_types`
and `knot_unfold_types`). A mismatch **below a function type or a record field**
(`(mu B) -> X` meeting `(R) -> X`) is not repairable by one coercion: it needs
`program(y) do c2(f(c1(y))) done`, an eta-expansion. Then `erase e' ≠ e` (they
agree only up to eta), and the behaviour claim needs a typed coherence relation
instead of an equation. #508's settled sub-decision 3 already says to measure how
often this happens before deciding. This note adopts that and makes it the first
spike of stage 3 (section 8), with the fallback priced in section 3, Q3.

## 3. Decisions

Each is a proof-model choice the owner delegated. **(load-bearing)** marks the
ones whose reversal rewrites later phases.

### Q1. What "the elaboration theorem" states **(load-bearing)**

- **A. Soundness of W with knots, with W returning the term (chosen).** The
  statement of 2.3. One relation (`typing`), no new judgment, and the composition
  with phase 8's completeness is direct. Cost: the theorem cannot be stated or
  proved before W ties knots, so it lands with #508's lemma set, not before.
- **B. A declarative equi-recursive typing relation `typing_eq`, and a translation
  theorem `typing_eq e T -> exists e', erase e' = e /\ typing e' T'`.** Modular:
  the statement does not mention W. Costs a second copy of the ~40 typing rules
  with `T_Conv` extended by an unrolling equation (about 1500 lines, most of it
  mechanical, and a hnf-style inversion for each canonical-forms lemma), plus
  W's soundness against `typing_eq` on top. And `typing_eq` is not what the
  language is: the language is "the checker accepts it", which is W. Rejected.
- **C. An equi-recursive calculus (no `mu` rules, `teq` coinductive).** ADR 0032
  section 5 weighed it and ADR 0037 chose iso. Not reopened. Rejected.

### Q2. How the equality that W's unifier decides is stated **(load-bearing)**

#508 settled it as bounded unrolling; this note adopts it and says what it is: a
relation `T ~~[n] T'` (equal to unrolling depth `n`, indexed so it is decidable and
needs no coinduction) with `T ~~ T'` meaning some `n`. Its decision procedure is the
checker's assumed-pairs search. The same function, extracted, is what the
differential driver uses to compare two recursive types (section 7).
Alternative: a coinductive bisimulation. Simpler to state, harder to compute, no
extracted checker. Rejected, as #508 did.

### Q3. Eta-expansion or a canonical-form restriction **(load-bearing)**

- **A. Head coercions only (chosen, pending the measurement).** `erase e' = e`
  exactly. A program that needs a coercion below a function type or a record field
  is outside the theorem and counted by the corpus under one named skip
  (`DeepCoercion`). The measurement (stage 3, spike): instrument `unify_ty` and log
  each head unfold or fold with the path from the node's type root; count the
  corpus programs with a non-empty path.
- **B. Allow eta-expansion.** `e'` may contain `program(y) do c2(f(c1(y))) done`.
  The behaviour claim becomes a typed coherence relation `e ~[T] e'` (a fold-free
  term and an iso term that agree up to coercion and eta), with a simulation
  lemma: if `e ~[T] e'` and `e` steps, `e'` steps to something related. It needs
  canonical forms (a value of mu type is a `fold`) at every step. I estimate
  1500 to 2000 lines on top of A.
- **C. No coercions: re-type the nodes** (replace every unrolled copy of a mu type
  by the mu, so every node has the folded form). Fails when a node's type
  is the unrolled form with a different tail from the mu's (a method literal's own
  closed row versus `S_ρ`, section 2.2); there the node needs a real `fold` after
  instantiation, which is a head coercion, so C reduces to A.

Decision rule: if the measured count of deep-coercion programs is under 1% of the
programs that tie a knot, A and the named skip; if it is a large share, B. The
architect decides on the number. Nothing before stage 3 depends on it.

**Measured (2026-11-22, stage 3 spike).** `unify_ty` was instrumented (a depth
counter that does not advance when a `Rec` unfolds in place) and every program
`core_corpus` checks was run (63578 checks, release build). A head event is a
`Rec` meeting a non-`Rec`, or two unequal `Rec`s, at depth d from the root of the
unify call. 3693 programs tie a knot or log an event (3652 tie a knot; 41 log an
event without one). Of the 48 programs where a `Rec` meets a non-`Rec`: 29 have
every event at depth 0, 15 reach depth 1, and 4 reach depth 2 or more. Depth 1
is mostly the argument of a call, where the unify root is the callee's function
type, so that coercion is a head coercion on the argument node. Counting depth
1 as deep, 19 of 3693 programs (0.5%) need a coercion below a function type or
a record field; counting only depth 2 and up, 4 (0.1%). Another 6 programs
unify two unequal `Rec`s and nothing else; they need `~~`, not a coercion
below a constructor. The 48 are almost all hand-written (docs, examples,
tests: methods, tag groups, `step(ball)`); the generated programs tie knots
without a `Rec` meeting a non-`Rec`. Q3-A stands, and stage 3 takes the head-coercion route.

### Q4. How `self` is visible to W **(load-bearing)**

W works on locally nameless terms, where a binder has no name, so `program(self)`
is indistinguishable from `program(x)`. ADR 0034 decision 2 makes the difference
matter: a method's `self` has the **record's** type, and all methods in a literal
share one receiver type. So W needs a marker.

- **A. A method field in the record spine (chosen).** `fields` gains `l :: e ; fs`
  next to `l : e ; fs`. It types, steps and substitutes exactly as a plain field.
  Only `T_Obj` (Q5) and W's literal case read it. No new term, no new value, no new
  redex. About 30 definitions over `fields` (open, close, substitution, free
  variables, `fs_set`, `fs_drop`, projection, `typing_fields`, the three
  `GoatInfer` field walkers) gain a case: roughly 400 lines. Ott generates the
  `open`/`close`/`fv`/`lc` companions.
- **B. A wrapper term `meth(e)`.** One more `exp` constructor, so every `exp`
  matcher (about 29 files in #488's experience) gains a case, and a value form
  and a redex or a rule that sees through it. More churn than A for the same
  information.
- **C. No marker; W treats every function field's first parameter as a receiver.**
  Changes which programs are accepted (a plain function's first parameter would
  be forced to the record's type). Wrong.
- **D. No marker; W types methods as ordinary lambdas and ties knots by the
  occurs check (ADR 0032's mechanism).** Same types as trees for a literal with
  one method, and the same accept set there. For two or more methods the accept
  set differs from the checker's (section 3, Q5): W would accept `lit.a()` where
  the checker rejects. Sufficient for soundness, not for the differential test.

### Q5. The shared receiver, as a rule **(load-bearing; owner question 1)**

ADR 0034 decision 2 gives every method of a literal one receiver type, the
literal's own record plus a row `ρ`. That is **strictly less general** than a
receiver per method, and the checker implements it. With the checker on `master`:

```
lit = {a: program(self) do self.x done, b: program(self) do self.y done}
lit2 = {...lit, x: 1}
lit2.a()        # error: record has an unexpected field `y`
```

`a` reads only `x`, but its `self` is the whole literal's receiver, which `b` makes
require `y` too; the same program with `y: 2` added runs. With a receiver per
method (what Q4-D gives) `lit2.a()` is accepted. The calculus's rules today are the
per-method ones, so for completeness ("the checker accepts what the rules accept",
ADR 0037 decision 2) the rule must say the shared version. `T_Obj`:

```
S = mu B,   B = {l1: B1; …; ln: Bn | ρ},   lct 0 S,   guarded B
for each plain field   li : G |- ei : open_typ 0 S Bi
for each method field  li :: G |- ei : open_typ 0 S Bi,  and open_typ 0 S Bi = (S) -> R   (its parameter is S itself)
------------------------------------------------------------------------------------------
G |- {fs} : {l1: open_typ 0 S B1; …; ln: open_typ 0 S Bn}
```

`ρ` is a row variable free in `S`, so a later `T_Let` generalizes it. `T_Obj`
needs no new redex: the premises are `T_Rec`, `T_Abs` and the existing mu rules
with a shared `S`. A literal with no method field keeps `T_Rec`.

W's literal case (how the model finds `S`):

- **A. Pre-bind the receiver (chosen).** Allocate slots `αi` and `ρ`, give every
  method's `self` the plain record type `{l1: α1; …; ln: αn | ρ}`, infer the
  bodies, and unify each method's type with its slot. The slot `αm` then occurs
  in its own solution and #508's variable knot (`knot αm T`, the spike's
  `knot_unrolls`) ties it. No new W machinery. The types are bigger than the
  checker's (each slot's knot contains the other slots, n² terms for n methods)
  but they are the same **regular trees**, which is what the differential compares
  (section 7). I believe so from the construction in 2.2 and the one-method case;
  the stage-5 differential run is the check.
- **B. Mirror `self_defs`.** A receiver variable `s` with a recorded definition,
  unified through its definition, tied once at the end by one `knot s def`. The
  same shape as the Rust types and smaller, but W's state gains a table and
  `infer_sound` gains an invariant over it: I estimate 1500 lines extra. Revisit
  only if A's types are too large for the extracted W to run on the corpus.

If the owner rejects the shared receiver (owner question 1), Q4-D is the whole
methods story and stages 5's marker and `T_Obj` disappear (section 8).

### Q6. The method flag **(load-bearing for completeness, not for soundness)**

- **A. Not modelled (chosen).** The flag only makes the checker reject more
  (`METHOD` against `PLAIN`, a dot call on a plain function, `::` on a method), so
  soundness is unaffected, as for phase 4's `lacks`. The reader erases the flag from
  the type column and skips a program the checker rejected because of it, under a
  narrow `MethodFlag` skip detected from the error (today by message text; the
  stage-2 PR should add a structured error kind in `checker/src/error.rs`, which the
  proof gate does not cover). Documented gap: the calculus accepts
  `r.f(a)` where `f` is a plain `program(x, y)`.
- **B. A slot in `Ext`/`Maybe` like presence** (a `typ`, `METHOD`/`PLAIN`). Closes the
  gap. Touches every row lemma the way phase 4's `row_Maybe` did (~1500 lines in
  28 files, most of it the same case in each mutual induction). The algorithm
  completeness proof needs it; this phase does not.
- **C. A flag on the arrow.** Every `typ_Arrow` matcher changes. More churn than B.

### Q7. Parameter receivers and #433 **(owner question 2)**

The calculus is indifferent to the shape of a knot: any guarded `mu` types, and
W's variable knot and row knot (#508) are the same lemma either way. What can
change is **which programs are accepted and which types they get**. A single knot
per parameter receiver, with the row variable `ρ` shared across unrollings, is a
different regular tree from nested knots with a fresh tail at each level. So
#433's second half is an ADR 0032 amendment, and the proofs should model the
amended rule. Section 7 says how to keep the differential test from depending on
the order #433 and the proof stages land in.

### Q8. Where the split-group programs are fixed

In the corpus reader, as `docs/semantics.md` section 6 already says ("elaboration
hoists the group"): place the `letrec` after the last value binding any member
reads (and no later than the first use of a member). ADR 0003's evaluation-order
check guarantees such a position exists for an accepted program. It needs name
resolution by symbol, which the reader has and the parser fragment does not (the
README's reason for excluding a group after a value binding). Alternatives:
extend the calculus's `letrec` to span interleaved values (a rule with a
different shape, every phase-2 lemma changes) or prove a let-floating lemma
for syntactic values (optional, not needed: the differential compares the hoisted
term's type with the checker's).

## 4. Which lemmas and files change

| File | Change |
| --- | --- |
| new `GoatElab.v` | `erase`; `erase_step`, `erase_traps` (behaviour); `~~[n]` on `typ`/`row`, its reflexivity, symmetry, decidability; the head coercion function and `coerce_typing`; `erase_coerce` |
| `GoatMu.v` | `~~[n]` is stable under `ap_typ` (`ap_open_mut` already commutes it with unrolling) |
| `GoatInfer*.v` | `unify_t` gains `Mu`/`Mu` and `Bvar`/`Bvar`; the occurs check ties a knot instead of failing; `infer` returns an elaborated term; `infer_closed_sound` becomes `infer_elab`; `infer_mu_free` is replaced by what W now returns (a `mu` of a guarded body). The unifier's specification changes from "equal" to "`~~`" |
| `GoatInferMuFree.v` | retired or kept for the knot-free fragment (decide in the stage-4 PR) |
| `goat_ln.ott`, `Goat_ott.v` (stage 5 only) | `fields` gains `fs_meth` |
| `GoatDefs.v` (stage 5) | `T_Obj`; a `fs_meth` case in `fs_set`, `fs_drop`, projection, `typing_fields` |
| `GoatMeta.v`, `GoatSound.v` (stage 5) | the `fs_meth` case of each mutual induction over `fields`; inversion for `T_Obj`; preservation for a literal that steps field by field |
| `GoatDen.v`, `GoatShape.v`, `GoatPrint*.v` (stage 6) | a dot call on a path receiver and on any other receiver (hidden `let`) |
| `GoatAssumptions.v` | `infer_elab` and `erase_step` join the listed theorems |
| new `GoatMethods.v` | worked examples: `ball`, `ball.moved()`, `step(ball)`, `big = {...ball, size: 10}`, the three-method model, what has no derivation |

`typing D G e T`, the kinding environment `D`, `inst`, `gen`, `kres` and the
step relation do not change in stages 3 and 4. Stage 5 changes `fields` and adds
one typing rule.

## 5. What is proved

- **`erase_step`**: if `e'` steps to `e''` then `erase e'' = erase e'` (the step was
  `unfold(fold v) --> v`) or `erase e'` steps to `erase e''`; `traps` likewise. The
  converse needs types: for a closed typed `e'`, if `erase e'` steps to `e1` then
  `e'` reaches some `e''` with `erase e'' = e1` after zero or more fold/unfold
  steps (by `progress` and canonical forms: a closed value of mu type is a
  `fold`). Together `e'` and `erase e'` reach the same value (up to erasing folds)
  or the same trap, and diverge together.
- **`coerce_typing`**: if `T ~~ T'` by a head step and `G |- e : T` then
  `G |- c(e) : T'` with `erase (c e) = erase e`.
- **`infer_elab`** (2.3), 0 admits, no axiom; `progress`, `preservation` and
  `soundness` keep their statements.
- **Examples** in `GoatMethods.v` (section 4).

The `make check-assumptions` list grows by `infer_elab` and `erase_step`.

## 6. The corpus: how the three skips go to 0

A count goes to 0 when its feature lands, and its programs then show up under the
next feature they use or are compared (`differential/README.md`). So "goes to 0"
does not mean "all compared"; each stage below says where the programs go.

**"A recursive group split by a value binding" (1554).** Stage 1, reader only.
For each block the reader already computes the groups and their members; it
places the group at the position of Q8 instead of returning `SplitGroup`, reading
each free variable by symbol (the reader's `var` matches by name first, which a
hoist past a shadowing binding would trip; look up by symbol). No calculus
change, no proofs change. Risk: the 1554 programs have never been compared, so a
real disagreement (the checker's group generalization against `T_Letrec`) may
appear. That is what the test is for. They fall under `NumeralLet` (2938 today,
so it grows), compare, or mismatch.

**"Methods, self or dot calls" (69).** Stage 2 (reader) and stage 5 (rules).

- The reader reads a node in `Lowered::dot_calls` or `Lowered::takes` as the
  `proj`/`app`/`let` of 2.1, a `self` parameter as a parameter, and erases the flag
  from the type column (`Canon::ty` returns `None` on a `METHOD` field today; it
  must read the flag and print past it).
- A program the checker rejected because of the flag goes to `MethodFlag` (Q6).
- A program whose checker types contain a `Rec` goes to `RecursiveType` (11 today).
  **I did not measure how many of the 69 do**: a literal with a method ties
  `s` to a `Rec` even when the result type shows none. Stage 2's report prints it.
- A literal with two or more methods goes to a new `SharedReceiver` skip until
  stage 5, because Q4-D accepts programs the checker rejects there (Q5).
- The rest are compared, in both directions.

**"The checker infers a recursive type" (11, plus whatever stage 2 adds).** Stage 4
(W ties knots). The corpus writer already prints a recursive root type as an
`R` line and the driver reports it skipped. After stage 4 the driver compares it
(section 7), and a node-type `Rec` no longer skips the program. What stage 4 still
leaves out is #508's settled incomplete case, a row variable inside a formed knot
that later unifies with a row mentioning that knot (`DeepKnot`, counted), and Q3-A's
`DeepCoercion` if the measurement picks A.

## 7. Interaction with #508, #433, #564 and the differential test

- **#508 is stage 4.** Its lemma list (knot lemma, equality, coercion lemma, W
  returns the term, row knot, reader and driver) is what 2.3 needs, and its "blocked
  by" is this phase's elaboration ticket. This note proposes they are one effort in
  two tickets, sequenced: stage 3 (coercion and erasure, here) before #508's
  W changes, so that #508's `infer_elab` has the lemmas it uses. Decisions 1, 2, 3
  and 4 of #508 stand (W returns the term; bounded unrolling; measure eta first;
  incomplete on a row variable inside a knot, counted).
- **#433.** It is changing `checker/src/infer.rs` and `ty.rs` now (PR #567 is the
  size-only half), so stage 4's checker-side work is a reader and driver change in
  `core_corpus.rs`, not in the checker. Two touch points to coordinate with
  whoever lands second: (a) `core_corpus.rs` detects a recursive type by
  `format!("{ty:?}").contains("Rec(")`, which a change to `Ty`'s representation
  (shared nodes, a different `Debug`) breaks silently. Stage 2 replaces it with a
  `Ty` predicate. (b) the "program too complex" budgets: a program near the limit
  may be accepted by W and rejected by the checker, or the reverse, after #433
  moves the limits. The reader skips a checker error that is the resource-limit
  diagnostic, under `ResourceLimit`, which CLAUDE.md's exception allows.
  **Keeping the test indifferent to #433's shape change.** The driver compares two
  recursive types as regular trees, not as printed strings (Q2): both sides
  print the type as a mu term, free variables numbered by first occurrence in a
  left-to-right traversal (unrolling repeats a body that was already traversed, so
  the numbering is the same for a type and its unrolling), and the driver decides
  equality with the extracted `~~` decision procedure. A single knot, nested knots,
  a folded or an unrolled root print differently and compare equal. A change of
  *acceptance* or of the tree (the shared `ρ`) still shows as a mismatch, which is
  what should happen.
- **#564** (a `lacks` sort on row variables) is independent. `LacksOnTail` (222) is
  not in this phase's scope. It also touches `sat`, `kres`, `inst` and W's
  substitution invariant, which stage 4 rewrites; whichever lands second merges
  those. Say so in whichever PR is second.
- **Tags.** The "tags and match" skip (185) is phase 3's corpus work, not
  this phase's. Tags carry their own recursion by declaration, so W's knots never
  see a recursive variant.

## 8. Staged PR plan

Sizes are lines added, counting generated `Goat_ott.v` changes separately, calibrated
against phase 3 (#527, +1235 across 25 files) and phase 4 (about 1500 across 28).
Stage 4's range is from #505's estimate for Option B (2500 to 3500) and is the
least certain number here.

| Stage | Contents | Size | Corpus effect |
| --- | --- | --- | --- |
| 0 | this note | 450 (docs) | none |
| 1 | reader hoists split groups (Q8) | ~200 (`core_corpus.rs`, `differential/README.md`) | `SplitGroup` 1554 -> 0 |
| 2 | reader reads dot calls, `::` and `self`; flag erased from the type column; `MethodFlag`, `SharedReceiver`, `ResourceLimit` skips; a `Ty` recursion predicate; a structured error kind for flag errors | ~450 | `MethodsAndDotCalls` 69 -> 0; programs land in compare, `RecursiveType`, `SharedReceiver`, `MethodFlag` |
| 3 | `GoatElab.v`: `erase`, `erase_step`, `~~[n]`, head coercions, `GoatMethods.v` examples; the deep-coercion measurement (spike first, in a scratch file, before the rest) ; ADR 0037 amendment (the reading in 2.3) | ~1100 | none |
| 4 | W ties knots and returns the term (#508), in four PRs. **4.1** `infer_elab` for the fragment W covers today (`GoatInferElab.v`: `typing D nil e' T /\ erase e' = e`; `e'` is `e` because W accepts no `fold` or `unfold`). **4.2** (done: `GoatUnrollEqb.v`, `GoatElabConverse.v`) `unroll_eqb`, a budget-bounded search for `~~[n]` (it needs no assumed-pairs set, since the budget ends the search), sound for `unroll_eq` and not complete, and the typed converse of `erase_step`. **4.3** in two parts. *4.3a (done: `GoatKnot.v`, `GoatInferKnot.v`)*: the knot unifier as a separate function `unify_k` with `unify_k_sound` (`s T1 ~~ s T2`), not yet called by `infer`. *4.3b (done: `GoatCoerce.v`, `GoatClose.v`, `GoatInferW.v`)*: `infer` calls `unify_co` (`unify_t`, then `unify_k` and `coerce_dec`, the head-coercible decision procedure on `chain`) at every join, returns the elaborated term as a fifth component, and `infer_sound` is re-proved with it; a difference below a function type or a record field is a deep coercion and W fails. A recursive group's members still unify with `unify_t`. `infer_elab` is no longer the identity; `infer_mu_free` and `GoatInferMuFree.v` are retired (W builds recursive types), and 4.4 states a guardedness fact in their place. **4.4** (done: `GoatGuard.v`, `GoatInferGuard.v`) `infer_guarded` replaces `infer_mu_free` (every recursive type W returns is guarded; `bind_k` checks the type it binds, so the knot-tying unifier's substitutions are guarded with no hypothesis on its arguments), and the reader and driver compare recursive types as regular trees. Of the 31 recursive-type programs the differential test compares 18, with 0 mismatches; the algorithm refuses 13, 7 because a row variable must itself knot (`DeepKnot`, counted as `K` lines) and 6 because a recursive group's members need a knot. **4.5** (done) knots through recursive groups: `unify_grp` replaces `unify_pw` in W's letrec case and puts the head coercions of a member's result under its lambda (`unify_mem`; `mem_co`/`pw_co` and `unify_grp_sound`), so the six group programs compare (31 of 42 recursive-type programs compared, 0 mismatches). Left: the row knot. The 11 refusals measured by logging each failure in the extracted algorithm: 3 row variable occurs (`occR`), 3 tail occurs (`rewrite_row`), 3 deep coercions, 1 `unify_k` failure with no occurs check, and 1 group member needing a `fold` of the whole lambda | ~3000 over 4 PRs (4.1 is ~200) | `RecursiveType` -> 0 (plus `DeepKnot`, `DeepCoercion` if any) |
| 5 | methods in the rules: `fs_meth`, `T_Obj`, W's literal case (Q4, Q5); ADR 0034 amendment recording the shared receiver as a rule. **Done**: `fs_meth` is a field of the record spine and runs as a plain one; `T_Obj` (`T_Record` now asks for a spine with no method) takes `meths_shared`, each method's type equal up to unrolling to a function of one receiver, the literal's row plus a tail `Rt`; a spread or restrict builds a plain record (`fs_plain`). W's literal case is Q5-A: `infer_obj` infers each method body with the receiver in scope, `tie_obj` unifies the slots with the fields afterwards, and `infer_sound` types the result by `T_Obj`. The reader writes a method `(meth e)`, the driver reads `fs_meth`, and the `SharedReceiver` and method-receiver skips are gone: 13 programs move to compare, 9 compared and 4 refused for a row that must knot (`DeepKnot`). Not done: a Coq non-derivation of `{...lit, x: 1}.a()` (the algorithm and the checker reject it, differential line 352); it needs an inversion lemma for `unroll_eq` | ~1200 | `SharedReceiver` -> 0 |
| 6 | parser fragment: dot call on any receiver (a path repeats, another receiver binds a hidden `let`, ADR 0031 decision 2); `::` and the variable-receiver dot call are already in (`DP_take`, `DP_dot_call`); T1, T3 cases | ~350 | none (grammar and fragment, no corpus count) |
| 7 | **Done.** close: README, `docs/semantics.md`, ADR 0037 and this plan brought up to date; `GoatAssumptions.v` lists 19 theorems; the corpus skip table is in `proofs/README.md`; `unify_pw` (replaced by `unify_grp`) deleted. Open, with links: #606 (11 recursive programs W refuses), #564 (`lacks` on a row variable, 222 programs), the missing Coq non-derivation of `{...lit, x: 1}.a()`, the 65 `SplitGroup` programs | ~250 | `SplitGroup` 1554 -> 65; `MethodsAndDotCalls`, `SharedReceiver` -> 0; `RecursiveType` is compared (31 of 42) |

Ordering: 1, 2 and 6 are independent of each other and of 3 to 5, and can start now.
3 before 4. 4 before 5 (5's W case uses 4's knot). 7 last. Stage 5 is the one the
owner's answer to question 1 can cancel. Stage 3 and stage 4a can be proved in
parallel by two people after the measurement.

Proof gate (ADR 0037). The gate fires on `grammar/goat.peg`, `checker/src/{infer,lower,ty}.rs`
and `prelude/prelude.goat` without a `proofs/` change. No stage here changes the
surface grammar (`fs_meth` is a calculus form, not syntax). Stage 2's `Ty` predicate
touches `ty.rs`, so it carries the `no-semantics-change` label and a
`No semantics change:` line, as CLAUDE.md permits for a change outside typing, grammar
and evaluation. Stages 3 to 6 change `proofs/`, which satisfies the gate.

## 9. Owner questions

These are the two points where the plan changes what the language is, or depends
on a language decision the owner has not made.

1. **Is the shared receiver the intended language?** Section 3 Q5. As implemented
   (ADR 0034 decision 2) every method in a literal shares one receiver type, so
   with `{a: program(self) do self.x done, b: program(self) do self.y done}`,
   `{...lit, x: 1}.a()` is rejected ("unexpected field `y`") though `a` reads only
   `x`. A receiver per method would accept it, and is simpler to prove (no marker,
   no `T_Obj`; stage 5 is cancelled). It is what ADR 0034 rejected because "tying
   those views into one recursive type does not finish for three methods", which
   concerns the checker's algorithm, not what a rule can say. Options: keep the
   shared receiver (this plan models it); or amend ADR 0034 to per-method
   receivers and accept the algorithm cost. I recommend keeping it: it is decided,
   shipped and tested, and the proof can encode it. The surprise for a kid is the
   error text, which names the field `y` but not `b`; a better message is a
   checker ticket, not a proof one.
2. **Does #433's single knot per parameter receiver go ahead?** PR #567 says it is
   an ADR 0032 amendment "with the owner's sign-off". It changes which trees a
   parameter receiver gets (a shared `ρ` in place of a fresh tail per level), so it
   can change acceptance. The proofs stay valid for any guarded mu either way; W's
   model (stage 4) should match whichever rule the checker has when stage 4 starts.
   If the amendment is pending then, stage 4 models nested knots (ADR 0032 as it
   stands) and the stage after #433 adds the receiver variable, the way section 3,
   Q5-B does for a literal.

Everything else here is proof-internal and decided in section 3 (including Q3,
whose number the architect reads off the spike), so nothing waits on the owner
except these two.

## 10. Risks

Most serious first.

1. **The deep-coercion count (Q3).** If many programs need eta, stage 3 grows by
   1500 to 2000 lines and `erase e' = e` becomes a typed coherence relation. The
   spike is the first task of stage 3 and is cheap (an instrumented
   `unify_ty` and one corpus run). If it comes back large, report before any other
   stage 3 work.
2. **Stage 4's size.** 3000 lines is the least reliable number. The unifier
   specification changes from "equal" to "`~~`" and `infer_sound`'s induction is
   redone with an output term; the phase-2 lesson is that a change of judgment late
   rewrites everything, and this changes a statement, not the judgment. The
   mitigation is #508's: the spike already proves the variable knot against the real
   rules with 0 admits and no axiom (`docs/design/spikes/KnotSpike.v`).
3. **Pre-bound receivers' type size (Q5-A).** n methods give n² terms per type in
   the model. Fine for the proofs (fuel, not a budget); the extracted W must still
   run the corpus's literals, the largest of which has five methods.
4. **The row variable inside a knot** (ADR 0032's multi-prefix hole). W stays
   incomplete there, counted as `DeepKnot`. A shared-binder mu would close it and is
   not scheduled.
5. **Reader trust grows.** The hoist, the dot-call reading and the flag erasure are
   unverified reader code compared against the checker, like `float(e)`. The
   differential test is the check; none is a theorem.
6. **Method flag gap (Q6-A).** The rules accept `r.f(a)` for a plain function
   taking the record first; the checker rejects it (ADR 0034 decision 4). A
   completeness proof for the whole language needs Q6-B, and the README says so.
