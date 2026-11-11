# Formal semantics — core goat

This is goat's first written formal semantics: a small-step operational
semantics and a declarative type system for **core goat**, together with the
exact statements of the **progress** and **preservation** theorems we intend to
mechanize in Coq. It is the contract the proof development (ADR
[0008](adr/0008-formal-verification-strategy.md), tracker issues #68–#72) is
written against. The companion machine source is
[`proofs/goat.ott`](../proofs/goat.ott); the typeset rules below and the Coq
definitions are both generated from that one Ott file so they cannot drift.

The job of this model is narrow and deliberate: make the **sharp edge** —
lambda-bound parameters are monomorphic (docs/plan.md, "Known limitation") —
*stateable and provable*, so the later rank-2 fix (#72) can be shown to repair
it without reintroducing unsoundness. Everything that does not bear on that
theorem is left out, and §8 says exactly what and why.

The model is kept faithful to the real checker, not to an idealized variant. The
type and row grammar mirrors [`checker/src/ty.rs`](../checker/src/ty.rs)
(`Ty`/`Row`), and the typing and row rules mirror
[`checker/src/infer.rs`](../checker/src/infer.rs) (`infer`, `unify`,
`unify_row`, `rewrite_row`, `generalize`, `instantiate`). Where the model and
the implementation diverge, §8 flags it.

## 1. Scope

**In the core.** A call-by-value lambda calculus — goat's `program` — with:

- n-ary abstraction `program(x₁,…,xₖ) do e done` and n-ary application
  `e(e₁,…,eₖ)` (goat functions are genuinely n-ary, not curried; see
  [`Ty::Func(Vec<Ty>, Box<Ty>)`](../checker/src/ty.rs) and ADR 0004);
- Hindley–Milner `let`-generalization: a binding `x = e₁  e₂` generalizes, so
  `=`-bound names are polymorphic; **lambda-bound parameters stay monomorphic**
  (this asymmetry *is* the sharp edge);
- two base types, `Number` and `Bool`, each inhabited only by constants
  (numerals, `true`, `false`);
- records as **scoped-label rows** (Leijen, *Extensible records with scoped
  labels*, `papers/scopedlabels.pdf`): construction `{l₁: e₁,…,lₖ: eₖ}` and
  field projection `e.l`, with Leijen's row-equivalence relation.

Values are immutable: record values and closures (program literals) are values,
and there is no mutable reference, cell, or assignment in the language.

**Declarative, not algorithmic.** We model and (in #70–#71) prove soundness of
the **declarative** type system — well-typed closed terms do not get stuck. We
do *not* prove soundness or completeness of Algorithm W, unification, or
`rewrite_row`; those are a strictly larger, separate effort, out of scope per
ADR 0008. The checker's unification is a known sound-and-complete *algorithm*
for the declarative relation (Leijen, Thms 1–2); the declarative relation is
what the sharp-edge theorem is about.

**Out of the core (modeled by nothing — see §8 for the "why").** Reference
counting / heap / the Perceus model; variants, `match`, and recursive (μ)
types; strings; the `Unit` type; `if`/conditionals and arithmetic (the
eliminators of `Bool` and `Number`); numeric constraints; monomorphization;
recursive and mutually-recursive bindings.

## 2. Syntax

Term variables `x, y, z, f, g, m, p`; labels `l`; numeral constants `n`. Type
variables `α, β`; row variables `r, s`. Metavariables range over: `e` terms,
`v` values, `τ` monotypes, `ρ` rows, `σ` type schemes, `Γ` contexts.

```
e  ::=  x                              variable
     |  n  |  true  |  false           constants
     |  program(x₁,…,xₖ) do e done     abstraction        (k ≥ 0, the xᵢ distinct)
     |  e(e₁,…,eₖ)                     application        (k ≥ 0)
     |  x = e₁  e₂                     binding (let)      (x bound in e₂ only)
     |  {l₁: e₁, …, lₖ: eₖ}            record             (k ≥ 0)
     |  e.l                            field projection

v  ::=  n  |  true  |  false           constant value
     |  program(x₁,…,xₖ) do e done     closure value
     |  {l₁: v₁, …, lₖ: vₖ}            record value

τ  ::=  Number  |  Bool               base types
     |  (τ₁,…,τₖ) → τ                  function type
     |  {ρ}                            record type
     |  α                              type variable

ρ  ::=  ·                             empty row (closed tail)
     |  r                             row variable (open tail)
     |  l : τ ; ρ                     row extension

σ  ::=  τ  |  ∀ α₁…αₘ r₁…rₙ. τ        type scheme (monotype, or quantified)

Γ  ::=  ·  |  Γ, x : σ                typing context
```

The binding form `x = e₁  e₂` is goat's `name = value  rest`; it is written here
with an explicit body `e₂`. A trailing binding with no body (`name = value` as
the whole program) is `x = e₁  x`, which is well-typed iff `e₁` is, and whose
value is `e₁`'s — so the core needs no separate construct for it.

`{ρ}` is a record whose fields are the row `ρ`. We write a row left-to-right as
`l₁:τ₁ ; … ; lₖ:τₖ ; t` where the tail `t` is `·` (a *closed* row, the kind a
record *literal* produces) or a row variable `r` (an *open* row, what field
access demands). Leijen's bar notation `{l:τ | ρ}` is sugar for `{l:τ ; ρ}`; we
use `;` throughout to match `Row::Extend`. **Duplicate labels are allowed and
retained** (`{x:τ ; x:τ' ; ·}` is a legal two-field row), which is the whole
point of scoped labels.

Type and row variables are **not** term binders. They are a free-variable set
acted on by a kind-respecting type/row substitution over types, schemes, and
contexts (§5), exactly as `checker/src/ty.rs` treats `TypeVar`: one id space,
each id used in exactly one role (type var or row var). Only `x` in
`program(…) do e done` and `x` in `x = e₁ e₂` are term binders; the
mechanization (#70) treats those locally-namelessly (metalib/LNgen).

## 3. Row equivalence

Records are equal up to permutation of **distinct** labels; fields that share a
label keep their relative order. This is Leijen's scoped-label equality (Figure
1 of the paper), lifted congruently through all of `τ`. We write it `≅`, defined
mutually on types and rows as the least relation closed under these rules.

```
——————————————— (≅-num)     ——————————————— (≅-bool)     ——————— (≅-tvar)
 Number ≅ Number             Bool ≅ Bool                   α ≅ α

 τ₁ ≅ τ₁'  …  τₖ ≅ τₖ'   τ ≅ τ'
—————————————————————————————————— (≅-arrow)
 (τ₁,…,τₖ)→τ ≅ (τ₁',…,τₖ')→τ'

   ρ ≅ ρ'                  τ ≅ τ'     ρ ≅ ρ'
——————————— (≅-rec)      ——————————————————————— (≅-head)
  {ρ} ≅ {ρ'}               l:τ ; ρ  ≅  l:τ' ; ρ'

——————— (≅r-empty)      ——————— (≅r-var)
 · ≅ ·                    r ≅ r

      l ≠ l'
———————————————————————————————————— (≅-swap)
 l:τ ; l':τ' ; ρ  ≅  l':τ' ; l:τ ; ρ

 τ ≅ τ'      τ' ≅ τ''          ρ ≅ ρ'    ρ' ≅ ρ''        (symmetric closure
—————————————————— (≅-trans)  —————————————————— (≅r-trans)  of all of the above
   τ ≅ τ''                       ρ ≅ ρ''                      is included)
```

`(≅-swap)` is the only non-structural rule and the only one that reorders a row.
It fires **only when `l ≠ l'`**, so it can permute distinct labels freely but
can never move one `l`-field past another `l`-field. Reflexivity follows from
the atom rules plus the congruences; we include symmetry and transitivity so `≅`
is a genuine equivalence and a congruence. This matches `papers/scopedlabels.pdf`
Figure 1 (`eq-const`, `eq-var`, `eq-app`, `eq-head`, `eq-swap`, `eq-trans`),
specialized to goat's grammar.

**Characterization (the equational theory B3 depends on).** For a row `ρ` and a
label `l`, let `π_l(ρ)` be the list of field types carried by `l`, in the order
they occur in `ρ`. Then:

> `ρ ≅ ρ'` **iff** `ρ` and `ρ'` have the same tail (`·` ≅ `·`, or the same row
> variable `r`), the same set of labels, and for every label `l`, `π_l(ρ)` and
> `π_l(ρ')` have equal length and are componentwise `≅`.

In words: a row is, up to `≅`, a finite map from each label to a *list* of field
types (mod `≅`); `≅` permutes distinct labels and nothing else. This is the
precise theory the row lemmas (§7, L1–L3) pin down, and completeness of the
swap-generated congruence with respect to this semantic characterization is the
single hardest row obligation for the Coq development (§9).

The checker realizes `≅` operationally through `rewrite_row`
([`infer.rs`](../checker/src/infer.rs)), which surfaces a label `l` by searching
past *differing* labels while keeping their position — Leijen's Figure 3 row
rewriting — and so surfaces the **first** `l`. The declarative counterpart is
`(≅-swap)` plus lemma L3 (§7); both agree that `.l` names the first `l`.

## 4. Typing

The judgment `Γ ⊢ e : τ` assigns a **monotype** to a term. Schemes appear only
in the context and are introduced at a binding (`T-Let`) and eliminated at a
variable (`T-Var`). The instance relation `τ ≺ σ` and the context's
generalization are defined in §5.

```
 x : σ ∈ Γ      τ ≺ σ
———————————————————————— (T-Var)      ———————————————— (T-Num)
       Γ ⊢ x : τ                       Γ ⊢ n : Number

———————————————— (T-True)      ———————————————— (T-False)
 Γ ⊢ true : Bool                Γ ⊢ false : Bool

 Γ, x₁:τ₁, …, xₖ:τₖ ⊢ e : τ
————————————————————————————————————————————————— (T-Abs)
 Γ ⊢ program(x₁,…,xₖ) do e done : (τ₁,…,τₖ) → τ

 Γ ⊢ e : (τ₁,…,τₖ) → τ      Γ ⊢ eᵢ : τᵢ   (each i)
——————————————————————————————————————————————————— (T-App)
            Γ ⊢ e(e₁,…,eₖ) : τ

 Γ ⊢ e₁ : τ₁      σ = gen(Γ, τ₁)      Γ, x:σ ⊢ e₂ : τ₂
———————————————————————————————————————————————————————— (T-Let)
            Γ ⊢ (x = e₁  e₂) : τ₂

 Γ ⊢ eᵢ : τᵢ   (each i)
——————————————————————————————————————————————————— (T-Record)
 Γ ⊢ {l₁: e₁, …, lₖ: eₖ} : {l₁:τ₁ ; … ; lₖ:τₖ ; ·}

 Γ ⊢ e : {l : τ ; ρ}             Γ ⊢ e : τ      τ ≅ τ'
——————————————————— (T-Proj)    ———————————————————————— (T-Conv)
   Γ ⊢ e.l : τ                        Γ ⊢ e : τ'
```

Rule by rule:

- **`T-Var`** instantiates: a use of `x` may take any monotype `τ` that is a
  generic instance of `x`'s scheme (`instantiate`, replacing quantified
  variables with fresh monotypes/rows). A lambda-bound `x` has the mono scheme
  `σ = τ_x`, whose only instance is `τ_x` itself — so every use of a parameter
  gets the *same* monotype. A `=`-bound `x` may have quantifiers, so each use
  can differ. This single difference is the sharp edge.
- **`T-Abs`** binds each parameter at a **monotype** `τᵢ` (no `∀`). The body is
  checked with those monomorphic assumptions; the function's type records the
  arity `k`. Matches `infer.rs`, which gives each param a `Scheme::mono`.
- **`T-App`** requires the callee to have a function type whose arity matches the
  number of arguments, and each argument to have the corresponding domain type.
  Arity disagreement is a type error, never a stuck term (matches the arity
  check in `unify`'s `Func` case).
- **`T-Let`** generalizes: `e₁` is typed, its type `τ₁` is generalized against
  the current context (§5), and the resulting scheme is what `x` is bound to in
  `e₂`. Generalization is **unrestricted** — it applies to every `e₁`, not only
  syntactic values. This is sound here precisely because the language is pure:
  the value restriction exists only to tame mutable references, and core goat
  has none (§8).
- **`T-Record`** builds a **closed** row (tail `·`) in written order, so a
  literal's type records its labels and their order, duplicates included.
- **`T-Proj`** requires `e` to have a record type whose row presents `l` at the
  head, and gives `e.l` that field's type. Because `(≅-swap)` never moves one
  `l` past another `l`, `T-Conv` can bring only the **first** `l` to the head —
  so `T-Proj` types `e.l` at the type of the first `l`, exactly as the
  operational rule `ST-ProjRec` (§6) selects the first `l`.
- **`T-Conv`** closes typing under `≅`: anywhere a type is produced, an
  equivalent type may be used. This is where row reordering happens — e.g.
  passing a `{b:Bool ; a:Number ; ·}` value where `{a:Number ; b:Bool ; ·}` is
  expected (`a ≠ b`, so `(≅-swap)` applies). A standalone conversion rule keeps
  every elimination form oblivious to row order; the cost is one extra case in
  every induction, discharged by L2 (§7). (An equivalent presentation folds `≅`
  into `T-App` and `T-Proj`, Leijen's style; see §9 for the mechanization
  trade-off.)

## 5. Schemes: free variables, generalization, instantiation

```
ftv(τ), ftv(ρ)   free type and row variables of a type / row
ftv(∀ V. τ)  =   ftv(τ) \ V
ftv(Γ)       =   ⋃ { ftv(σ) : (x:σ) ∈ Γ }
```

**Generalization** quantifies exactly the variables free in the type but not the
context:

```
gen(Γ, τ)  =  ∀ (ftv(τ) \ ftv(Γ)). τ
```

This is `Inferer::generalize`: the difference of the type's free variables and
the environment's. Both type and row variables are quantified.

**Instantiation** `τ ≺ σ`: for `σ = ∀ α₁…αₘ r₁…rₙ. τ₀`, we have `τ ≺ σ` when
`τ = [α₁↦τ₁,…,αₘ↦τₘ, r₁↦ρ₁,…,rₙ↦ρₙ] τ₀` for some monotypes `τⱼ` and rows `ρⱼ`
(kind-respecting: type variables go to types, row variables to rows). A monotype
`σ = τ₀` has `τ₀` as its only instance. This is `Inferer::instantiate` (fresh
images per use site).

A **type/row substitution** `θ` maps type variables to monotypes and row
variables to rows, applied capture-avoidingly to `τ`, `ρ`, `σ` (skipping a
scheme's own quantified variables), and pointwise to `Γ`. It is the model's
counterpart of walking `subst`/`row_subst` in the checker.

## 6. Operational semantics

Small-step, call-by-value, left-to-right, substitution-based: `e ⟶ e'`. The
redex rules:

```
——————————————————————————————————————————————————————————————— (ST-Beta)
 (program(x₁,…,xₖ) do e done)(v₁,…,vₖ) ⟶ e[x₁↦v₁, …, xₖ↦vₖ]

————————————————————————— (ST-LetV)
 (x = v  e₂) ⟶ e₂[x↦v]

 lⱼ = l      l ∉ {l₁, …, lⱼ₋₁}
——————————————————————————————————— (ST-ProjRec)
 {l₁:v₁, …, lₘ:vₘ}.l ⟶ vⱼ
```

`ST-ProjRec` selects the **first** field labeled `l` (side condition: no earlier
field carries `l`), matching `rewrite_row` and `T-Proj`. The congruence rules
fix left-to-right evaluation order:

```
       e ⟶ e'                      v₁…vᵢ₋₁ values    eᵢ ⟶ eᵢ'
————————————————————————— (ST-App1)  ——————————————————————————————————————————— (ST-App2)
 e(e₁,…,eₖ) ⟶ e'(e₁,…,eₖ)            v(v₁,…,vᵢ₋₁,eᵢ,…,eₖ) ⟶ v(v₁,…,vᵢ₋₁,eᵢ',…,eₖ)

      e₁ ⟶ e₁'                     v₁…vᵢ₋₁ values    eᵢ ⟶ eᵢ'
——————————————————————— (ST-Let1)   ——————————————————————————————————————————————————— (ST-Rec)
 (x=e₁ e₂) ⟶ (x=e₁' e₂)            {…,lᵢ₋₁:vᵢ₋₁,lᵢ:eᵢ,…} ⟶ {…,lᵢ₋₁:vᵢ₋₁,lᵢ:eᵢ',…}

   e ⟶ e'
——————————————— (ST-Proj1)
 e.l ⟶ e'.l
```

Values do not step. A binding reduces by first evaluating `e₁` to a value
(`ST-Let1`) and then substituting (`ST-LetV`); because `e₁` is closed-up-to-`Γ`
and fully evaluated before substitution, the polymorphic substitution lemma (L6b,
§7) applies and `let`-polymorphism is sound without a value restriction. `⟶*` is
the reflexive-transitive closure of `⟶`.

## 7. Metatheory

**Definitions.** A term is a *value* if it is in the `v` grammar. A term `e` is
*stuck* if it is not a value and no `e'` has `e ⟶ e'`. Stuck terms are exactly
the errors a type system must rule out: projecting an absent label, calling a
non-function, calling at the wrong arity, applying `.l` to a non-record.

The proofs (#71) rest on these lemmas; they are stated here so #70 knows the
obligations it must generate.

- **L1 — `≅` is a congruence equivalence.** `≅` (on types and rows, mutually) is
  reflexive, symmetric, transitive, and a congruence for every type and row
  constructor; it is the least such relation containing `(≅-swap)`. *(= Leijen
  Fig. 1.)*
- **L2 — `≅` preserves head shape ("no confusion").** If `τ ≅ τ'` then `τ` and
  `τ'` have the same outermost constructor: `Number ≅ τ'` ⟹ `τ' = Number`;
  likewise `Bool`; `(τ₁,…,τₖ)→τ ≅ τ'` ⟹ `τ' = (τ₁',…,τₖ')→τ'₀` with the **same
  arity `k`** and componentwise `≅`; `{ρ} ≅ τ'` ⟹ `τ' = {ρ'}` with `ρ ≅ ρ'`. In
  particular `Number ≅ Bool` is *not* derivable, and arities never change. This
  is what lets canonical forms survive `T-Conv`.
- **L2′ — `≅` preserves labels.** If `ρ ≅ ρ'` then they have the same tail and,
  for each label `l`, the same-length, componentwise-`≅` list `π_l` (the
  characterization in §3). Hence rows with different label sets (e.g.
  `{x:Number;·}` vs `{x:Number;y:Number;·}`) are never `≅`.
- **L3 — row surfacing (scoped-label core).** If `ρ ≅ (l:τ ; ρ')`, then `ρ`
  contains a field labeled `l`; letting `(l:τⱼ)` be the **first** `l`-field of
  `ρ`, we have `τⱼ ≅ τ` and `ρ' ≅ (ρ minus its first l-field)`. So the type `τ`
  that `T-Proj` reads off is determined up to `≅` by the first `l`. This is the
  declarative analogue of `rewrite_row` and the bridge between `T-Proj` and
  `ST-ProjRec`.
- **L4 — structural lemmas.** Weakening, permutation, and `≅`-respecting
  variants, for `Γ`.
- **L5 — type/row substitution preserves typing.** If `Γ ⊢ e : τ` and `θ` is a
  kind-respecting type/row substitution, then `θΓ ⊢ e : θτ`. (Drives
  instantiation, and the `let` case below.)
- **L6 — term substitution.**
  - **(a) monomorphic:** if `Γ, x:τ' ⊢ e : τ` and `Γ ⊢ v : τ'`, then
    `Γ ⊢ e[x↦v] : τ`. (For `ST-Beta`.)
  - **(b) polymorphic:** if `Γ, x:σ ⊢ e : τ` and `Γ ⊢ v : τ₀` where
    `σ = ∀ V. τ₀` and `V ∩ ftv(Γ) = ∅`, then `Γ ⊢ e[x↦v] : τ`. (For `ST-LetV`.)
    Each occurrence of `x` used `v` at some instance `θτ₀` of `σ`; by L5, `v`
    has that instance because the quantified `V` are not free in `Γ`.
- **L7 — canonical forms.** If `· ⊢ v : τ` for a value `v`:
  - `τ ≅ Number` ⟹ `v` is a numeral `n`;
  - `τ ≅ Bool` ⟹ `v ∈ {true, false}`;
  - `τ ≅ (τ₁,…,τₖ)→τ₀` ⟹ `v = program(x₁,…,xₖ) do e done` with **exactly `k`**
    parameters;
  - `τ ≅ {ρ}` ⟹ `v = {l₁:v₁,…,lₘ:vₘ}` whose natural row
    `ρ_v = (l₁:τ₁;…;lₘ:τₘ;·) ≅ ρ`; and for any `(l:τ'';ρ'') ≅ ρ`, `v` has a
    first-`l` field whose value has a type `≅ τ''`.

  (Each case: induction on the value's typing, using L2/L2′ to push `T-Conv`
  through and L3 for the record case.)

### Progress

> **Theorem (Progress).** If `· ⊢ e : τ`, then either `e` is a value or there
> exists `e'` with `e ⟶ e'`.

Proof by induction on `· ⊢ e : τ`. `T-Conv` uses the IH directly (being a value
or being able to step does not depend on the type). `T-App`: by L7 the evaluated
callee is a `k`-ary `program` and the arguments are `k` values, so `ST-Beta`
fires (or a subterm steps by `ST-App1/2`). `T-Proj`: by L7 and L3 the evaluated
record has a first-`l` field, so `ST-ProjRec` fires (or `ST-Proj1`). `T-Let`:
either `e₁` steps (`ST-Let1`) or it is a value and `ST-LetV` fires. Constants,
abstractions, and record values are values. **No well-typed closed term is
stuck.**

### Preservation

> **Theorem (Preservation / subject reduction).** If `Γ ⊢ e : τ` and `e ⟶ e'`,
> then `Γ ⊢ e' : τ`.

Proof by induction on the derivation of `e ⟶ e'` (equivalently on `Γ ⊢ e : τ`),
inverting typing through `T-Conv` with L2/L2′. `ST-Beta` uses L6a; `ST-LetV`
uses L6b (its side condition `V ∩ ftv(Γ) = ∅` holds because `gen` quantifies
exactly `ftv(τ₁) \ ftv(Γ)`); `ST-ProjRec` uses L7/L3 to show the first-`l`
value has the projected type `τ`; the congruence rules use the IH. The theorem
is stated for arbitrary `Γ` because the induction needs it; soundness uses the
closed case `Γ = ·`.

### Soundness

> **Corollary (Type soundness).** If `· ⊢ e : τ` and `e ⟶* e'`, then `e'` is not
> stuck: `e'` is a value or steps further.

Immediate from Progress and Preservation. This is the theorem the whole
development exists to establish, and the fixed target the sharp-edge fix (#72)
must preserve.

## 8. The sharp edge, worked

These are the four "Known limitation" programs from docs/plan.md as derivations
and non-derivations. Throughout, `I ≡ program(x) do x done`; by `T-Abs`/`T-Var`,
`· ⊢ I : (α)→α` for any `α`. We write `a = e₁  e₂` for the inner binding whose
body `e₂` ignores `a` — it forces `e₁` to be typed, then types `e₂`.

### 8.1 `m = {id: program(x) do x done}  (a = (m.id)(1)  (m.id)(true))` — **accepts**

- `T-Record` on `{id: I}` with `· ⊢ I : (α)→α` gives `{id: I} : {id:(α)→α ; ·}`.
- `gen(·, {id:(α)→α ; ·}) = ∀α. {id:(α)→α ; ·}`, since `α ∉ ftv(·)`. Call it
  `σ_m`; bind `m : σ_m`.
- First use: `T-Var` instantiates `σ_m` at `α := Number`, so
  `m : {id:(Number)→Number ; ·}`, `T-Proj` gives `m.id : (Number)→Number`, and
  `T-App` with `1 : Number` gives `(m.id)(1) : Number`. Bind `a : Number`.
- Second use: `T-Var` instantiates `σ_m` **again**, at `α := Bool`, so
  `m.id : (Bool)→Bool` and `(m.id)(true) : Bool`.
- Whole program: `Bool`. ✓

It accepts because `m` itself is generalized, so **each mention of `m`
re-instantiates `α`**. The field `id` is not independently polymorphic; the
record `m` is, and that is enough.

### 8.2 `use = program(m) do a = (m.id)(1)  (m.id)(true) done` — **rejects** (the sharp edge)

Typing the body needs `Γ, m:τ_m ⊢ …`, with `m` bound at a **monotype** `τ_m`
(`T-Abs`, no `∀`). `m.id` requires, by `T-Proj` (+ `T-Conv`), that
`τ_m ≅ {id:τ_id ; ρ}` for a single fixed `τ_id`.

- `(m.id)(1)` forces, by `T-App`, `τ_id ≅ (Number)→τ`.
- `(m.id)(true)` reuses the **same** `τ_id` (a monotype has only itself as
  instance) and forces `τ_id ≅ (Bool)→τ'`.

So `(Number)→τ ≅ (Bool)→τ'`, which by L2 forces `Number ≅ Bool` — not derivable.
No `τ_id` exists, so there is no derivation of the body, and `use` is
untypeable; the program is rejected. The checker reports this as the targeted
"`m` is a parameter, so it can only be used at one type here" error
([`unify_use`](../checker/src/infer.rs)). ✗

### 8.3 `both = program(f) do a = f(1)  f(true) done` — **rejects** (no record needed)

`T-Abs` binds `f : τ_f` at a monotype. `f(1)` forces `τ_f ≅ (Number)→τ`;
`f(true)` forces the same `τ_f ≅ (Bool)→τ'`. By L2, `Number ≅ Bool` — impossible.
No derivation; rejected. This is the sharp edge with no record in sight, and it
is the case only the rank-2 fix (#72) can repair. ✗

### 8.4 `getx = program(p) do p.x done` with `use2 = program(g) do a = g({x:1})  g({x:2,y:3}) done` — **rejects** (row mismatch)

`getx` types fine and polymorphically: `T-Abs` binds `p : {x:α ; r}` (a monotype
that happens to be an open record), `T-Proj` gives `p.x : α`, so
`getx : ({x:α ; r})→α`, and `gen` yields `σ_getx = ∀α r. ({x:α ; r})→α`.

`use2` does not. `T-Abs` binds `g : τ_g` at a monotype.

- `g({x:1})`: `T-Record` gives `{x:1} : {x:Number ; ·}`, so `T-App` forces
  `τ_g ≅ ({x:Number ; ·})→τ`.
- `g({x:2,y:3})`: `{x:2,y:3} : {x:Number ; y:Number ; ·}`, so
  `τ_g ≅ ({x:Number ; y:Number ; ·})→τ'`.

By L2 these force `{x:Number ; ·} ≅ {x:Number ; y:Number ; ·}`, i.e. two rows
with label sets `{x}` and `{x,y}`; by L2′ they are not `≅`. No derivation;
rejected (`record is missing field y`). ✗

A **generalized** `g` would re-instantiate the row variable `r` at each call —
`σ_getx`'s `∀r` is exactly that freedom — and both calls would type. A
monomorphic parameter cannot, which is why `use2(getx)` is rejected even though
`getx` is a perfectly good polymorphic function.

## 9. Modeling decisions and faithfulness notes

Each choice below is a deliberate simplification toward the smallest core that
makes §7 and §8 stateable (ADR 0008), with its justification and any gap from
`checker/src`.

- **RC / heap / Perceus abstracted away.** The operational semantics is
  substitution over immutable values. Reference counting is a memory strategy
  that cannot make a well-typed term get stuck, so it changes neither Progress
  nor Preservation; modeling it is large and buys the sharp-edge theorem
  nothing. RC memory-safety (Phase 6) is a separate obligation this proof does
  not cover.
- **Immutability ⟹ no value restriction.** Core goat has no mutable reference,
  cell, or assignment, so `T-Let` generalizes **every** `e₁`, matching
  `infer.rs` (which has no syntactic-value check). This is the classical result
  that the value restriction is needed only in the presence of mutable
  references/effects. Modeling immutability *as the absence of mutable
  references* is precisely what licenses both the unrestricted generalization
  and the RC abstraction above.
- **`Bool`/`Number` have constructors but no eliminators.** The core omits `if`
  and arithmetic. Both base types are present (the §8 programs need `1` and
  `true`), but their elimination forms are trivial later deltas — `if` is a
  boolean eliminator with the obvious two reduction rules and a progress/
  preservation case each — that add nothing to the sharp-edge theorem. The real
  checker has `If` and `Bin`; the core deliberately does not.
- **`let` is non-recursive here; goat's is recursive for `program` values.**
  ADR 0003 makes a `program`-valued binding recursive (and all function
  bindings in a scope a mutually-recursive, order-free group), seeded
  monomorphically and generalized afterward (`seed_function_group`). The core
  models **non-recursive** `let`, which is faithful to goat's *value* bindings
  (sequential, shadowing) and sufficient for all of §8 — none of those programs
  uses a binding that refers to itself. Recursion is orthogonal to the
  monomorphic-parameter sharp edge; the faithful extension is a `letrec`/`fix`
  delta (monomorphic self-reference, generalize at the binding, an unfolding
  reduction), deferred like variants. **This is the clearest gap from the
  implementation; flagged.**
- **n-ary functions, not curried.** `program`/application are n-ary to match
  `Ty::Func(Vec<Ty>, Box<Ty>)` and the arity-checked calling convention (ADR
  0004); currying would misrepresent both and erase the arity-mismatch error.
  The cost is borne by the mechanization, not the model (§ below).
- **`Unit`, strings, variants/`match`, recursive (μ) types, numeric
  constraints, mono — all out.** Each is a later delta on the proven core (ADR
  0008). Variants reuse this very row machinery (plan.md Phase 7), so the row
  lemmas L1–L3 are the reusable part.
- **Declarative, not algorithmic.** `≺`/`gen` here are the declarative
  instance/generalization relations, not Algorithm W. The checker's
  `unify`/`rewrite_row` is a sound-and-complete algorithm for this relation
  (Leijen Thms 1–2), but its soundness, completeness, and **row-unification
  termination** (the `tail(r) ∉ dom(θ₁)` side condition, paper §7) are out of
  scope per ADR 0008.

**Where I was unsure the model matches `checker/src`.** Two places, both called
out above: (1) the recursion gap — the core's `let` is non-recursive while the
checker makes `program`-valued bindings recursive; I judged this orthogonal to
the theorem and deferred it, but a reviewer may want the `letrec` delta modeled
now rather than later. (2) The core omits `if`/arithmetic/`Unit` that the
checker implements; the §8 programs do not need them, but they are real surface
language and their deltas should be scheduled.

## 10. For the mechanization (#70 B2, #71 B3)

The hardest parts to anticipate, so B2/B3 can budget for them:

- **Row-equivalence completeness (L1/L2′).** Proving the swap-generated
  congruence `≅` complete with respect to the §3 "finite map to lists of types"
  characterization is the main row obligation and ADR 0008's named schedule
  risk. Everything downstream (canonical forms for records, L3, the §8.4
  non-derivation) rests on it.
- **n-ary term binders under locally-nameless.** metalib/LNgen is smoothest for
  **single** binders; `program(x₁,…,xₖ)` is a simultaneous multi-binder. The two
  realistic encodings are (a) an internal currying to single-binder λ
  (semantics-preserving, cheapest for LNgen, at the cost of a surface/core gap
  the arity lemmas must bridge) or (b) a telescope / simultaneous-substitution
  encoding (faithful, more infrastructure). Choosing between them is the biggest
  binder decision for B2. The type/row variables sidestep this entirely —
  they are a free-variable set with ordinary type substitution (L5), not
  LNgen binders.
- **The `T-Conv` induction tax.** A standalone conversion rule adds a case to
  every induction. If that proves heavy, fold `≅` into `T-App` (argument types)
  and `T-Proj` (the projected row) à la Leijen's `(app)` rule and drop `T-Conv`;
  L2 is what makes the two presentations interderivable. Decide this early, as
  it reshapes every inversion lemma.
- **Polymorphic substitution (L6b).** The one lemma where term substitution and
  type substitution (L5) interact; the standard HM proof carries, but it is the
  subtlest case and depends on `gen` quantifying exactly `ftv(τ₁) \ ftv(Γ)`.
