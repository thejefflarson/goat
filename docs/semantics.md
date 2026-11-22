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
*stateable and provable*. Rank-2 inference, which would repair it, is not part
of the language (no type-annotation syntax exists to express it, and ADR 0027
declines the annotation-free form), so the model states the edge as the
documented limit of the language. Everything that does not bear on that
theorem is left out, and §9 says exactly what and why.

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
- Hindley–Milner `let`-generalization: a binding `x = e₁  e₂` whose `e₁` is a
  syntactic value generalizes, so such `=`-bound names are polymorphic (ADR
  0027, the value restriction); **lambda-bound parameters stay monomorphic**
  (this asymmetry *is* the sharp edge);
- **recursion**: a group of functions that call themselves and each other,
  `letrec f₁ = e₁, …, fₙ = eₙ in e`, the order-free mutual group of ADR 0003;
- five base types: `Int`, `Float`, `Bool`, `String` and `Unit`. Their
  introduction forms are whole-number literals, decimal literals, `true` and
  `false`, string literals, and the unit value; their elimination forms are
  `if` on a `Bool`, the arithmetic operators `+ - * / // %`, and the
  comparisons `< <= > >= == !=` (ADR 0017, ADR 0036), each at concrete types
  (§4). An `Int` is a signed 64-bit integer; a `Float` is opaque: every
  `Float` operation is unspecified (§6);
- an explicit **Int-to-Float coercion** `float(e)`, which elaboration inserts
  wherever the checker accepts an `Int` for a `Float` (§4);
- a **trap**: integer `//` or `%` by zero (a `Float` one is not a trap), and an integer result outside the
  64-bit range, are defined runtime errors, one of the three outcomes of a
  closed well-typed term (§7);
- records as **scoped-label rows** (Leijen, *Extensible records with scoped
  labels*, `papers/scopedlabels.pdf`): construction `{l₁: e₁,…,lₖ: eₖ}` and
  field projection `e.l`, with Leijen's row-equivalence relation;
- **iso-recursive types** (ADR 0037, decision 3): the type `μ.τ` with explicit
  `fold(e)` and `unfold(e)` terms, restricted to **guarded** recursion (§4).
  The checker's equi-recursive types are related to these by an elaboration
  theorem that lands in phase 5 (§9).

Values are immutable: record values and closures (program literals) are values,
and there is no mutable reference, cell, or assignment in the language.

**Declarative, not algorithmic.** We model and (in #70–#71) prove soundness of
the **declarative** type system — well-typed closed terms do not get stuck. We
do *not* prove soundness or completeness of Algorithm W, unification, or
`rewrite_row`; those are a strictly larger, separate effort, out of scope per
ADR 0008. The checker's unification is a known sound-and-complete *algorithm*
for the declarative relation (Leijen, Thms 1–2); the declarative relation is
what the sharp-edge theorem is about.

**Out of the core (modeled by nothing — see §9 for the "why").** Reference
counting / heap / the Perceus model; variants and `match`; the `Eq` and `Ordered` constraints (a comparison is typed at concrete
types only, so a generic comparison waits for those sorts); the `trap()`
builtin; the 32-bit `Int` of
the embedded target; IEEE rounding, infinities and NaN (a `Float` is opaque);
comparison of `Unit`, records and tags (phase 6); rank-2
inference; `and`, `or`, `not`
and unary minus; monomorphization.

## 2. Syntax

Term variables `x, y, z, f, g, m, p`; labels `l`; string
literals `q` (a list of bytes, ADR 0009); whole-number literals `n` (integers)
and `Float` values `d` (opaque: no rule reads which one). Type
variables `α, β`; row variables `r, s`. Metavariables range over: `e` terms,
`v` values, `τ` monotypes, `ρ` rows, `σ` type schemes, `Γ` contexts.

```
e  ::=  x                              variable
     |  n  |  d  |  true  |  false     whole-number, Float and boolean constants
     |  q  |  unit                       string literal (its bytes), the unit value
     |  program(x₁,…,xₖ) do e done     abstraction        (k ≥ 0, the xᵢ distinct)
     |  e(e₁,…,eₖ)                     application        (k ≥ 0)
     |  x = e₁  e₂                     binding (let)      (x bound in e₂ only)
     |  letrec f₁ = e₁, …, fₙ = eₙ in e
                                       recursive group    (n ≥ 1, each eᵢ a function;
                                                           the fᵢ bound in every eⱼ and in e)
     |  {l₁: e₁, …, lₖ: eₖ}            record             (k ≥ 0)
     |  e.l                            field projection
     |  if e₁ then e₂ else e₃          conditional
     |  e₁ ⊙ e₂                        binary operation   (⊙ ∈ + - * / // %  < <= > >= == !=)
     |  float(e)                       Int-to-Float coercion (inserted by elaboration)
     |  fold(e)  |  unfold(e)           roll into, and unroll out of, a recursive type

v  ::=  n  |  d  |  true  |  false     constant value
     |  q  |  unit                      string and unit values
     |  program(x₁,…,xₖ) do e done     closure value
     |  {l₁: v₁, …, lₖ: vₖ}            record value
     |  fold(v)                        rolled value

τ  ::=  Int  |  Float  |  Bool  |  String  |  Unit   base types
     |  (τ₁,…,τₖ) → τ                  function type
     |  {ρ}                            record type
     |  α                              type variable
     |  μ.τ                            recursive type     (binds the index 0 of τ)
     |  #i                             index of an enclosing μ   (i ≥ 0)

ρ  ::=  ·                             empty row (closed tail)
     |  r                             row variable (open tail)
     |  l : τ ; ρ                     row extension

σ  ::=  τ  |  ∀ α₁…αₘ r₁…rₙ. τ        type scheme (monotype, or quantified)

Γ  ::=  ·  |  Γ, x : σ                typing context
```

The `letrec` is the elaboration of a scope's function bindings (ADR 0003):
every `name = program(…) do … done` in a chain of bindings is a member of one
group, and the chain's remaining bindings and result are its body `e`. A
`program` literal is a *syntactic value* — a term whose evaluation does no work
— as are the constants, a variable, `float(v)` of a value, a record of syntactic
values, and a `letrec` whose body is one (`gen_value(e)`, §4).

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

A recursive type `μ.τ` binds with a de Bruijn index: `#0` in `τ` is the
`μ` itself, `#1` the next `μ` out, and so on. Written with a name, `μ t. {moved: (t) → t; x: Int}`
is `μ.{moved: (#0) → #0; x: Int}`. The index is for the mechanization; the
surface language has no syntax for `μ`, `fold` or `unfold`, which belong to the
elaborated program (§9). `τ[μ.τ/#0]`, written `unroll(μ.τ)`, replaces the index
`#0` of `τ` by `μ.τ` and lowers the indices above it. A type is *closed*
(`lc`) when every index is bound by an enclosing `μ`.

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
——————————————— (≅-int)     ——————————————— (≅-float)     ——————————————— (≅-bool)
 Int ≅ Int                   Float ≅ Float                 Bool ≅ Bool

——————————————— (≅-unit)     ——————————————— (≅-string)    ——————— (≅-tvar)
 Unit ≅ Unit                 String ≅ String              α ≅ α

 τ₁ ≅ τ₁'  …  τₖ ≅ τₖ'   τ ≅ τ'
—————————————————————————————————— (≅-arrow)
 (τ₁,…,τₖ)→τ ≅ (τ₁',…,τₖ')→τ'

   ρ ≅ ρ'                  τ ≅ τ'     ρ ≅ ρ'
——————————— (≅-rec)      ——————————————————————— (≅-head)
  {ρ} ≅ {ρ'}               l:τ ; ρ  ≅  l:τ' ; ρ'

——————— (≅-index)         τ ≅ τ'
 #i ≅ #i                 ——————————— (≅-mu)
                           μ.τ ≅ μ.τ'

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

**No unrolling equation.** `(≅-mu)` compares the bodies of two recursive types
and nothing else: `μ.τ ≅ unroll(μ.τ)` is *not* a rule, so `≅` stays a
syntactic congruence and a type equal to a `μ` is a `μ` (L2). That is what makes
the recursion iso-recursive: a value of type `μ.τ` and a value of its unrolling
are different things, and `fold` and `unfold` are the explicit passages between
them (§4). The checker's types are equi-recursive (a type equals its unrolling,
ADR 0032); the elaboration theorem of phase 5 (§9) inserts the `fold`s and
`unfold`s that connect the two.

The checker realizes `≅` operationally through `rewrite_row`
([`infer.rs`](../checker/src/infer.rs)), which surfaces a label `l` by searching
past *differing* labels while keeping their position — Leijen's Figure 3 row
rewriting — and so surfaces the **first** `l`. The declarative counterpart is
`(≅-swap)` plus lemma L3 (§7); both agree that `.l` names the first `l`.

## 4. Typing

The judgment `Δ ; Γ ⊢ e : τ` assigns a **monotype** to a term. Schemes appear
only in the context and are introduced at a binding (`T-Let`) and eliminated at
a variable (`T-Var`). The instance relation `τ ≺_Δ σ` and the context's
generalization are defined in §5. `Δ` is a **kinding environment** (ADR 0037):
it gives each free type variable a *sort*, `Any`, `Numeric` or `Literal`, and
is `Any` outside a finite set of variables. `Δ ⊢ τ : κ` says `τ` may stand
where a variable of sort `κ` stands: `Int` and `Float` have every sort, a
variable `a` has the sorts at or above `Δ(a)` (a `Literal` variable is also
`Numeric`, and every variable is `Any`), and any other type has sort `Any`
only. A judgment that omits `Δ` is the one with `Δ` the all-`Any` environment,
which is the one a closed program is typed in.

```
 x : σ ∈ Γ      τ ≺_Δ σ
———————————————————————— (T-Var)      ———————————————————— (T-Num)
       Δ;Γ ⊢ x : τ                       Δ ⊢ τ : Literal
                                          ————————————————
                                           Δ;Γ ⊢ n : τ

———————————————— (T-Dec)
 Δ;Γ ⊢ d : Float

———————————————— (T-True)      ———————————————— (T-False)
 Γ ⊢ true : Bool                Γ ⊢ false : Bool

———————————————— (T-Unit)      ———————————————— (T-Str)
 Γ ⊢ unit : Unit                Γ ⊢ q : String

 Γ ⊢ e₁ : Bool      Γ ⊢ e₂ : τ      Γ ⊢ e₃ : τ
————————————————————————————————————————————————— (T-If)
        Γ ⊢ if e₁ then e₂ else e₃ : τ

 Δ;Γ ⊢ e : τ      Δ ⊢ τ : Numeric
———————————————————————————————————— (T-ToFloat)
 Δ;Γ ⊢ float(e) : Float

 Δ;Γ ⊢ e₁ : τ₁      Δ;Γ ⊢ e₂ : τ₂      ⊙ : τ₁, τ₂ ⇒_Δ τ
——————————————————————————————————————————————————————————— (T-Bin)
                 Δ;Γ ⊢ e₁ ⊙ e₂ : τ

```

The operator signature `⊙ : τ₁, τ₂ ⇒ τ` (ADR 0017, ADR 0036) says which operand
types an operator takes and what it gives. Both operands of an arithmetic or
comparison operator have one type. `+ - * // %` are generic: the one type may be any
`Numeric` type, `Int`, `Float` or a `Numeric` variable. A comparison stays at
the four concrete types.

```
 ⊙ ∈ {+, -, *}      Δ ⊢ τ : Numeric         ⊙ ∈ {//, %}      Δ ⊢ τ : Numeric
———————————————————————————————————— (S-Ring)   ———————————————————————————————————— (S-Whole)
        ⊙ : τ, τ ⇒_Δ τ                                 ⊙ : τ, τ ⇒_Δ τ

—————————————————————————— (S-Quot)
 / : Float, Float ⇒ Float

 ⊙ ∈ {<, <=, >, >=, ==, !=}      τ ∈ {Int, Float, String, Bool}
——————————————————————————————————————————————————————— (S-Cmp)
                     ⊙ : τ, τ ⇒ Bool

```

```
 Δ;Γ, x₁:τ₁, …, xₖ:τₖ ⊢ e : τ
————————————————————————————————————————————————— (T-Abs)
 Δ;Γ ⊢ program(x₁,…,xₖ) do e done : (τ₁,…,τₖ) → τ

 Δ;Γ ⊢ e : (τ₁,…,τₖ) → τ      Δ;Γ ⊢ eᵢ : τᵢ   (each i)
————————————————————————————————————————————————————— (T-App)
            Δ;Γ ⊢ e(e₁,…,eₖ) : τ

 gen_value(e₁)    V = ftv(τ₁) \ ftv(Γ)    Δ[V↦κ] ; Γ ⊢ e₁ : τ₁
 σ = gen(Γ, τ₁, κ)      Δ;Γ, x:σ ⊢ e₂ : τ₂
————————————————————————————————————————————————————————————————————— (T-Let)
                        Δ;Γ ⊢ (x = e₁  e₂) : τ₂

 Δ;Γ ⊢ e₁ : τ₁      Δ;Γ, x:τ₁ ⊢ e₂ : τ₂
——————————————————————————————————————————— (T-LetMono)
        Δ;Γ ⊢ (x = e₁  e₂) : τ₂

 eᵢ = program(…) do … done   (each i)      V = ftv(τ) \ ftv(Γ)   with τ = {f₁:τ₁ ; … ; fₙ:τₙ ; ·}
 Δ[V↦κ] ; Γ, f₁:τ₁, …, fₙ:τₙ ⊢ eᵢ : τᵢ   (each i)
 σᵢ = gen(Γ, τ, κ) with the body τᵢ        Δ;Γ, f₁:σ₁, …, fₙ:σₙ ⊢ e : τ'
————————————————————————————————————————————————————————————————————————————————————————— (T-Letrec)
                     Δ;Γ ⊢ letrec f₁ = e₁, …, fₙ = eₙ in e : τ'

 Δ;Γ ⊢ eᵢ : τᵢ   (each i)
——————————————————————————————————————————————————— (T-Record)
 Δ;Γ ⊢ {l₁: e₁, …, lₖ: eₖ} : {l₁:τ₁ ; … ; lₖ:τₖ ; ·}

 Δ;Γ ⊢ e : {l : τ ; ρ}             Δ;Γ ⊢ e : τ      τ ≅ τ'
——————————————————————— (T-Proj)    ———————————————————————————— (T-Conv)
   Δ;Γ ⊢ e.l : τ                        Δ;Γ ⊢ e : τ'

 μ.τ closed      guarded(τ)      Δ;Γ ⊢ e : unroll(μ.τ)
——————————————————————————————————————————————————————— (T-Fold)
                Δ;Γ ⊢ fold(e) : μ.τ

 μ.τ closed      guarded(τ)      Δ;Γ ⊢ e : μ.τ
——————————————————————————————————————————————————— (T-Unfold)
              Δ;Γ ⊢ unfold(e) : unroll(μ.τ)
```

`guarded(τ)` mirrors ADR 0032: every mention of the index `#0` in `τ` sits under
a record field **and** under a function type (a parameter or the result),
counting each `μ` between as transparent (under it the index is `#1`, and so
on). So `μ.{moved: (#0) → #0; x: Int}` is guarded; `μ.(#0) → #0` (the
self-application the checker rejects as `x(x)`), `μ.#0` (vacuous), and
`μ.{a: #0}` (no function) are not. A variant payload will guard on its own
once variants join the calculus (phase 3).

(`T-If`, `T-Unit`, `T-Str`, `T-True`, `T-False` and `T-Dec` carry `Δ` through
unchanged.)

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
- **`T-Let`** generalizes a syntactic value: `e₁` is typed, its type `τ₁` is
  generalized against the current context (§5), and the resulting scheme is what
  `x` is bound to in `e₂`. The variables it generalizes carry the sorts `κ`
  the scheme records, and `e₁` is typed in `Δ` extended with them, so that
  `let double = program(x) do x * 2 done` has the scheme
  `∀ a:Literal. a → a` and `double(1.5)` types at `Float`. Each use then
  instantiates `a` at a type of that sort (`Int`, `Float`, or a `Literal`
  variable), and `double("a")` has no derivation.
- **`T-LetMono`** is the value restriction's other half (ADR 0027): any binding
  may instead give `x` the monotype `τ₁`, and a computed `e₁` (a call, a
  projection, an operation, a `let`) has no other rule. A name bound to
  `id(program(x) do x done)` therefore has one type, and using it at two types
  has no derivation. The rule does not require `e₁` to be a computed term: a
  syntactic value may also be left monomorphic, which loses nothing, and keeps
  preservation simple because a step can turn a computed `e₁` into a value.
- **`T-Letrec`** types the members with the whole group in scope at one
  monotype each (a function can call itself and its neighbours, but only at the
  types it has inside the group, so recursion is monomorphic), then types the
  body with each member generalized against `Γ` alone. Every member's scheme
  quantifies the variables of the whole group's types that `Γ` does not fix, so
  each use of a member instantiates the group afresh. The members must be
  `program` literals: a `letrec` is a group of functions, as in the checker,
  where only a `program` value is recursive (ADR 0003). That is the whole of
  recursion: there is no recursive value (`ones = Link(1, ones)` is an unknown
  name).
- **`T-Record`** builds a **closed** row (tail `·`) in written order, so a
  literal's type records its labels and their order, duplicates included.
- **`T-Proj`** requires `e` to have a record type whose row presents `l` at the
  head, and gives `e.l` that field's type. Because `(≅-swap)` never moves one
  `l` past another `l`, `T-Conv` can bring only the **first** `l` to the head —
  so `T-Proj` types `e.l` at the type of the first `l`, exactly as the
  operational rule `ST-ProjRec` (§6) selects the first `l`.
- **`T-If`** types both branches at one type, so the whole `if` has that type
  whichever branch runs. The condition must be a `Bool`: `if 1 then …` has no
  derivation, and the checker reports `expected Bool, found Number`.
- **`T-Bin`** types an operation by the signature of its operator, at the
  types of its operands.
  - `+ - *` take two operands of one `Numeric` type and give that type
    (`S-Ring`), and so do `//` and `%` (`S-Whole`): two `Int`s, two `Float`s, or two operands of a `Numeric`
    variable, so `program(x) do x * x done` is generic.
  - `/` takes two `Float`s and gives a `Float` (`S-Quot`). The checker accepts
    `7 / 2` and types it `Float`; elaboration writes it `float(7) / float(2)`.
  - `//` and `%` are generic like `+ - *`: two `Int`s give an `Int`, two
    `Float`s a `Float`, so `7.5 // 2` is a `Float` and
    `program(x) do x // 2 done` is generic. The checker accepts `7 // 2.5` and
    types it `Float`; elaboration writes it `float(7) // 2.5`.
  - A comparison takes two `Int`s, two `Float`s, two strings or two booleans
    (`S-Cmp`); so `1 < "a"` has no derivation and `true + true` has none (the
    checker: `expected Number, found String`, `` `+` needs numbers… ``). The
    checker accepts `1 < 1.5`; elaboration writes it `float(1) < 1.5`.
- **`T-Num`.** A whole-number literal has any `Literal` type: `Int`, `Float`,
  or a `Literal` variable (ADR 0017's literal defaulting is a choice of type for
  that variable). So `1 + 1.5` has a derivation, with both operands at
  `Float`, and `if c then 1 else 2.5` types at `Float`. `1 < "a"` and `if 1 …`
  have none: `String` and `Bool` are not `Literal`.
- **`T-ToFloat`.** Wherever the checker accepts an `Int` where a `Float` is
  wanted (a call whose parameter is a `Float`, ADR 0017), elaboration inserts
  `float(e)`. That is every *scalar join site* (ADR 0040): an operand of an
  operator or a comparison, an argument whose parameter is a `Float` or a
  `Numeric` variable, a branch of an `if` or `match`, an item of a list
  literal. Never under a constructor: a record, a list or a function passed
  whole stays exact. `GoatPhase2.v` pins an elaborated widened branch and call
  (`widened_branch_types`, `widened_call_types`). It takes any `Numeric` operand and gives a `Float`; on a `Float`
  it is the identity (`ST-ToFloat`), so a generic function can coerce its
  argument. `float(true)` has no derivation. The calculus has no subtyping:
  `float(e)` is how an `Int` operand reaches a `Float` slot.
- **`T-Fold`** and **`T-Unfold`** are the two explicit passages between a
  recursive type and its unrolling. `fold(e)` is typed by the unrolling of the
  type it produces and is *unannotated*: it has every guarded `μ.τ` whose
  unrolling `e` has, as `float(e)` has several types today, so terms stay free
  of types. Both rules require the `μ` closed and guarded, so no term has the
  type `μ.(#0) → #0`: there is no `fold` at it, and no `unfold` of a value of it
  (`GoatRecTypes.v`, `no_fold_at_self_application`). A recursive type satisfies
  only the sort `Any`: a `μ` is never `Numeric` or `Literal`, and an index has
  no sort of its own, since it stands for a type that is substituted, never for
  a type variable that is quantified.

  A worked example in goat source, with the recursion through a record field
  and a function type, as ADR 0034's methods have it:

  ```
  P    = μ t. {moved: (t) → t; x: Int}
  ball = fold({moved: program(s) do s done, x: 1})        : P
  step = program(p) do (unfold(p).moved)(p) done          : (P) → P
  ```

  `step(ball)` runs: `ST-UnfoldFold` cancels the pair, `ST-ProjRec` reads the
  method off the record, and the receiver comes back (`GoatRecTypes.v`). The
  receiver is passed explicitly, as ADR 0031 has it.
- **`T-Conv`** closes typing under `≅`: anywhere a type is produced, an
  equivalent type may be used. This is where row reordering happens — e.g.
  passing a `{b:Bool ; a:Int ; ·}` value where `{a:Int ; b:Bool ; ·}` is
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
gen(Γ, τ, κ)  =  ∀ (ftv(τ) \ ftv(Γ)) with sorts κ. τ
```

This is `Inferer::generalize`: the difference of the type's free variables and
the environment's. Both type and row variables are quantified. A scheme records
the sort of each quantified type variable (`∀ a:κ`); a row variable has no sort.
The sorts `κ` are the ones the bound term was typed under (`T-Let`).

**Instantiation** `τ ≺_Δ σ`: for `σ = ∀ α₁:κ₁…αₘ:κₘ r₁…rₙ. τ₀`, we have
`τ ≺_Δ σ` when `τ = [α₁↦τ₁,…,αₘ↦τₘ, r₁↦ρ₁,…,rₙ↦ρₙ] τ₀` for some monotypes `τⱼ`
and rows `ρⱼ` with `Δ ⊢ τⱼ : κⱼ` (kind-respecting: type variables go to types of
their sort, row variables to rows). A monotype `σ = τ₀` has `τ₀` as its only
instance. This is `Inferer::instantiate` (fresh images per use site).

A substitution `θ` **respects** `Δ ⊢ Δ'` when `Δ' ⊢ θ(α) : Δ(α)` for every `α`.
Typing is preserved by such a substitution (L5).

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

 e' = e[f₁↦v₁, …, fₙ↦vₙ]      vᵢ = eᵢ[f₁↦(letrec …in f₁), …, fₙ↦(letrec … in fₙ)]
——————————————————————————————————————————————————————————————————————————————— (ST-Letrec)
 (letrec f₁ = e₁, …, fₙ = eₙ in e) ⟶ e'

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

—————————————————————————— (ST-IfTrue)     ———————————————————————————— (ST-IfFalse)
 if true then e₂ else e₃ ⟶ e₂              if false then e₂ else e₃ ⟶ e₃

      e₁ ⟶ e₁'                                   e₁ ⟶ e₁'
———————————————————————————————— (ST-If1)    ——————————————————— (ST-Op1)
 if e₁ then e₂ else e₃ ⟶ if e₁' …            e₁ ⊙ e₂ ⟶ e₁' ⊙ e₂

     e₂ ⟶ e₂'                                  v₁, v₂ values      ⊙(v₁, v₂) = v
——————————————————— (ST-Op2)           ————————————————————————————————————— (ST-Op)
 v ⊙ e₂ ⟶ v ⊙ e₂'                        v₁ ⊙ v₂ ⟶ v

      e ⟶ e'                                    d is any Float
——————————————————————— (ST-ToFloat1)    ————————————————————————— (ST-ToFloat)
 float(e) ⟶ float(e')                     float(n) ⟶ d

 ————————————————————————— (ST-ToFloat-Dec)
  float(d) ⟶ d

   v a value                      e ⟶ e'                    e ⟶ e'
———————————————————— (ST-UnfoldFold)  ——————————————————— (ST-Fold1)  ———————————————————————— (ST-Unfold1)
 unfold(fold(v)) ⟶ v              fold(e) ⟶ fold(e')          unfold(e) ⟶ unfold(e')
```

`⊙(v₁, v₂) = v` is the value an operator gives on two literals. It is a relation
because a `Float` operation has no single answer; every `Int` case has at most
one.

- **Integers.** An `Int` is a signed 64-bit integer, the range `[-2⁶³, 2⁶³ − 1]`.
  `+`, `-` and `*` on whole numbers `a` and `b` give `a + b`, `a − b` and
  `a · b` over ℤ, so `1 - 2 = -1`, when the result is in range. `a // b` is
  `⌊a / b⌋` (rounding toward negative infinity) and `a % b` has the sign of
  `b`, so `-7 // 2 = -4` and `-7 % 3 = 2`. A zero divisor does not step, and
  neither does a result outside the range: both trap (below). The one quotient
  that does not fit is `-2⁶³ // -1`; `-2⁶³ % -1` is `0`, which fits.
  The same operators on two `Float`s are Floats below.
- **Floats.** A `Float` value `d` is opaque. Any `+ - * /` on two `Float` values
  gives any `Float`, and so does `//` or `%` with a decimal operand, so `⊙(d₁, d₂) = d` holds for every `d`: the model is a
  relation, and a property of it holds for any function a compiler computes.
  A numeral beside a decimal is a `Float` operand (`1 + 1.5`), since a numeral
  may have type `Float`; two bare numerals step as `Int`s, whatever type they
  were typed at.
  This covers IEEE rounding, a quotient by zero, infinities and NaN, none of
  which the model separates out. A comparison of two `Float` values gives either
  boolean. `float(n)` gives any `Float` (`ST-ToFloat`).
- **Comparison.** Two `Int`s compare as integers. Two strings compare bytewise
  with a prefix first, and two booleans with `false` before `true` (ADR 0036).
  The result is `true` or `false` as the operator asks (`==` and `!=` ask for
  equal and unequal).

On any other pair of values `⊙` has no result; canonical forms (L7) show a
well-typed term never reaches that case. §9 lists where `⊙` departs from the
compiler.

**Traps.** A closed term *traps*, written `e ↯ k`, with `Div_by_zero` when
evaluation reaches `v₁ // 0` or `v₁ % 0`, and with `Overflow` when it reaches
an `Int` operation `v₁ ⊙ v₂` (`+ - * // %`) whose result is outside the 64-bit
range (the compiler's `this number got too big`, ADR 0017). The trap rises through the
enclosing context in the same left-to-right order as `⟶`: if `e₁ ↯ k` then
`e₁(…) ↯ k`, `e₁ ⊙ e₂ ↯ k`, `if e₁ … ↯ k`, and so on, and if `v` is a value and
`e₂ ↯ k` then `v ⊙ e₂ ↯ k`, and if `e ↯ k` then `float(e) ↯ k`, `fold(e) ↯ k` and `unfold(e) ↯ k`. A trapped term
has no `⟶` step. The `trap()` builtin is not in the core (§9).

Values do not step. A binding reduces by first evaluating `e₁` to a value
(`ST-Let1`) and then substituting (`ST-LetV`); because `e₁` is closed-up-to-`Γ`
and fully evaluated before substitution, the polymorphic substitution lemma (L6b,
§7) applies to a generalized binding. A recursive group unrolls when it is
reached (`ST-Letrec`): each member name becomes that member's function, whose
own references to the group are the group again, so the next use unrolls it
again; the members are closures, so the unrolling does no work and a group is
never stuck. `⟶*` is the reflexive-transitive closure of `⟶`.

In the mechanization the group has one bound name `p` for the record of its
functions, a member `fᵢ` is the projection `p.lᵢ`, and the unrolling replaces
`p` in the body by that record, in which each `p` is the group again
(`proofs/GoatDefs.v`, `st_letrec`). The two presentations are the same
reduction; the single binder is what the locally-nameless infrastructure
handles (§10).

## 7. Metatheory

**Definitions.** A term is a *value* if it is in the `v` grammar. A term `e` is
*stuck* if it is not a value, no `e'` has `e ⟶ e'`, and it does not trap. Stuck
terms are exactly the errors a type system must rule out: projecting an absent label, calling a
non-function, calling at the wrong arity, applying `.l` to a non-record.

The proofs (#71) rest on these lemmas; they are stated here so #70 knows the
obligations it must generate.

- **L1 — `≅` is a congruence equivalence.** `≅` (on types and rows, mutually) is
  reflexive, symmetric, transitive, and a congruence for every type and row
  constructor; it is the least such relation containing `(≅-swap)`. *(= Leijen
  Fig. 1.)*
- **L2 — `≅` preserves head shape ("no confusion").** If `τ ≅ τ'` then `τ` and
  `τ'` have the same outermost constructor: `Int ≅ τ'` ⟹ `τ' = Int`;
  likewise `Float`, `Bool`, `String` and `Unit`; `(τ₁,…,τₖ)→τ ≅ τ'` ⟹ `τ' = (τ₁',…,τₖ')→τ'₀` with the **same
  arity `k`** and componentwise `≅`; `{ρ} ≅ τ'` ⟹ `τ' = {ρ'}` with `ρ ≅ ρ'`. In
  particular `Int ≅ Bool` is *not* derivable, and arities never change. This
  is what lets canonical forms survive `T-Conv`.
- **L2′ — `≅` preserves labels.** If `ρ ≅ ρ'` then they have the same tail and,
  for each label `l`, the same-length, componentwise-`≅` list `π_l` (the
  characterization in §3). Hence rows with different label sets (e.g.
  `{x:Int;·}` vs `{x:Int;y:Int;·}`) are never `≅`.
- **L3 — row surfacing (scoped-label core).** If `ρ ≅ (l:τ ; ρ')`, then `ρ`
  contains a field labeled `l`; letting `(l:τⱼ)` be the **first** `l`-field of
  `ρ`, we have `τⱼ ≅ τ` and `ρ' ≅ (ρ minus its first l-field)`. So the type `τ`
  that `T-Proj` reads off is determined up to `≅` by the first `l`. This is the
  declarative analogue of `rewrite_row` and the bridge between `T-Proj` and
  `ST-ProjRec`.
- **L4 — structural lemmas.** Weakening, permutation, and `≅`-respecting
  variants, for `Γ`.
- **L5 — type/row substitution preserves typing.** If `Δ;Γ ⊢ e : τ` and `θ`
  is a type/row substitution that respects `Δ ⊢ Δ'`, then `Δ';θΓ ⊢ e : θτ`.
  (Drives instantiation, and the `let` case below, where the generalized
  variables are renamed to fresh ones that are `Any` in `Δ'`, so renaming never
  loses a sort.)
- **L6 — term substitution.** The substituted `v` is a syntactic value
  (`gen_value(v)`), so a `let` inside `e` keeps the premise of `T-Let`: a
  syntactic value stays one under substituting a syntactic value for a name.
  - **(a) monomorphic:** if `Γ, x:τ' ⊢ e : τ` and `Γ ⊢ v : τ'`, then
    `Γ ⊢ e[x↦v] : τ`. (For `ST-Beta`, and for the group's members in
    `ST-Letrec`.)
  - **(b) polymorphic:** if `Δ;Γ, x:σ ⊢ e : τ` and `Δ[V↦κ];Γ ⊢ v : τ₀` where
    `σ = ∀ V:κ. τ₀` and `V ∩ ftv(Γ) = ∅`, then `Δ;Γ ⊢ e[x↦v] : τ`. (For
    `ST-LetV`.) Each occurrence of `x` used `v` at some instance `θτ₀` of `σ`;
    by L5, `v` has that instance because the quantified `V` are not free in `Γ`
    and `θ` respects the sorts `κ`. Inside `e` the environment grows at each
    `let`; a derivation of `v` moves between two environments that agree on the
    free variables of `Γ` and `τ₀` by sending the other variables `v` uses to
    `Int`, which has every sort.
- **L7 — canonical forms.** If `· ⊢ v : τ` for a value `v`:
  - `τ ≅ Int` ⟹ `v` is a whole-number literal `n`;
  - `τ ≅ Float` ⟹ `v` is a `Float` value `d`, or a whole-number literal `n`
    (a numeral has any `Literal` type);
  - `τ ≅ α` for a type variable `α` ⟹ `v` is a whole-number literal `n`;
  - `τ ≅ Bool` ⟹ `v ∈ {true, false}`;
  - `τ ≅ String` ⟹ `v` is a string literal `q`;
  - `τ ≅ Unit` ⟹ `v = unit`;
  - `τ ≅ (τ₁,…,τₖ)→τ₀` ⟹ `v = program(x₁,…,xₖ) do e done` with **exactly `k`**
    parameters;
  - `τ ≅ {ρ}` ⟹ `v = {l₁:v₁,…,lₘ:vₘ}` whose natural row
    `ρ_v = (l₁:τ₁;…;lₘ:τₘ;·) ≅ ρ`; and for any `(l:τ'';ρ'') ≅ ρ`, `v` has a
    first-`l` field whose value has a type `≅ τ''`.

  - `τ ≅ μ.τ₀` ⟹ `v = fold(v')` for a value `v'` with `· ⊢ v' : unroll(μ.τ₀)`.

  (Each case: induction on the value's typing, using L2/L2′ to push `T-Conv`
  through and L3 for the record case.)
- **L8 — recursive types.** Three facts carry `fold` and `unfold` through the
  rest. *Substitution commutes with unrolling:* `θ(unroll(μ.τ)) =
  unroll(θ(μ.τ))` when every type `θ` substitutes in is closed. That premise is
  why a generic instance (`τ ≺_Δ σ`), a renaming and an algorithm substitution
  each carry "closed images", and why L5 does: a type with a free index put
  under a `μ` would be captured. *Equality respects unrolling:* if `τ ≅ τ'` and
  `υ ≅ υ'` then `τ[υ/#k] ≅ τ'[υ'/#k]`, so folding at an equal type unrolls to an
  equal type (this is what `ST-UnfoldFold` and L7 use). *The guard is invariant:*
  `guarded` is preserved by `θ` and by `≅`, so a conversion cannot dodge it.
  Neither a `μ` nor an index adds a free type or row variable of its own, so
  `ftv`, `frv`, generalization and the sorts of §5 are untouched.

### Progress

> **Theorem (Progress).** If `· ⊢ e : τ`, then `e` is a value, or there exists
> `e'` with `e ⟶ e'`, or `e` traps (`e ↯ k` for some `k`).

Proof by induction on `· ⊢ e : τ`. `T-Conv` uses the IH directly (being a value,
stepping or trapping does not depend on the type). `T-If`: by L7 an evaluated
condition is `true` or `false`, so `ST-IfTrue` or `ST-IfFalse` fires (or the
condition steps by `ST-If1`, or traps). `T-Bin`: either an operand steps
(`ST-Op1`, `ST-Op2`) or traps, or both are values, and the operator's signature
and L7 give the operands' forms. Then `ST-Op` fires, except for an `Int`
operation that divides by zero or leaves the 64-bit range, which traps. `T-ToFloat`:
by L7 an evaluated operand is a whole number or a `Float` value, so `ST-ToFloat`
or `ST-ToFloat-Dec` fires (or the operand steps by `ST-ToFloat1`, or traps). `T-App`: by L7 the evaluated
callee is a `k`-ary `program` and the arguments are `k` values, so `ST-Beta`
fires (or a subterm steps by `ST-App1/2`, or traps). `T-Proj`: by L7 and L3 the
evaluated record has a first-`l` field, so `ST-ProjRec` fires (or `ST-Proj1`).
`T-Let` and `T-LetMono`: either `e₁` steps (`ST-Let1`), or traps, or it is a
value and `ST-LetV` fires. `T-Letrec`: the members are `program` literals, so
`ST-Letrec` fires. Constants, abstractions, and record values are values. **No well-typed
closed term is stuck.**

### Preservation

> **Theorem (Preservation / subject reduction).** If `Γ ⊢ e : τ` and `e ⟶ e'`,
> then `Γ ⊢ e' : τ`.

Proof by induction on the derivation of `e ⟶ e'` (equivalently on `Γ ⊢ e : τ`),
inverting typing through `T-Conv` with L2/L2′. `ST-Beta` uses L6a; `ST-LetV`
uses L6b for a generalized binding (its side condition `V ∩ ftv(Γ) = ∅` holds
because `gen` quantifies exactly `ftv(τ₁) \ ftv(Γ)`) and L6a for a monomorphic
one; `ST-Let1` keeps `gen_value(e₁)` because a syntactic value that steps is
still one; `ST-Letrec` types the unrolled group at the record type of its
members by L6a (the group, whose body is its own name, has that type, and
substituting it for the name in the members, typed with the name at that type,
types the unrolled members) and then substitutes the record of unrolled members
into the body by L6b; `ST-ProjRec` uses L7/L3 to show the first-`l`
value has the projected type `τ`; `ST-IfTrue` and `ST-IfFalse` return the branch,
which has the type of the whole `if`; `ST-Op` uses L7 to read both operands as
literals of the operator's types, so the result is a whole number or `Float`
value (arithmetic) or a boolean (comparison), the type its signature assigns;
`ST-ToFloat` and `ST-ToFloat-Dec` give a `Float` value, which has type `Float`
by `T-Dec`; an `ST-Op` on numerals at a `Literal` variable gives a numeral at
that variable, by the numerals' own typing (L7); the
congruence rules use the IH. The theorem
is stated for arbitrary `Γ` because the induction needs it; soundness uses the
closed case `Γ = ·`.

### Soundness

> **Corollary (Type soundness).** If `· ⊢ e : τ` and `e ⟶* e'`, then `e'` is not
> stuck: `e'` is a value, steps further, or traps.

Immediate from Progress and Preservation. This is the theorem the whole
development exists to establish.

## 8. The sharp edge, worked

These are the four "Known limitation" programs from docs/plan.md as derivations
and non-derivations. Throughout, `I ≡ program(x) do x done`; by `T-Abs`/`T-Var`,
`· ⊢ I : (α)→α` for any `α`. We write `a = e₁  e₂` for the inner binding whose
body `e₂` ignores `a` — it forces `e₁` to be typed, then types `e₂`.

### 8.1 `m = {id: program(x) do x done}  (a = (m.id)(1)  (m.id)(true))` — **accepts**

- `T-Record` on `{id: I}` with `· ⊢ I : (α)→α` gives `{id: I} : {id:(α)→α ; ·}`.
- `gen(·, {id:(α)→α ; ·}) = ∀α. {id:(α)→α ; ·}`, since `α ∉ ftv(·)`. Call it
  `σ_m`; bind `m : σ_m`.
- First use: `T-Var` instantiates `σ_m` at `α := Int`, so
  `m : {id:(Int)→Int ; ·}`, `T-Proj` gives `m.id : (Int)→Int`, and
  `T-App` with `1 : Int` gives `(m.id)(1) : Int`. Bind `a : Int`.
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

- `(m.id)(1)` forces, by `T-App`, `τ_id ≅ (Int)→τ`.
- `(m.id)(true)` reuses the **same** `τ_id` (a monotype has only itself as
  instance) and forces `τ_id ≅ (Bool)→τ'`.

So `(Int)→τ ≅ (Bool)→τ'`, which by L2 forces `Int ≅ Bool` — not derivable.
No `τ_id` exists, so there is no derivation of the body, and `use` is
untypeable; the program is rejected. The checker reports this as the targeted
"`m.id` gets a Number here and a Bool there, but a function you pass in can only take one kind of thing" error
([`unify_use`](../checker/src/infer.rs)). ✗

### 8.3 `both = program(f) do a = f(1)  f(true) done` — **rejects** (no record needed)

`T-Abs` binds `f : τ_f` at a monotype. `f(1)` forces `τ_f ≅ (Int)→τ`;
`f(true)` forces the same `τ_f ≅ (Bool)→τ'`. By L2, `Int ≅ Bool` — impossible.
No derivation; rejected. This is the sharp edge with no record in sight. The
language has no rank-2 inference and no annotation syntax to ask for it, so this
is the intended limit. ✗

### 8.4 `getx = program(p) do p.x done` with `use2 = program(g) do a = g({x:1})  g({x:2,y:3}) done` — **rejects** (row mismatch)

`getx` types fine and polymorphically: `T-Abs` binds `p : {x:α ; r}` (a monotype
that happens to be an open record), `T-Proj` gives `p.x : α`, so
`getx : ({x:α ; r})→α`, and `gen` yields `σ_getx = ∀α r. ({x:α ; r})→α`.

`use2` does not. `T-Abs` binds `g : τ_g` at a monotype.

- `g({x:1})`: `T-Record` gives `{x:1} : {x:Int ; ·}`, so `T-App` forces
  `τ_g ≅ ({x:Int ; ·})→τ`.
- `g({x:2,y:3})`: `{x:2,y:3} : {x:Int ; y:Int ; ·}`, so
  `τ_g ≅ ({x:Int ; y:Int ; ·})→τ'`.

By L2 these force `{x:Int ; ·} ≅ {x:Int ; y:Int ; ·}`, i.e. two rows
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
- **The value restriction is modeled (phase 2, ADR 0037).** Core goat has no
  mutable reference, so unrestricted generalization would be sound, but the
  checker restricts it (ADR 0027: a computed binding keeps one type, because mono
  specializes a generalized binding per use and so would repeat the computation),
  and the rules say what the checker does. `gen_value` is the checker's
  `is_syntactic_value` on the constructs the core has: unit, constants, names,
  functions and records of those. Variants and spreads join with phases 3 and 4.
  Two additions a proof needs, both agreeing with the checker: `float(v)` of a
  value is a value (a literal the context settles as a `Float` is elaborated to
  `float(n)` and stays generalizable), and a `letrec` whose body is a value is a
  value (ML's nonexpansive terms: the unrolled group is substituted for a name,
  and the name must stay generalizable afterwards). `proofs/GoatPhase2.v` holds
  the classification as checked examples.
- **Recursive types are iso-recursive in the calculus (phase 5a, ADR 0037
  decision 3).** The calculus has `μ.τ` with explicit `fold` and `unfold`, a
  congruence-only `≅` on it, and the `guarded` restriction of §4. Decided with
  the owner (ADR 0037 amendment): `fold` is unannotated; the binder is a de
  Bruijn index in the grammar, with unrolling and closure written by hand in
  `proofs/GoatDefs.v` and `proofs/GoatMu.v` (a cofinite `μ` rule would make the
  substitution lemma need finite-support hypotheses on every substitution, and
  Ott's generated open and closure for types would go unused); the bound index
  has no sort, and a `μ` satisfies only `Any`; the parser fragment is unchanged,
  since `μ`, `fold` and `unfold` have no surface syntax. **Left to phase 5
  proper:** the elaboration theorem (every program the checker's algorithm
  accepts elaborates, by inserting `fold`s and `unfold`s, into one the
  iso-recursive rules accept), extending algorithm W to produce a `μ` (it
  rejects `fold` and `unfold` today, and its occurs check refuses to bind a
  variable to a type with a free index, so it stays sound), and the type of an
  open-extensible recursive receiver (ADR 0034 decision 3: intended reading is
  `∀ r. μ t. {moved: (t) → t; x: Int ; r}`, instantiated at the extension and
  refolded by the elaborator; it needs methods and `self`). Phase 3's tag
  signature `Δ` must keep closed payload types in the sense of `lc` (a payload
  under a `μ` mentions an index), not "no free variables".
- **Spread and restrict (phase 4, ADR 0033, ADR 0037).** A row entry
  `l ^ P : T ; R` holds the field `l` at `T` when its presence `P` is `Unit`,
  holds none when `P` is `Bool` and `R` has no `l`, and is stuck when `P` is a
  variable (the checker's `PRESENT` and `ABSENT`, `ty.rs`). Row equivalence
  gains `l ^ Unit : T ; R ≅ l : T ; R`, `l ^ Bool : T ; R ≅ R` (when `R`'s
  spine, to its `nil`, names no `l`) and the swaps of an entry past another.
  `{...e1, l: e2}` has type `{l : T ; R}` when `e1 : {l ^ P : T ; R}` and
  `e2 : T`, so one rule covers an update (`P = Unit`), an extension
  (`P = Bool`) and a parameter of unknown shape (`P` a variable). It steps, once
  both are values, to the record with its first `l` set to the value, or with
  `l` added in front when there is none. `restrict(e, l)` takes the first `l`
  out of a record whose type has one. Scoped labels stay, so a row may hold a
  label twice and the checker's rule that it never does (ADR 0033 decision 5)
  is stricter than the model. Row variables carry no `lacks` constraint: a
  spread of a row that ends in a row variable the checker knows lacks the label
  has no derivation, and the checker accepts it. `proofs/GoatPhase4.v` holds
  the cases as checked examples; `docs/design/phase4-proof-plan.md` has the
  decisions and what waits (algorithm W, the parser fragment, `lacks`).
- **Base types and their operators (phase 1, ADR 0037).** The core has
  `Int`, `Float`, `Bool`, `String` and `Unit`, with `if`, the operators and the
  comparisons of §4. `proofs/GoatPhase1.v` holds each of the cases below as a
  checked example, and the examples were compared with `goat check` and
  `goat run` from a release build. What the model abstracts:
  - *`Int` is 64 bits.* The compiler's `Int` is an `i64` on desktop and an
    `i32` on embedded, and an operation that does not fit traps
    (`this number got too big`, ADR 0017). The model takes the desktop width, so
    `Int` is the range `[-2⁶³, 2⁶³ − 1]` and a result outside it traps with
    `Overflow`; the 32-bit target is not separately modeled.
  - *A `Float` is opaque.* The compiler's `Float` is an `f64` (`f32` on
    embedded) with IEEE rounding, infinities and NaN. The model keeps none of
    that: a `Float` value carries nothing a rule reads, and every `Float`
    operation, comparison included, is an unspecified function, modeled as a
    relation that allows every result. `0.1 + 0.2 == 0.3` and `x == x` can step
    either way. Soundness holds for every choice, so it holds for the compiler's.
  - *Float `//` and `%`.* The compiler computes them as Python does (CPython's
    `float_divmod`): `//` is the floor of the quotient of the two doubles and `%`
    takes the divisor's sign, so `7.5 // 2 = 3`, `-7.5 % 2 = 0.5` and
    `1 // 0.1 = 9` (not the `10` that `floor(1 / 0.1)` gives). A zero divisor
    follows IEEE rather than trapping: `x // 0.0` is `x / 0.0` (`inf`, `-inf` or
    `nan`) and `x % 0.0` is `nan`. The model relates every `Float` pair to every
    `Float`, so none of this is modeled. On the embedded profile the operands
    are `f32`s, computed in `f64` and rounded back to `f32` (ADR 0017).
  - *Traps.* A zero divisor in an `Int` `//` or `%` traps in the compiler (ADR 0023:
    `5 // 0` prints `trap: division by zero`) and traps here: it has no `⟶` step
    and is a third outcome of Progress and Soundness. So does an `Int` result
    outside the range. The `trap()` builtin raises no trap here, because the
    model has no such term.
  - *A call coerces.* The compiler accepts an `Int` argument where the
    parameter is a `Float` (`f(7 // 2)` with `f` forced to take a `Float`), and
    an `Int` beside a `Float` at an operator. The calculus has no subtyping:
    elaboration writes `float(e)` at each such place (`T-ToFloat`), including
    the branches of an `if` and the arguments of a generic call (ADR 0040), so the
    soundness theorems apply to the elaborated term. Whether the checker inserts
    it exactly where the compiler accepts an `Int` is the elaborator's
    obligation, not a theorem here.
  - *Generic operators.* The checker types `a < b` with an `Eq` constraint
    and `a + b` with `Numeric`, so a generic function stays polymorphic over
    them. The calculus models `Numeric` and `Literal` as sorts of type variables
    (§4, §5), so `+ - *` and a numeral apply at any `Numeric` or `Literal`
    type, a variable included. A comparison applies at `Int`, `Float`, `String`
    or `Bool` only; a function that uses `<` at a type variable has no
    derivation here, and generic comparisons wait for the `Eq` and `Ordered`
    sorts.
  - *Defaulting.* ADR 0017 settles a `Literal` variable left unconstrained at
    `Int`; `Numeric` has no default. The calculus has no defaulting rule: a
    closed program is typed in the all-`Any` environment, where each use of a
    generalized `Literal` variable is at a concrete `Int` or `Float`, so the
    default is a choice of instance, made by the elaborator at the top-level
    program judgment, and a theorem here holds for every choice.
  - *Algorithm W.* The proofs' inference algorithm threads a kinding environment
    (`proofs/GoatInfer.v`): a numeral is a fresh `Literal` variable, `float(e)`
    and `+ - *` unify their operands with a fresh `Numeric` variable,
    unification checks a sorted variable against a type and binds the coarser of
    two variables to the finer, `generalize` records the sorts of the variables
    it quantifies and `instantiate` gives each fresh variable its scheme's sort.
    So it infers `1 + 1.5 : Float` and `program(x) do x * 2 done : a -> a` with
    `a` `Literal`. Every type it infers is derivable (`infer_closed_sound`, in the
    environment it returns). It is not complete: a comparison has no signature at
    a variable, so one on a numeral's variable settles at `Int`, and a comparison
    of two other variables is rejected.
  - *A string token has no payload.* The lexer is trusted, so the parse tree
    carries no bytes, and a string denotes `q` for every `q`.
  - *`if` has an `else`.* `if c then a done` lowers to `if c then a else ()`;
    the core has the three-armed form only, and the unit value has no literal.
  - *Not here:* comparison of `Unit` (phase 6, structural ordering), records and
    tags (ADR 0036), `and`, `or`,
    `not`, unary minus, and the precedence of a run of operators (the parser
    fragment has at most one operator in an expression).
- **Recursion is a group of functions (phase 2, ADR 0037).** ADR 0003 makes
  every `program`-valued binding in a scope part of one mutually recursive,
  order-free group, seeded monomorphically (`seed_function_group`); a *value*
  binding is non-recursive, sequential and shadowing, which is the plain `let`.
  The core's `letrec` is that group (`T-Letrec`, `ST-Letrec`). What it abstracts
  or differs on:
  - *Elaboration hoists the group.* A function may see the value bindings above
    it but not those below; the `letrec` is placed after the value bindings its
    members use, so a member also sees value bindings between them and the group.
    Name resolution, not the type system, keeps those out of reach (ADR 0003).
  - *The group is generalized as a whole.* Each member is generalized against
    the context outside the group, so a member whose type shares a variable with
    another member is still polymorphic in it. The checker does the same: it
    infers the members in order and generalizes one once every member it is
    connected to (through what either mentions, among the members not yet
    generalized) has been inferred, so
    `f = program(x) do g(x) done  g = program(y) do y done` types `f` at
    `forall a. (a) -> a` and `f(1)` followed by `f(true)` checks (`Infer::settle`).
    A member that mentions no pending member, and that none mentions, is
    generalized when its own binding is reached, as before.
  - *No recursive values.* Only a function may name itself.
- **n-ary functions, not curried.** `program`/application are n-ary to match
  `Ty::Func(Vec<Ty>, Box<Ty>)` and the arity-checked calling convention (ADR
  0004); currying would misrepresent both and erase the arity-mismatch error.
  The cost is borne by the mechanization, not the model (§ below).
- **Variants/`match`, recursive (μ) types, constraints, mono — all out.** Each is a later delta on the proven core (ADR
  0008). Variants reuse this very row machinery (plan.md Phase 7), so the row
  lemmas L1–L3 are the reusable part.
- **Declarative, not algorithmic.** `≺`/`gen` here are the declarative
  instance/generalization relations, not Algorithm W. The checker's
  `unify`/`rewrite_row` is a sound-and-complete algorithm for this relation
  (Leijen Thms 1–2), but its soundness, completeness, and **row-unification
  termination** (the `tail(r) ∉ dom(θ₁)` side condition, paper §7) are out of
  scope per ADR 0008.

**Where the model differs from `checker/src`.** The constructs still to come in
ADR 0037's phase order. A value binding between two members of a group is
visible to the checker (it sees the group's monotypes), which the elaboration
into one `letrec` does not model; the differential test skips such programs.

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
