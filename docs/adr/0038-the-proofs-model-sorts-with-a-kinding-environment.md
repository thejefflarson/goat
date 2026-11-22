# ADR 0038 — The proofs model a type variable's sort with a kinding environment

- Status: accepted (2026-11-15)
- Refines: ADR 0037 (phase 2: generic operators).
- Context: the generic-operator work of ADR 0037's phase 2, issue #451.

## Context

The checker types `a + b` with a `Numeric` constraint and a numeral with a
`Literal` one (ADR 0017), so `program(x) do x * 2 done` is generic. The calculus
must say what a constrained type variable is, and the substitution lemma behind
preservation must survive it. Three representations were weighed:

- **P: the sort lives in the variable** (`typ_Var k a`). The generated syntax
  changes, and a set of atoms disagrees with sort-keyed substitutions: two
  variables with one name and different sorts are different variables, and the
  free-variable sets no longer say which.
- **The atom determines its sort.** Metalib's atoms are sealed, so a sort cannot
  be read off one.
- **Q: a kinding environment** `D`, a total map from atoms to sorts that is
  `Any` outside a finite set, indexes the typing judgment, and each scheme
  records the sorts of its quantified atoms. Each atom has one sort at a time,
  type variables stay a plain `typ_Var a`, and `goat_ln.ott` is untouched.

## Decision

1. **Q.** `typing D G e T`. A scheme is `Sch tq rq body sk`, matching
   `forall a:K`. `T_Let` and `T_Letrec` type the bound term under `ext D V k`,
   `D` extended by the sorts `k` on the variables `V` the binding generalizes.
   A substitution respects the sorts when `kres D D' st`: every atom goes to a
   type that satisfies its sort in `D'`. The program judgment is
   `typing d_any nil e T`, `d_any` being `Any` everywhere.
2. **The first cut is `+ - *`, numerals and `float(e)`.** A numeral has any
   `Literal` type, `Float` included, and two bare numerals step as `Int`s.
   `float(e)` takes any `Numeric` operand and is the identity on a `Float`. A
   comparison stays at concrete types until the `Eq` and `Ordered` sorts exist.
3. **Defaulting is not a rule.** ADR 0017 settles a `Literal` variable left
   unconstrained at `Int`, and `Numeric` has no default. A closed derivation in
   `d_any` instantiates each generalized variable at a concrete type, so the
   default is a choice among derivations made by the elaborator, and the theorems
   hold for every choice.
4. **Algorithm W is not extended here.** The algorithm stays sound (every type
   it infers is derivable in `d_any`) and is incomplete for the generic
   operators. (Extended afterwards: the algorithm threads the kinding
   environment, `proofs/README.md`, "Algorithm W with sorted variables".)
   (Closed afterwards, 2026-11-22: a closed record whose fields all satisfy
   `Numeric` satisfies it, and `+ - * // %` step on two records field by field,
   pairing fields by label (`rec_zip`, `proofs/GoatRecArith.v`). A record is
   never `Literal`, so `float(e)` takes a `Literal` operand, where decision 2
   wrote `Numeric`: `float` of a record has no step. The algorithm binds a
   `Numeric` variable to a record whose fields satisfy `Numeric`, and does not
   push the sort onto a variable inside the record, because a substitution
   keeps the kinding environment. The differential corpus no longer skips the
   calls that pass a record to a generic operator.)

5. **A `let` may keep variables monomorphic (addendum, 2026-11-22).** The
   checker generalizes a numeral's `Literal` variable at a function and at a bare
   numeral (`n = 3`, ADR 0039) and nowhere else: `r = {a: 1}` is one record, so
   `r = {a: 1}  {x: r.a + 1.5, y: r.a // 2}` is an error, while a name, a
   `float(...)` or a record of numerals bound by `let` kept the numeral's
   variable shared. The calculus generalized every variable at every syntactic
   value, which made about 3,100 corpus programs (2,743 distinct) skip as
   `NumeralLet`. Measured with the skip off, 2 of them disagreed, both a record
   holding a numeral used at two types; the 2,519 that bind a name (`m = n`) did
   not (a name's variable is shared too, and no program used it at two types).
   Two options were weighed: restrict `T_Let` so it never quantifies a `Literal`
   variable except at a function or a bare numeral, or give `T_Let` a type `Tm`
   whose free variables stay monomorphic. The restriction cannot state the
   algorithm's invariant, because the algorithm leaves a shared `Literal`
   variable free in the context of the `let` body, in an environment where it
   still has its sort, and the restricted rule has no scheme with a free sorted
   variable to give it. So `T_Let` takes `Tm` and generalizes over the context
   extended with a binding of `Tm` (`pin_ctx`, `gen (pin_ctx Tm G)`); the bound
   term and the body are still typed over `G` alone. The rule allows any `Tm`
   (generalizing less is always sound), and the algorithm picks
   `let_pin D e T`: nothing for a function, a bare numeral or a recursive group,
   and the `Literal` variables of `T` for any other value. Progress,
   preservation and the substitution lemma are re-proved for the rule
   (`tsubst_gen_pin`, `typing_inst_gen` over a pinned context), as is the
   algorithm's soundness (`typing_gen_ren_on`); no admits, no new axioms. The
   declarative rule still derives programs the checker rejects, as it did
   before; only the algorithm has to agree with the checker. The same run found
   that the calculus did not generalize a spread of syntactic values, which the
   checker does (`is_syntactic_value`), so `{...b, k: 5}` over a record of a
   generic function typed its function monomorphically; `is_gen_value` now
   includes `e_spread`, and a rest pattern with no fields is outside the
   fragment, because it only says its source is a record.

## Consequences

- The substitution lemma quantifies over the environments a substitution
  respects, needs both environments to be `Any` outside a finite set (so a name
  a `let` is renamed onto carries any sort), and a derivation moves between two
  environments that agree on its context and type (`typing_denv_agree`).
  `proofs/README.md` explains where each is used.
- A later sort (`Eq`, `Ordered`) is a new case of `sort`, `finer` and `sat`.
