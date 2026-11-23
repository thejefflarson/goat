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
   comparison takes the `Eq` sort (phase 6, stage 1a); the `Ordered` sort comes later.
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
   declarative rule first allowed any `Tm`, so it derived types the checker
   does not give (`r = {a: 1}  {y: r.a, x: r.a + 1.5}.y` at `Int`); stage 7.1 of
   phase 7 narrowed it with the premise `lit_pinned`: unless the bound term is a
   function or a bare numeral, no quantified variable has the sort `Literal`.
   The recursive group left the unpinned set, because it unrolls to a record and
   preservation needs the stepped `let` to stay derivable. The same run found
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

## Follow-up: the `Eq` sort (phase 6, 2026-11-22)

`Eq` (ADR 0036) was added as the first such sort, with no change to the
decision above. `sort` gained `k_Eq` between `Any` and `Numeric` (`finer_numeric_eq`:
every `Numeric` type is `Eq`), and `sat` gained its cases: `String`, `Bool` and
`Unit` are `Eq`; a record is `Eq` when every field is; a `mu` is when its body
is, with a bound index counting as `Eq`; a tag group is when every parameter its
declaration uses is. A comparison unifies both operands at one fresh `Eq`
variable, which replaced the two-run `lenient`/`ora` workaround of #525. The
sort mechanism held up: the substitution lemma and `kres` needed no change.
`cmp_total` (two values of one `Eq` type compare) and `cmp_unerase` (the
elaboration converse for a comparison) are in the checked-closed list.

Two limits of the decision show here, both on the sound side. The unifier did
not push a sort onto a variable inside a compound it meets, so
`f = program(x) do same({p: x}, {p: x}) done` was accepted by the checker and
refused by W (#623); the amendment below closes it. And `sat_b`, the algorithm's
decision procedure, is conservative on `mu` and tag groups: it gives them `Any`
only, so W refuses a comparison of a recursive or tag type that `sat` accepts.

## Amendment: sort propagation and row kinds (phase 7, 2026-11-22)

**Sort propagation (#623).** The unifiers return the kinding environment. When a
variable of sort `k` binds to a type, each variable inside the type that is
coarser than `k` is renamed to a fresh variable of sort `k` (`push_sort`), then
the type must satisfy `k`. Renaming rather than mutating the environment keeps
the invariant `Good` relies on, that only a fresh atom ever gets a sort: the
renaming substitution respects the sorts (`k` is finer than the sort it
replaces) and the new environment refines the old one on a fresh atom alone.
The cost was one extra result in every unifier's signature (`unify_t`, `unify_r`,
`unify_k`, `unify_kr`, `unify_co`, `unify_mem`, `unify_grp`, `tie_obj`) and `infer`
passing the returned environment on; the soundness statements say `GoodU D n s D'
n'` (the supply grows, and a well-kept `D` gives a `Good` step), and `unify_sound`,
`unify_k_sound`, `unify_co_sound` and `infer_sound` keep their other conclusions.

**Row kinds.** The calculus gave a row variable a kind, a sort and a set of
labels it lacks (`RK`, `drk`; stage 7.2), so a spread onto an open row has a
derivation when the tail lacks the label (`T_SpreadL`) and an open record
satisfies `Eq` or `Numeric` when its fields and its tail do. A scheme records the
kind of each quantified row variable (`s_rk`) and `T_Let` types its body under
them. A substitution respects the kinds when `rkres D D' sr`. Algorithm W still
keeps every row variable at `rk_any` (`rtriv D`, part of `DOk`), so `rkres` holds
vacuously for it; the unifier's row side (a variable that binds to a row
passes the variable's lacks and sort on to the row's tail, a restricted row's
tail lacks the removed label, a spread checks the lacks) is the remaining part of
phase 7 stage 7.3 and is what removes the corpus reader's `LacksOnTail` skip.
