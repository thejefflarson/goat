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
   One incompleteness remains: the checker applies `+ - *` to two records field
   by field, so `add({x: 1}, {x: 2})` types in the checker and has no derivation
   here. A record would have to satisfy `Numeric` (`sat`), and the operators
   would need a step rule on records, so progress, preservation and the
   substitution lemma change; it waits for a ticket that carries that change.
   The differential corpus skips exactly the calls that pass a record where a
   quantified variable is an operand of `+ - *`; a record passed to any other
   function is compared.

## Consequences

- The substitution lemma quantifies over the environments a substitution
  respects, needs both environments to be `Any` outside a finite set (so a name
  a `let` is renamed onto carries any sort), and a derivation moves between two
  environments that agree on its context and type (`typing_denv_agree`).
  `proofs/README.md` explains where each is used.
- A later sort (`Eq`, `Ordered`) is a new case of `sort`, `finer` and `sat`.
