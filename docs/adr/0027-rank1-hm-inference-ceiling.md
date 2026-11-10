# ADR 0027 — Rank-1 Hindley-Milner is the inference ceiling; computed bindings are monomorphic

- Status: accepted (2026-11-09)
- Context: two questions looked like one. First, whether goat should infer
  higher-rank polymorphism (a parameter used at two types inside its function
  body). Second, a miscompile: `a = addX({x: 1})` bound the result of a call and
  generalized it, so `a({y: 1})` and `a({y: 1, x: 2})` type-checked at two
  shapes while the program computed one value. Monomorphization lowers a
  polymorphic binding by specializing it per ground type; a *computed* value runs
  once, so it cannot be lowered at two ground types without boxing or re-running
  its effects. The checker accepted the program and mono produced wrong code.
- Decision: **rank-1 Hindley-Milner is goat's permanent inference ceiling.**
  Rank-2 polymorphism is decidable by intersection types (Kfoury and Wells: typability
  at rank 2 is decidable and has principal typings), but rank 3 and above is
  undecidable (Wells 1999). Annotation-free rank-2 is deliberately not pursued: it
  needs a different inference architecture (intersection types plus
  anti-unification over scoped-label rows) for near-zero audience value, and goat
  has no type annotations to fall back on. `proofs/GoatRank2.v` stays as a valid
  artifact of the rank-2 analysis; nothing depends on it.
  The miscompile is a **value-restriction** problem, decoupled from rank-2:
  rank-2 would not fix it, because the obstacle is lowering one once-evaluated
  value at two types. A `=` binding therefore generalizes its type variables only
  when its value is *syntactic*: a `program(...)` literal, a literal, a name, or a
  record or variant whose fields are all syntactic values. Any other value (a call,
  a `match`, an `if`, a field access, a spread) keeps a monotype.
- Consequences: a computed binding used at two incompatible types is a checker
  error that names the binding, says it is a computed value with one type, and
  suggests the fix: write it as a function so it re-specializes per use, for example
  `a = program(y) do addX({x: 1})(y) done`. The error carries the span of the
  conflicting call. The predicate is conservative: an unrecognized form is treated
  as computed, which can only turn a would-be miscompile into an error. Programs
  that used a computed binding at one type are unaffected. Mono, MIR, codegen and
  the Coq development do not change.
