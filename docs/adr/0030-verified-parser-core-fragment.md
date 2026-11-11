# ADR 0030 — The parser is verified for the core fragment only, over a trusted token stream

- Status: accepted (2026-11-11)
- Supersedes: ADR 0022 §7 ("we do not propose a verified parser … a tar pit").
- Context: ADR 0008 (the Coq development proves the type system over the
  locally-nameless core in `proofs/goat_ln.ott`), ADR 0022 (the grammar is the
  data `grammar/goat.peg`, interpreted by `parser/src/interp.rs`), and
  `docs/semantics.md` §10 (the n-ary surface forms are the k-fold iteration of
  the curried core).

## Context

ADR 0022 §7 declined to verify the parser, because a mechanized grammar for all
of goat buys the three parser requirements nothing. That judgement holds for the
whole language. It does not hold for the small fragment the proofs already
model: the proof's statements start at abstract syntax, so the distance between
source text and the term the proof talks about is unchecked trust. A verified
parser for just that fragment closes the distance where it matters and stays
small enough to finish.

## Decision

1. **The claim covers the core fragment only.** That is what `goat_ln.ott` has: a
   variable, a number, `true` and `false`, `program(x1, …, xk) do e done` with at
   least one parameter, a call `e(e1, …, ek)`, a binding `x = e1 e2`, a record
   literal `{l: e, …}`, a field access `e.l`, and parentheses. The n-ary forms
   are curried into the single-binder core, and field labels are interned to
   `nat` in first-occurrence order of the source text. `program()` with no
   parameter is excluded.
2. **The input is a trusted token stream.** The lexer is outside the claim, so
   nothing is said about how characters become tokens (identifiers, numbers,
   comments, the reserved words).
3. **Three claims, over the fragment.**
   - **T1.** Every parse of a core-fragment token stream denotes a term of
     `lc_exp`.
   - **T2.** The PEG parsing relation is deterministic: a token stream has at
     most one parse.
   - **T3.** Printing any core term and parsing the result gives back the same
     term.
4. **The grammar enters Coq by generation from `grammar/goat.peg`**, never by
   hand transcription. A transcribed copy is a second grammar that can drift
   from the one the parser runs; a generated one cannot.
5. **Everything outside the fragment is unverified.** `if`, `match`, tags, lists,
   operators, strings, loops, destructuring and `foreign` stay out. Widening the
   claim to any of them requires widening the soundness proof over `lc_exp`
   first; a parser claim cannot be larger than the language the proof knows.
   The Rust lowering (`checker/src/lower.rs`) and error recovery
   (`parser/src/interp.rs` `parse_recovering`) are not verified.
6. **The Rust side keeps the claim honest in the meantime.**
   - `parser/tests/rule_map.rs` classifies every rule of `goat.peg` as
     `core(<Ott production>)` or outside the core, and fails when a rule is
     missing from the map, when the map names a rule that no longer exists, or
     when it names a production `goat_ln.ott` lacks.
   - `checker/tests/core_roundtrip.rs` prints 10,000 generated core terms (fixed
     seed) as goat source in two styles, curried and grouped, parses and lowers
     them with the real front end, and checks the lowered HIR reads back as the
     same term. Its printer holds the parenthesisation rules the Coq printer
     mirrors.

## Consequences

- The real parser and lowering disagree with the Ott core in three places. They
  are findings, not bugs the fragment hides, and each is pinned by a test in
  `checker/tests/core_roundtrip.rs`:
  - **A function binding is recursive** (ADR 0003): in `x = program(y) do x done; x`
    the inner `x` is the binding itself. The Ott `let` binds `x` in `e2` only. The
    fragment's `let` is non-recursive, so the verified claim must either take the
    ADR 0003 rule for a `program`-valued binding or exclude self-reference.
  - **Functions of one block form a group** (ADR 0003): in
    `g = 1; f = program(y) do g done; g = program(z) do z done; f` the `g` in `f`
    reads the later function. In the Ott `let` it reads the earlier value.
  - **Duplicate record labels** are legal in the Ott core ("duplicates allowed")
    but are a lowering error (`{a: 1, a: 1}`). Likewise `program(x, x)` is a
    lowering error while the curried `program(x) do program(x) do e done done`
    is not.
  The generator avoids the three (unique names for function bindings, distinct
  labels per record, no duplicate parameter in one group). The Coq ticket decides
  whether T1 states these as side conditions on the term or changes the Ott.
- T1 to T3 say nothing about the Rust interpreter: they are facts about the
  generated grammar. Connecting the two stays a testing argument (the rule map
  and the round-trip test), not a proof.
- A call on a non-identifier (`1(2)`) and a number as field base (`(1).a`) lower
  fine; rejecting them is the checker's job.
- Adding a grammar rule now forces a classification decision in review, which is
  the point.
