# ADR 0031 — A call through a dot passes the record first

- Status: accepted (2026-11-11)
- Context: ADR 0027 (rank-1 inference, value restriction), ADR 0028 (records
  are never recursive), ADR 0030 (the verified parser's core fragment), and the
  brief `docs/ideas/dot-call-methods.md`.

## Context

Kids want to attach behaviour to a thing, as `ball.moved()` reads in Python or
Rust. goat records can already hold functions, and a record bound with `=`
whose fields are values is generalized. So `a.y(a)`, which hands the record to
its own function, already type-checks and runs. What is missing is the syntax.

## Decision

1. **`r.f(a1, …, ak)` means `(r.f)(r, a1, …, ak)`, and `r.f()` means
   `(r.f)(r)`.** The rule is purely syntactic. Lowering desugars it before the
   checker runs, so inference, rows, mono and codegen do not change.
2. **The receiver is evaluated once.** A receiver that is a variable or a path
   of field accesses (`o.inner`) is repeated, which is unobservable and keeps
   each use of the root variable separately instantiated. Any other receiver is
   bound once to a hidden, hygienic name.
3. **`(r.f)(x)` calls a stored function without the record.** A parenthesized
   projection is not a dot call.
4. **`r.f` without parentheses stays field access.**
5. **`self` is a convention, not a keyword.**
6. **No pipe operator, and no type-directed method lookup.** `"abc".length()`
   is not supported, because resolving a name by the receiver's type breaks
   principal types. Builtins stay free functions.
7. **Methods on a receiver with a single fixed type stay rejected for now.**
   The supported receiver is a record value bound with `=` (or a path into
   one), which ADR 0027 generalizes. A parameter, a call result, a spread copy
   and an `if` or `match` result each have one fixed type, so the method's
   parameter would have to contain the receiver's own type. That case needs a
   recursive type. The checker gives it a targeted message,
   and ADR 0028's rule that records are never recursive stands. The direction
   is structural: a recursive type guarded by a function parameter inside a
   record field, which the checker infers. Named record types are not the
   route, because a kid must never have to declare a type to call a method.
   Whether to accept the structural route is decided by a later ADR, after a
   spike measures mono support, the proof boundary and error quality.

8. **The rewrite happens in lowering** (`checker/src/lower.rs`). The grammar
   does not change: `r.f(x)` and `(r.f)(x)` already parse to different trees.
   Lowering records each dot call in a side table that the checker reads for
   its messages, so the call node and mono are unchanged.

## Consequences

- The meaning of `r.f(x)` changes for existing programs that store plain
  functions in records. The one in-repo program that does so,
  `examples/closure_shapes.goat`, migrates.
- The verified parser's T1 denotation and T3 printer change for the dot call.
  Inside the core fragment the receiver is restricted to a variable, so the
  desugaring introduces no binder. The Coq change lands in its own PR after the
  Rust change. Until then the proofs describe the old meaning of `r.f(x)`,
  which ADR 0030 permits because T1–T3 make no claim about the Rust lowering.
- An arity mismatch on a dot call gets a spanned diagnostic that names the
  passed record and both fixes.
