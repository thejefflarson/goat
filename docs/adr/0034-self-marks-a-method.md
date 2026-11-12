# ADR 0034 — `self` marks a method, `.` calls methods, `::` calls without the record

- Status: accepted (2026-11-11).
- Amends: ADR 0031 (item 5, "`self` is a convention, not a keyword"; item 3,
  the `(r.f)(x)` escape) and ADR 0032 (how a method's receiver type is found).
- Context: ADR 0033 and its spike evidence. Methods inferred one by one see
  different views of their receiver (`{x | ρa}`, `{y | ρb}`, `{x, y | ρc}`), and
  tying those views into one recursive type does not finish for three methods.

## Decision

1. **`self` is a keyword.** A function whose first parameter is `self` is a
   method. `self` may appear only as the first parameter of a function written
   directly as a field of a record literal. Anywhere else, the checker reports
   "`self` only means something inside a record".
2. **A method is typed against the record it lives in.** When a record literal
   is built, `self` in each of its methods has that record's type. Every method
   in the record shares one receiver type, so the recursive type has one shape,
   however many methods there are.
3. **The receiver type stays open to extension.** `self` has the record's fields
   plus whatever a later extension adds. So `big = {...ball, size: 10};
   big.moved()` passes `big`, and under ADR 0033 an updating method returns
   `big`'s type.
4. **`.` calls methods only.** `r.f(a…)` means `(r.f)(r, a…)` and requires `f`
   to be a method. A field's type records whether it is a method, so a dot call
   on a parameter has one meaning. A dot call on a plain function is an error:
   "`double` has no `self`, so call it with `tools::double(5)`".
5. **`r::f` takes a field out without passing the record.** `r::f(a…)` means
   `(r.f)(a…)`, and bare `r::f` is the function value. On a method,
   `ball::moved(other)` passes `self` explicitly. `(r.f)(x)` still works, since
   a parenthesized expression is an expression, but `::` is the form the docs
   teach.
6. **No named types, no annotations.** Everything above is inferred.

## Consequences

- `::` is a new token. The lexer and `grammar/goat.peg` gain one rule,
  `GoatGrammar.v` regenerates, and T2 (determinism) is rechecked against it. T1
  and T3 either gain a rule for `r::f` or leave it outside the proven fragment,
  as path receivers are today.
- ADR 0032's machinery remains for receivers whose record is not known at the
  call (a parameter). The knot now ties a single receiver shape per record, and
  #403's nested knots are expected to become unnecessary. The build ticket
  measures this on a three-method model.
- #386's missing-`self` message changes: a dot call on a plain function suggests
  `::`.
- Plain functions stored in records are unaffected. They are ordinary values.
- `examples/closure_shapes.goat` moves to `r::f(3)`, and the docs teach `::`.
- Live reload of methods held in the model (canvas option (c)) builds on this.
  A method's code is known from the record literal that made it, so the host can
  rebind methods by field after an edit.
