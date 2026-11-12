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
5. **`::` calls functions without `self` only.** `r::f(a…)` means
   `(r.f)(a…)`, and bare `r::f` is the function value, so a record of tools
   is called as `math::double(5)`. A method is called with `.` and nothing
   else: `ball::moved()` and `ball::moved(other)` are errors that steer to
   `ball.moved()` and `other.moved()`. Rust also allows `Type::method(x)`; goat
   does not, so each kind of function has one call form, and `::` puts no shape
   constraint on its arguments. `(r.f)(x)` still works, since a parenthesized
   expression is an expression, but `::` is the form the docs teach.
   A record cannot hold its own constructor: that field would have to refer to
   the record, and goat values are acyclic, while a `new` that rebuilds a
   literal returns a record without `new`, so not the record's shape. A new
   ball is a prototype copy (`{...ball, pos: 5}`), a method returning a
   changed copy (`ball.at(5)`), or a top-level function (`make_ball(5)`).
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

## Implementation addendum (2026-11-11)

Decisions the build made where the ADR left room. The three-method model
(`x`, `y`, `update`, `nudge`, `draw`; `m.nudge().update().draw()` and
`m = run(init(), 4); m.draw()`) now checks and runs through the interpreter and
wasm with one recursive type and no nested knots.

1. **Method-ness is a flag on the record field, not on `Func`.** `Row::Extend`
   and `Row::Maybe` carry a `method` type. It is a variable bound to one of two
   constants, `METHOD` or `PLAIN`, by the same mechanism as ADR 0033's presence
   flags, so generalization, instantiation and unification carry it with no
   second substitution. `r.f(a)` unifies the flag of `f` with `METHOD`. `r::f`,
   `(r.f)` and plain projection leave it alone. Unifying a `METHOD` field with a
   `PLAIN` one is an error that names the field, so a list that mixes the two
   shapes says so. Mono and canon erase the flag: a layout never depends on it.
2. **`self` is reserved by lowering and the checker, not the lexer.** The
   parser still reads `self` as a name, so `grammar/goat.peg` and the proofs do
   not change. Lowering reports `self` as a parameter anywhere but first, `self`
   as the first parameter of a function that is not written directly as a
   record field, and an unbound `self`. A field of a spread literal
   (`{...r, f: program(self) do … done}`) may be a method; its receiver is typed
   by ADR 0032's knot, since the literal's final shape is the spread's.
3. **A record literal with methods is typed like a `letrec` over its fields.**
   Every field gets a type variable, and the literal gets one receiver variable,
   `s`, that every method's `self` has as its type. `s` stands for
   `{fields | ρ}` over those variables, with one shared row variable `ρ` for
   whatever a later extension adds, and it is never bound while the bodies are
   inferred: unifying `s` with a record unifies that record, so `self.x` and
   `{...self, …}` see the fields, and a sibling call `self.g()` constrains
   `g`'s variable without a cycle through its own type. This is how OCaml types
   objects. After the bodies are inferred, each method is unified with its
   field's variable, a result equal to the receiver's record is written `s`, and
   `s` is bound once to `μs. {fields | ρ}`. The literal's own type is the closed
   row of those fields, each mentioning `s`. `ρ` is generalized with the
   binding, so each use of a record instantiates its own extension:
   `big = {...ball, size: 10}; big.moved()` returns `big`'s type. Methods that
   call siblings, chain through `self`, or update the record all take this one
   path, and ADR 0032's occurs-check knot remains for receivers that are
   parameters.
4. **The highlighter shows `self` as a keyword by a rule both sides share.**
   `parser::lexer::highlight` marks a name `self` as a keyword (as it marks
   declared tags), and `editor/highlight.goat` does the same. `lexer::lex` and
   `tokenize`, which the parser reads, keep `self` a name, so the highlighter
   and the lexer agree byte for byte on `highlight`'s output. The rule is
   lexical, so `self` reads as a keyword everywhere, a field label `{self: 1}`
   included; telling the label apart would need the parse, which the
   highlighter does not have.
5. **Errors.** Each is spanned and names neither `μ` nor a raw variable:
   a dot call on a plain function suggests `::` and the `self` fix; `self`
   outside a record, or not first, says where it goes; `r::f` on a method says
   "`moved` has `self`, so call it with a dot: `ball.moved()`. `::` is for
   functions without `self`, like `math::double(5)`.", naming one of the
   record's own functions without `self` as the example when it has one, and
   suggesting `other.moved()` when the first argument names a record. `r::f` settles a field whose flag is
   still open as plain, as `r.f(…)` settles it as a method; a call on a record built by a method
   without `...self` names the method that dropped the rest. The earlier
   `(r.f)()` suggestion is now `r::f()`.
6. **Check time.** The ticket asked that the three-method model check in at
   most twice the time of the same model written without methods. The first
   build took 3.1 ms against 0.15 ms in a release build, because each method's
   type embedded the receiver twice and `unify_ty` resolved whole types at every
   step. The receiver variable, shallow resolution in `unify_ty` and
   `unify_row` (types in the substitution are shared, so following a variable
   copies nothing), unresolved keys for the pairs unification assumes equal, and
   a cheaper search for types to refold bring it to about 1.3 ms against 0.15
   ms: still about nine times, not two. What is left is mostly `run`'s own
   parameter, which a dot call on a parameter ties into nested knots (ADR
   0032), and `finish` copying `n` receiver types for `n` mentions of `self`.
   A literal of thirty methods, half of them calling siblings, checks in about
   12 ms in a release build.
7. **Final types are bounded too.** A type within `MAX_TYPE_TERMS` when
   inferred can grow as later unifications bind the variables inside it, so
   before the checker hands its types on, each is counted, with the count
   stopping early, against `MAX_UNFOLDED_TERMS`; one over it is a spanned
   "program too complex" error. A record literal's receiver is counted before
   it is resolved. A literal of twelve updating methods, or four that call
   siblings, now checks; one of a hundred and twenty is refused. A method
   called on the result of a sibling call (`self.bump().bump()`) is still
   refused, with "cannot construct an infinite record type", because the
   result's type is not yet known to be the receiver when the second call is
   typed.
