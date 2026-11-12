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
   Every field gets a type variable, and every method's `self` is
   `{fields | ρ}` over those variables with one shared row variable `ρ` for
   whatever a later extension adds. After the bodies are inferred, the receiver
   type is folded once into `μs. {fields | ρ}` with each method typed `(s, …) ->`
   its result, and the literal's own type is the closed row of those fields. `ρ`
   is generalized with the binding, so each use of a record instantiates its own
   extension: `big = {...ball, size: 10}; big.moved()` returns `big`'s type. If a
   method calls a sibling through `self`, the methods' types mention another
   field's variable and the fold is skipped; the fields are then unified one at
   a time, which can still tie a knot per method. ADR 0032's occurs-check knot
   remains for receivers that are parameters.
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
   most twice the time of the same model written without methods. It does not:
   3.1 ms against 0.15 ms in a release build. Each method's type embeds the
   receiver twice, so the record type has about 110 terms against about 15, and
   `unify_ty` resolves whole types at every step. The criterion
   was waived for this build; sharing the receiver type, or resolving it
   shallowly, is #417.
7. **Final types are bounded too.** A type within `MAX_TYPE_TERMS` when
   inferred can grow as later unifications bind the variables inside it: six
   methods calling one another through `self` reach two million terms once
   substituted, and folding them back into `μ` form does not finish. Before the
   checker hands its types on, each is counted, with the count stopping early,
   against `MAX_UNFOLDED_TERMS`; one over it is a spanned "program too
   complex" error. Such records are now rejected in well under a second rather
   than checking forever, and records of more than about ten methods, or four
   that call siblings, hit the bound; making them fit is #417's work.
