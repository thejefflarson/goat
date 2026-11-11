# Dot calls pass the record first

Status: settled with the owner, 2026-11-11. Decision recorded in ADR 0031.

## The idea

Let a record carry functions that act on it, the way Python and Rust methods
do, without a new kind of value and without type annotations.

```
ball = {x: 1, speed: 2, moved: program(self) do {...self, x: self.x + self.speed} done};
ball.moved()            # means (ball.moved)(ball)
```

## The rule

A call through a dot passes the record first:

- `r.f(a, b)` means `(r.f)(r, a, b)`.
- `r.f()` means `(r.f)(r)`.
- The receiver is evaluated once. `make().f(a)` binds the result of `make()`
  before it projects `f` and passes it.
- Field access without parentheses stays field access: `r.f` is the function
  itself, not a call.
- To call a stored function without passing the record, parenthesize the
  projection: `(r.f)(a)`.
- The first parameter is a parameter like any other. `self` is a convention,
  not a keyword.

## Why this works with no type-system change

A dot call desugars to an ordinary call before the checker sees it, so
inference, rows, mono and codegen are untouched. On current master the
spelled-out form already type-checks and runs:

```
a = {x: 1, y: program(self) do self.x done};
a.y(a)        # 1
```

A record bound with `=` whose fields are values generalizes (ADR 0027), so
each use of `a` gets its own instance of the method's type, and the record's
type never has to contain itself.

## What stays out

**Calling a method on a record received as a parameter.**

```
call_y = program(p) do p.y() done
→ cannot construct the infinite type t = ({y: t | …}) -> …
```

Inside `call_y`, `p` is monomorphic, so `p.y` must accept `p` itself, and that
type contains itself. Accepting it needs recursive types, either structural
(μ-types inferred by the checker) or nominal (a declared record name). Both are
deferred, and the owner chose the direction: pursue the structural route and
never require named types for it. The spike for the structural route typed in the checker but crashed
mono in `lower_ty`, falls outside the proven core fragment (ADR 0030), and
prints `μt.{…}` errors. The nominal route needs a declaration form that has to
be squared with the no-annotations rule. This program keeps today's error, with
a better message (below).

**Methods on strings and lists.** `"abc".length()` would need to find
`length` by the receiver's type, which breaks principal types. Builtins stay
free functions: `char_count("abc")`.

**A pipe operator.** The owner rejected `x |> f(a)`.

## Costs

- **The meaning of `r.f(x)` changes.** Today it calls the stored function with
  `x`; afterwards it passes `r` first. One shipped program relies on the old
  meaning: `examples/closure_shapes.goat:22` (`r.f(3) + r.g(2)`). It moves to
  `(r.f)(3)` or gains a `self` parameter. The docs (`docs/llm.md`, the
  README) change with it.
- **The verified parser's denotation changes.** The core fragment (ADR 0030)
  includes both a call and a field access, so today `r.f(x)` denotes
  `App(Field(r, f), x)`. T1 must now denote the desugared term. T3's printer
  must print `App(Field(r, f), x)` as `(r.f)(x)`. Binding a non-variable
  receiver once needs a fresh name in the core, which meets T3's
  `names_distinct` side condition. Restricting the fragment's dot call to a
  variable receiver keeps the proof change small: `r.f(x)` becomes
  `App(App(Field(r, f), r), x)`, with no new binder.
- **Error messages must speak in dot-call terms.** Two cases need targeted,
  spanned checker diagnostics:
  - An arity mismatch on a dot call, where the stored function lacks the
    record parameter: "`ball.moved()` passes `ball` as the first argument, but
    `moved` takes no parameters. Add one, like `program(self) do … done`, or
    write `(ball.moved)()` to call it without the record."
  - The infinite-type error on a method call through a parameter: name the
    limitation and suggest passing the function instead of the record.

## Handoff to plan-sprint

Theme: dot calls pass the record first (ADR 0031). Expected tickets:

1. Desugar dot calls in CST→AST lowering, evaluate the receiver once, and add
   `(r.f)(x)` as the explicit escape. Migrate `examples/closure_shapes.goat`.
   Add checker tests and end-to-end run tests.
2. The two targeted diagnostics: an arity mismatch on a dot call, and a method
   call through a parameter.
3. Docs: `docs/llm.md`, the README, an example (`examples/methods.goat`).
4. Coq: update T1's denotation and T3's printer for the dot call, with the
   receiver restricted to a variable in the fragment. Keep 0 admits and 3 closed
   theorems. This is proof work done in one thread, not a swarm.
5. Editor completion: after `r.`, offer fields. Check whether the goat
   completer needs any change.
