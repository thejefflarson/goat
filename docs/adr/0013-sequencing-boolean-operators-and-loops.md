# ADR 0013 — Sequencing is `a; b`; `and`/`or`/`not` and loops lower to `if` and tail calls

- Status: accepted (2026-11-07)
- Context: Phase 8 (P8e). Supersedes the "sequencing" remarks left open when the
  postfix-call ambiguity was closed (`1 (2)` reads as a call); `docs/plan.md`
  ("Other language features"); ADR 0006 (capturing closures), which the loop
  lowering relies on.

## Context

A program was one chain of bindings ending in one expression, so a bare call such
as `print(x)` could not stand as a statement: the prelude worked around it with
throwaway bindings (`shown = print(...)`). The plan offered two forms, `expr rest`
(read as `_ = expr  rest`) and `a; b`.

`expr rest` cannot be parsed. A `(` after an expression is a call, and a `-` after
one is subtraction, so `print(1) (2)` and `print(1) -2` already mean something
else. Whitespace-significant calls or a statement separator were the two ways out
of that ambiguity (see the closed issue on it).

## Decision

**Sequencing is `a; b`.** `a` runs, its value is dropped, and `b` runs; the whole
is `b`'s value. A trailing `a;` makes the whole expression `Unit`. A statement
ends only at a `;`, so the call/minus ambiguity never arises. It lowers to a `Let`
of a fresh, unnameable symbol, so no HIR, MIR or backend node is added.

A binding's value stops at `;` (`value` in the grammar, not `expr`), and the `;`
after a binding is optional: `x = 1; f(x)` and `x = 1  f(x)` both put `x` in scope
for what follows. Without that, `x = 1; x` would sequence outside `x`'s scope.

**`and` / `or` / `not`** are reserved words. `a and b` is
`if a then b else false done`, `a or b` is `if a then true else b done`, and
`not a` is `if a then false else true done`, so the right operand of `and`/`or`
runs only when the left does not decide the result. Binding strength, loosest first:
`or`, `and`, `not`, `==`/`!=`, comparisons, `+ -`, `* /`. `not` sits below `==`
(`not a == b` is `not (a == b)`), as in Python.

**Loops** lower, in the checker, to a local self-recursive function whose recursive
call is in tail position:

- `repeat n times do B done` counts `i` from 0 while `i < n`.
- `for i from a to b do B done` counts `i` from `a` while `i <= b`, so both ends
  are included; counting down runs zero times.
- `for x in xs do B done` matches `Empty` / `Link(x, rest)` and recurses on `rest`.

`n`, `a`, `b` and `xs` are evaluated once, in that order. The body's value is
discarded and the loop is `Unit`. No `Loop` node is added to MIR: tail calls
already run in constant stack in the interpreter and in wasm, closures capture the
loop's free variables (ADR 0006), and reference counting needs no new rule, so
loops free correctly by construction and nothing in inference, mono or the
interpreter changed.

`for`, `and`, `or` and `not` are reserved (`repeat` and `times` already were).
`from`, `to` and `in` are keywords only inside a `for` header, so `line.from` and
`{to: 1}` keep working.

## Consequences

- Loop counters are `Number` (a float) until the Int/Float split lands (ADR 0001).
- The loop body is not required to be `Unit`; a non-`Unit` body value is dropped,
  as with `;`.
- A `;`-sequenced block costs one level of the lowering depth limit per statement,
  the same as a chain of bindings, so one block holds about 200 statements. Making
  that limit a function of tree shape rather than a count means walking `Let`
  chains iteratively in inference, mono and the interpreter; not done here.
- `true and 1` reports "expected `Number`, found `Bool`" at the whole expression,
  because the generated `else false` is what the `if` blames. `or` blames the right
  operand correctly. A sharper message needs a dedicated HIR node; not done here.
- Statements after a loop need a `;` (`repeat 3 times do … done;`), as after any
  other expression.
