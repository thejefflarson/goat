# ADR 0012 — Built-in constraints live on type variables; mono derives `==`, `print` and record arithmetic as plain MIR functions

- Status: accepted (2026-11-03)
- Context: Phase 8 (built-in constraints), `docs/plan.md` ("Built-in constraints",
  "No user-defined operator overloading"), ADR 0010 (layout identity),
  `docs/mir.md`.

## Decision

### The checker carries three constraints on variables

`eq` (no function anywhere inside), `appendable` (`String` or a list) and
`numeric` (`Number`, or a record whose fields are all `numeric`) are held in two
side tables on the inferer, `kinds` for type variables and `row_kinds` for row
variables. They never appear in a type or a scheme.

- Binding a variable removes its constraints and checks them against the type it
  is bound to, recursively through records, variants and `μ` bodies. A variable
  inside that type takes the constraint on; an open row hands it to every field
  it later gains (`rewrite_row`) and to its tail.
- Two constrained variables unify by moving the first's constraints onto the
  second, so they intersect. `numeric` and `appendable` exclude each other.
- `instantiate` copies the constraints of a scheme's variables onto the fresh
  ones, so `add = program(a, b) do a + b done` is polymorphic over every
  `numeric` type and checks each call.
- `appendable` on a variant means its tags are only `Empty` and `Link`; the
  payload shape is not checked. No surface syntax applies it yet (`join` will).
- A violation is a spanned error that names the constraint in plain words
  ("can't compare functions with `==`", "`+` needs numbers or records of
  numbers, but this is `Bool`"). It names the operator when found at the
  operator, and says "arithmetic" when found later at a call.
- `< <= > >=` stay `Number`-only.

### Mono derives the per-type functions; the backends learn two nodes

`==`/`!=`, the printer behind `print`, and field-wise `+ - * /` on records are
ordinary MIR functions built from a ground type (`mir/src/mono/structural.rs`),
so the interpreter and every backend run them unchanged. Each is memoized on the
canonical form of its type (`canon::canonical`), registered before its body is
built, so a recursive type reuses the function it is in the middle of building
and derivation terminates. Where the shape allows it the recursive call is a
`TailCall` (the last field of a payload, the tail of a list), so comparing or
printing a long list uses constant stack. Printing a list writes `[1, 2, 3]`
through a second function for "the rest of the list", so it is iterative too.

Two MIR nodes cover what a function cannot express:

- `StrEq(a, b)` compares two strings by bytes; both operands are borrowed.
- `Write(..)` appends to the host's current output line (`Number`, `Str`, `Lit`)
  or ends it (`End`). The wasm module imports `write_number`, `write_string`,
  `write_end` and `write_int` only when it uses `Write`, after the `print_*` imports. The
  existing root `print_*` imports are unchanged: each still prints one line.

`print` is a builtin HIR node (`ExprKind::Builtin`), resolved when the name is
not otherwise bound, so a user definition replaces it with a warning. A call
becomes a direct call to the printer for the argument's type; a use as a value
becomes a closure over it.

## Consequences

- Strings print raw at the top level and quoted inside a record, variant or
  list. Functions print as `<function>`, `Unit` as `Unit`.
- Records print with labels in layout (sorted) order.
- `print` is a normal `Unit`-returning call, so the RC pass and the "erase Unit
  values, keep calls" rule preserve it with no effect marker.

## Amendment (2026-11-23): `/` is decided like `+`

The checker used to decide `/` at the operator, from the operand types it had
seen so far: a record on either side fixed record division, anything else fixed
`Float`. So the verdict depended on unification order:
`(program(a) do a / a done)({x: 1.0})` was refused, while `{x: 1.0} / {x: 3.0}`
was accepted, although both type.

`/` now joins its operands the way `+` does (`join_operands`), with a sort of its
own. A `Quot` variable (`Kind::Quot`) stands for the type of a quotient: it
settles to `Float`, or to a record whose fields are all `Quot`. `Quot` is finer
than `Numeric` (every quotient type is a number) and incomparable with `Literal`,
because a numeral may be an `Int` and a quotient may not; a `Literal` and a
`Quot` variable that unify meet at `Float`. The operator then yields the joined
type, and an `Int` operand still converts to `Float` where the join is `Float`
(ADR 0017). The checker therefore accepts and rejects `/` the same in either
statement order.

A function whose operands stay open is polymorphic over the quotient types:
`program(a, b) do a / b done` now prints as `(t4, t4) -> t4` with `t4` a `Quot`
variable, where it printed `(Number, Number) -> Number` before. A program whose
operands are concrete types prints as it did.
