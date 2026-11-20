# ADR 0040 — An `Int` widens to a `Float` where two scalars must agree

- Status: accepted (2026-11-20)
- Amends: [ADR 0017](0017-int-float-split.md) decision 4 (mixing) and its note
  "An `Int` argument widens at a call"; builds on
  [ADR 0039](0039-a-bare-numeral-binding-adapts-at-each-use.md).
- Context: #496, option 3; `docs/design/numbers-plan.md`.

## Context

The checker widened an `Int` beside a `Float` only when both types were already
concrete at the moment it looked (`join_operands`, `widen_arguments`). When
either was still a type variable, it unified instead, so the answer depended on
the order the checker visited the code:
`f = program(a, b) do a + b done` then `f(7 // 2, 2.5)` failed, and
`if c then 7 // 2 else 2.5 done` failed, while the same shapes with a concrete
callee parameter worked.

Plain Hindley-Milner cannot make `Int` meet `Float`. Subtyping and a type-level
`max` both cost principal types (see the design note). The calculus has
`T-ToFloat` already, and elaboration writes `float(e)` wherever the checker
widens, so no rule needs to change.

## Decision

1. **Widen at every scalar join site, never under a constructor.** The sites are
   the operands of `+ - * // %` and the comparisons; a call argument whose
   parameter is `Float` or a `Numeric` variable; the branches of `if` and
   `match`; the elements of a list literal. A record, a list or a function passed
   whole stays exact: `{a: i}` is not a `{a: Float}`.
2. **Comparisons widen** like arithmetic, so `==` across `Int` and `Float` is not
   transitive above 2^53. On the embedded profile an `Int` above 2^24 loses bits
   when widened. Both are accepted and documented.
3. **`Float` to `Int` is never implicit.** It is an error at the producer:
   "this is a `Float`, but an `Int` is needed here; use `round`, `floor` or
   `truncate`".
4. **No subtyping, no type-level `max`.** Principal types stay ordinary
   Hindley-Milner types with sorts.

## The solver

**Recording.** A join site that cannot decide on the spot records a *flow*
`producer => slot` (two types and the producer's span) in `Inferer::flows`
instead of unifying. It decides on the spot when both sides are the same scalar,
when they are `Int` and `Float` (the join is `Float`, and mono converts the `Int`
side), and when either side is a concrete type that is not a number or a
variable that cannot be one: those unify as before, so their errors read as
they did. The slot is a fresh variable carrying the operator's kind (`Numeric`,
`Eq`), which is the type of `a + b`, of the `if`, or of the list's elements.
Call arguments flow into the callee's own parameter type.

**Pure core.** `checker/src/flow.rs` holds the solver as a pure function of the
flow list: each end is a concrete `Int`, a concrete `Float` or a variable, and
the result is the scalar each variable takes, the groups of variables to unify,
and the edges that would narrow a `Float` into an `Int`. It touches no type
environment, so it is unit-tested on its own.

**Meaning.** Values form the order `Int < Float`. A variable reachable along
edges from a concrete end is *determined* from below: it takes the join of what
flows into it. Every other variable is *free*: a free variable takes the join of
the slots it feeds, since there is nothing else to say what it is (a parameter
`p` in `i + p` is an `Int`; in `i + p` and `p + 1.5` both, a `Float`, and the
`Int` side is converted). A component of free variables that no concrete end
touches is closed by unifying it, so the type that gets generalized is an
ordinary one (`program(a, b) do a + b done` stays `(a, a) -> a` with `a`
`Numeric`). A `Literal` variable needs no conversion: it simply becomes the
type it is given. The values are the least fixed point of two monotone
propagations (forward along every edge, backward only into free variables) over
a three-point order, so the answer does not depend on the order of the flows.

**Where it runs.** Flows are solved before a binding is generalized, because an
unsolved slot is a variable nothing ties to the parameters that feed it, and
generalizing would quantify it. Concretely: a function member of a recursive
group keeps the flows it recorded and the group solves them together when it
generalizes (as `generalize_members` does for the types); any other function
or syntactic value solves the flows recorded while it was inferred; and
whatever is left is solved when the whole program is inferred, before numbers
default. A computed (non-syntactic) binding is not generalized, so its flows
wait for the next solve. A binding nested in a function body solves its own
flows when it is generalized, which settles an outer parameter that the flows
mention earlier than the rest of the function body would: the one place the
result still depends on source order.

**Termination.** The solver visits each edge a bounded number of times: a
variable's value rises at most twice (`none`, `Int`, `Float`) and each rise
re-examines only the edges at that variable. The pre-pass that unifies flows
with a non-number end binds variables and removes edges, so it terminates too.

**Elaboration.** Node types are not changed: an `Int` producer keeps its type
and its slot becomes `Float`. Mono already converts at operators and at call
arguments from the node types; it now also converts an `if` or `match` branch
and a list element whose type is `Int` where the result is `Float`. A tail call
in a branch that is converted is not a tail call. The differential test writes
`float(e)` at each of these sites.

## Limits

- **The principality corner.** Closing an edge between two free variables by
  unification loses precision in one case: `program(i) do {a: i, b: if c then i
  else 1.5} done` is `(Float) -> {a: Float, b: Float}`, where full subtyping would
  keep `a: a`. Every call is accepted either way; a later `f(3).a` used as a list
  index is accepted by one and not the other.
- **Joins, not minima.** A free parameter used beside an `Int` in one place and
  a `Float` in another is a `Float`; the `Int` side is converted.
- `(i + j) + 1.5` adds as `Int` and then converts; `i + (j + 1.5)` adds as
  `Float`. Widening happens at the operator that meets the `Float`.

## Proofs

No rule changes. `GoatPhase2.v` gains an example that pins the elaborated form
of a widened program as derivable, and `docs/semantics.md` records where the
elaborator writes `float(e)`. The differential corpus exercises each join site.
