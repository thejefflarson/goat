# Numbers: softening the Int/Float edges (design pass for #496)

Status: proposal. Nothing here is decided; section 6 lists what the owner must decide.
Every claim marked "measured" was run against `master` at `ae0e6e1` with a debug build; the
Option 1 spike was a one-line checker change, discarded after measuring.

## 0. What the code does today (the ticket's premise is partly out of date)

The ticket says Option 3 "reverses the phase-1 decision that Int meets Float only through
`float(e)`". The checker already widens, in an order-dependent way. Three facts:

1. **The calculus has no subtyping and does not need it for the surface behaviour.** `float(e)`
   is what elaboration writes at every place the checker accepts an `Int` for a `Float`
   (`docs/semantics.md` section 4, T-ToFloat; `proofs/README.md`). That stays true under every
   option below. Whether the elaborator inserts it exactly where the checker widens is checked
   by the differential test, not proved.
2. **The checker widens only when both types are already concrete at the moment it looks.**
   `join_operands` (`checker/src/infer.rs`) widens `Int` beside `Float` at an operator;
   `widen_arguments` widens an `Int` argument when the callee's parameter is already `Float`.
   If either side is still a type variable, the two are unified instead, so the answer depends
   on the order the checker visits the code. Measured:

   | program | result |
   |---|---|
   | `i = 7 // 2` then `i + 1.5` | `4.5` |
   | `g = program(x) do x + 1.5 done` then `g(7 // 2)` | `4.5` |
   | `f = program(a, b) do a + b done` then `f(7 // 2, 2.5)` | error: expected `Int`, found `Float` |
   | `if true then 7 // 2 else 2.5 done` | error: expected `Int`, found `Float` |
   | `h = program(p) do p.a + 1.5 done`, `h({a: 7 // 2})` | error: expected `Float`, found `Int` |
   | `n = 3`, `{a: n + 1.5, b: n // 2}` | error: `//` needs whole numbers, but this is a `Float` |
   | `n = 3`, `{b: n // 2, a: n + 1.5}` (the two swapped) | `{b: 1, a: 4.5}` |

   The last two rows are one program in two orders. That is the real defect: the answer
   depends on source order, so there is no principal type to speak of.
3. **A list literal with an `Int` and a `Float` element already type-checks** (`[i, 2.5]` runs
   and prints `[3, 2.5]`), because a literal's elements get separate types and only a use
   unifies them. It is not a widening; it is a hole that a later use (`map`, `sum`) turns into
   a mismatch. Option 3 closes it properly.

Mono already **rematerializes** a generalized value binding at each use's type
(`mir/src/mono.rs`, `rematerialize`, from #376). Option 1 needs no new mono mechanism.

## 1. Option 1: a number bound with `=` adapts at each use

### Checker

`Inferer::generalize(ty, function)` removes `Literal` variables from the quantified set when
`function` is false (`in_ty.retain(|v| function || !self.is_literal(*v))`). Option 1 deletes
that filter for bindings the value restriction lets generalize (`is_syntactic_value`), so
`n = 3` gets the scheme `forall a:Literal. a` and each use instantiates a fresh `Literal`
variable. `default_numbers` already skips variables quantified in a scheme, and each use's own
variable defaults to `Int`.

### Mono and codegen

No new mechanism. `n = 3` is a generalized value binding, so `rematerialize` lowers `3` at the
use's type: `Int` at one use, `Float` constant at another. Constants have no effects, so
evaluating per use is unobservable. Relation to #372: that ticket fixed records holding a
polymorphic function; this is the same path with a `Literal`-sorted variable.

### Spike (measured)

Removing the filter and running the whole workspace test suite: everything passes except

- `a_shared_number_is_a_float_once_anything_needs_a_float` (checker unit test): asserts the old
  behaviour, to be inverted.
- 5 editor query tests (`checker/tests/query.rs`): the scope list and hover show a generalized
  literal as a raw variable (`t1600`) instead of `Number`. The query printer must print a
  `Literal` scheme variable as `Number`. Small.
- `a_record_held_in_two_places_is_rebuilt_once` (`cli/tests/reload.rs`): see "cost" below.

`{a: n + 1.5, b: n // 2}` runs and prints `{a: 4.5, b: 1}`, in either order.

### Which programs newly type-check

- The ticket's example, in either order.
- `p = {x: 1, y: 2}` then `{a: p.x + 1.5, b: p.y // 2}`: each field of a record of literals is
  its own number.
- `n = 3` used as a list index and as `n + 1.5`, in either order.

### Programs whose meaning changes

A binding that was one shared `Float` because one use needed a `Float` is now an `Int` at its
other uses. The value is the same (`Float 3` prints `3`), but `Int` and `Float` differ in two
places:

- Overflow. `n = 4611686018427387904`, `a = n + 1.5`, `b = n * 2`: `b` is `9.22e18` today and
  traps (`this number got too big`) after. Measured.
- Division by zero, once Option 2 lands: see section 2.

### Cost: records lose sharing

A record binding of literals (`init = {a: {r: 1, g: 2, b: 3}, b: {...}}`) is also a syntactic
value, so it generalizes and is rebuilt at every use: one allocation per use instead of one
shared object, and `cli/tests/reload.rs` checks that the reload snapshot keeps the sharing
(ADR 0035). This is the only runtime cost found. Section 6, D6, offers three ways out.

### An asymmetry that remains

`n = 3` adapts; `n = 2 * 3` does not, because a computed binding is not a syntactic value
(ADR 0027) and stays one monomorphic number. With Option 3's deferred join the asymmetry
mostly disappears (a computed `n` can be an `Int` and widen at `n + 1.5`); it stays only
where a number must be a `Float` inside a structure (section 3, "Where Option 1 still matters").

### Rules and proofs

None. The phase-2 rules already accept it: `T-Let` generalizes a syntactic value with the
sorts of its variables, `T-Num` gives a numeral any `Literal` type (`docs/semantics.md`
section 5). The checker is brought closer to the rules, which is a completeness gain, not a
rule change. Algorithm W (`GoatInfer.v`) is unchanged: it is already incomplete for numerals
at `Float` (`1 + 1.5`). `docs/semantics.md` needs no edit; ADR 0017's implementation note
("a binding that is not a function keeps its literals' types shared") is superseded and the
ADR gets an amendment.

## 2. Option 2: `//` and `%` on Floats

### Typing

Today `//` and `%` unify both operands with `Int` and give `Int` (`type_whole_division`);
a `Float` operand is a spanned error pointing at `round`. Proposed: type them as `+ - *`,
generic over `Numeric`: `(a, a) -> a`. Consequences:

- `program(x) do x // 2 done` was `(Int) -> Int`. It becomes `forall a:Numeric. (a) -> a`, so
  `half(7.5)` type-checks. `half(7)` still gives an `Int`.
- A number whose only `Int` constraint was `//` is no longer forced to `Int`
  (`n = 3  a = n + 1.5  n // 2` then makes `n` a `Float`). Value unchanged; see D7 for
  the division-by-zero difference.
- Records of numbers are `Numeric`, so `{x: 7, y: 9} // 2` would work field by field, as
  `+ - *` and `/` do (`type_division` already handles records). D5 offers scalars-only.

### Semantics (proposal, owner decides)

Python's, as the ticket says, for finite operands:

- `a % b` has the sign of `b`; `7.5 % 2 == 1.5`, `-7.5 % 2 == 0.5`, `7.5 % -2 == -0.5`.
- `a // b` is the floor of the exact quotient of the two doubles; `7.5 // 2 == 3`,
  `-7.5 // 2 == -4`.
- The identity `(a // b) * b + a % b == a` holds up to float rounding (it is exact for `Int`).
- CPython computes both from `fmod` (`float_divmod` in `Objects/floatobject.c`): remainder
  `r = fmod(a, b)`; if `r != 0` and its sign differs from `b`'s, add `b` to `r`. The quotient
  is `(a - r) / b`, rounded to the nearest whole number. This is why `1 // 0.1 == 9` and
  `1 % 0.1 == 0.0999...`, since `0.1` is slightly above a tenth; the naive `floor(a / b)` gives
  `10` there and breaks the identity. Reproduced from memory, to be checked against a
  CPython build when implemented.
- **Result type:** `Float`. `7.5 // 2` prints `3`, because a whole `Float` already prints with
  no decimal point (measured: `print(3.0)` prints `3`). An `Int` result would need a trap for
  values an `Int` cannot hold and would make `//` unlike `+ - *`.
- **Zero divisor, NaN, infinity:** follow IEEE like `/` (measured: `1 / 0` is `inf`,
  `0 / 0` is `nan`): `x // 0.0` is the floor of `x / 0.0` (`inf`, `-inf` or `nan`),
  `x % 0.0` is `nan`, `inf % b` is `nan`, `a % inf` is `a` when `a` and `inf` have one sign
  (Python's rule: `-5 % inf` is `inf`). `Int` is unchanged: a zero divisor traps.

### Runtime and codegen

- MIR: two new `FloatOp`s (`FloorDiv`, `Mod`) beside `Add Sub Mul Div` (`mir/src/mir.rs`),
  or one `FloatFn` pair. `mono.rs` `bin` dispatches `FloorDiv | Mod` on the operand type
  instead of always calling `whole_division`.
- Interpreter: Rust's `%` on `f64` is `fmod`, so the Python adjustment is a few lines.
- wasm: has `f64.floor` but **no `fmod` instruction**. Exactly reproducing `fmod` needs an
  emitted helper function (the usual algorithm shifts and subtracts the mantissa, roughly
  40 lines of hand-written wasm, or a loop on `a - b * trunc(a / b)` that is exact only
  while the quotient fits 53 bits). This is the one piece of Option 2 with real work. The
  alternative is a host import, which ADR 0017 avoided for `sqrt` and `truncate` ("no host
  has to provide them").
- Embedded `f32` profile: compute in `f64` and round the result to `f32`; `fmod` of two `f32`
  values is exact in `f64`, so only the final quotient rounds. Same rule ADR 0017 uses for
  `+ - * /`.

### Proof changes

- `goat.ott` `Jsig`: `Whole` (`o : Int, Int => Int`) stays for `Int`; add the `Float` case
  (`o : Float, Float => Float`) or fold `//` and `%` into the `Ring` rules as a generic rule
  over `Numeric` (`docs/semantics.md` S-Ring). `Quot`-style: no trap, because `Float` is
  opaque.
- `bin_step`: every `Float` `//` and `%` relates to every `Float`, the same free relation as
  `+ - * /`. No new theorem; progress, preservation and soundness gain one case each
  (inversion on `bin_sig`). If the owner picks "trap on a zero `Float` divisor" (D4) the model
  needs a `Float` trap outcome, which is the larger change.
- `GoatPhase1.v` / `GoatPhase2.v`: a few checked examples. Algorithm W: `bin_arg` gets the
  new operators; soundness gains a case. W stays incomplete for generic operators
  (ADR 0038, decision 4).
- The Coq-extracted checker used by the differential test must be re-extracted.

## 3. Option 3: an `Int` widens to a `Float` where they meet

### The trap

Plain HM unifies, and `Int` and `Float` do not unify. The two textbook repairs both cost
principal types:

- **Subtyping (`Int <: Float`)** gives each unknown a *bound*: `program(a, b) do a + b done`
  becomes `forall a b c. (a <: c, b <: c, c:Numeric) => (a, b) -> c`. Principal types exist
  for atomic subtyping (Mitchell 1984; Fuh and Mishra 1989) and MLsub (Dolan and Mycroft
  2017) infers them without annotations, but the types are constraint sets, errors name
  bounds ("`a` is at most `Float`"), and the proofs need a subsumption rule, which the
  calculus deliberately lacks. For records and functions it goes to full structural
  subtyping: a record `{a: Int}` passed where `{a: Float}` is wanted must be rebuilt (its
  field converts), a list needs a copy, and a function `(Float) -> Int` passed where
  `(Int) -> Float` is wanted needs a wrapper closure (contravariance). That breaks ADR 0032's
  shared recursive records and the reload sharing of ADR 0035.
- **A type-level `max`** (`(a, b) -> a ⊔ b`, Julia's `promote_type`): unifying `a ⊔ b` with a
  known `Float` is a disjunction (`a` is `Float` or `b` is `Float`) with no most general
  answer. `forward(a + b)` is enough to hit it. There is no principal type.

### Proposed route: widen at scalar join sites, solved after the binding is inferred

Keep unification. At a **join site**, where the language requires two scalar expressions to
have one type, record a *flow* `producer ⇒ slot` instead of unifying immediately. When the
enclosing top-level binding is inferred, solve the flows before generalizing:

- both ends concrete: `Int ⇒ Float` inserts a coercion, equal types need none, and
  `Float ⇒ Int` is an error that names `round`, `floor` and `truncate`;
- a `Literal` variable on either end needs no coercion: it becomes whatever the rest of the
  program forces, `Float` if only `Float` slots need it, `Int` if an `Int`-only slot also does;
- a `Numeric` or `Literal` variable with concrete producers takes the join of them
  (`Float` if any is `Float`);
- an edge between two variables that stay free is closed by unifying them, so the type that
  gets generalized is an ordinary HM type with sorts.

This is **deferred**, not eager, so the answer no longer depends on source order. Elaboration
writes `float(e)` at each solved `Int ⇒ Float` edge, so **the calculus and the phase 1 and 2
typing rules are unchanged**: no new rule, no subtyping, `T-ToFloat` already exists.

### Where the widening applies

| | (a) operators only | (b) scalar join sites | (c) everywhere (subtyping) |
|---|---|---|---|
| operands of `+ - * / // %` and comparisons | yes | yes | yes |
| arguments to a function whose parameter is `Float` or a `Numeric` variable | no (call needs `float`) | yes | yes |
| `if` and `match` branches | no | yes | yes |
| elements of a list literal | no | yes | yes |
| record fields, lists, functions passed whole | no | no | yes (copies, wrappers) |
| principal type | n/a, order-independent once deferred | yes for acceptance, with one corner (below) | constraint types; research-grade proof |
| inferred type of `program(a, b) do a + b done` | `forall a:Numeric. (a, a) -> a` | same | bounded, constraint-qualified |
| runtime cost | one convert per widen | same | one convert per widen, plus copies and closure wrappers |
| proof cost | none (rules unchanged) | none, but the differential test must write `float(e)` at the new sites | a subsumption rule, coercion elaboration theorem, W redone |

For (b), the type of `program(a, b) do a + b done` stays `forall a:Numeric. (a, a) -> a`; what
changes is its **calls**:

```
f = program(a, b) do a + b done
print(f(7 // 2, 2.5))        # today: error.  (b): 5.5; the Int argument is converted at the call.
```

The call instantiates `a` fresh; the two arguments flow `Int ⇒ a` and `Float ⇒ a`; the join is
`Float`; the `Int` side gets `float(...)`. Nothing inside `f` needs a coercion, so `f` is
compiled once per type as today.

#### Where Option 1 still matters under (b)

Widening is never applied under a constructor, so `n = 3  {a: n}` passed to `h` that wants
`{a: Float}` works only because `n` is a generalized literal (Option 1) and can be a `Float` at
that use. A computed `Int`, `{a: 7 // 2}`, still cannot (it would need a rebuilt record).

#### The principality corner

Closing an edge between two free variables by unification loses precision in one case. In
`program(i) do {a: i, b: if c then i else 1.5} done` full subtyping gives `(a) -> {a: a, b: Float}`
and closing gives `(Float) -> {a: Float, b: Float}`. Every call is accepted either way; only a
later use of `f(3).a` where an `Int` is required (a list index) is accepted by one and not the
other. Treat this as the documented limit of "principal for acceptance of calls".

### Error messages

The messages that matter today print both types as `Number` ("expected `Number`, found
`Number`") because `Int` and `Float` share a name. (b) removes most of those mismatches. The
remaining one is `Float ⇒ Int`, and it can say what to do: "this is a `Float` but an `Int` is
needed here; use `round`, `floor` or `truncate`", as `//` does today. A mismatch inside a
structure (`[Int]` where `[Float]` is wanted) is still reported as a type mismatch, and
there the message should name the elements.

### Surprising programs under (b)

- `(i + j) + 1.5` and `i + (j + 1.5)` can differ: the first adds as `Int` (and can trap on
  overflow), the second as `Float` (and rounds). Widening happens at the operator that meets
  the `Float`, not at the leaves.
- Adding `.0` flips a type downstream: `x = if c then 1 else 2.5` makes `x` a `Float` for
  everyone, and then `xs.at(x)` is an error pointing at `round`.
- An `Int` above 2^53 loses low bits when widened (2^24 on the embedded `f32` profile), and
  comparison widens too: `9007199254740993 == 9007199254740992.0` is `true`, yet the two
  `Int`s differ, so `==` across `Int` and `Float` is not transitive. D3 offers an exact
  comparison.
- `{x: i} + {x: 1.5}` is an error while `i + 1.5` works: no widening under a constructor.
- A list literal `[i, 2.5]` becomes a `[Float]`; today it is an unusual cons chain with
  per-element types (section 0, fact 3).

### Prior art

From memory; not re-verified for this pass, and none of it needs to be cited in code.

- **OCaml**: no overloading and no widening: `+` and `+.`, `float_of_int`.
- **Haskell**: `Num` and `fromIntegral`; a numeral is `Num a => a` (goat's `Literal` sort);
  defaulting to `Integer` or `Double`; no implicit `Int`-to-`Double`.
- **Elm**: `number` is a constrained variable (goat's `Numeric`), `Int` and `Float` never
  mix, `toFloat` is explicit. The kinding design in `kinds.rs` is Elm-style already.
- **Swift**: literals are polymorphic; a variable bound to an `Int` expression does not widen:
  `let i = 3; i + 1.5` is an error until `Double(i)`.
- **Julia**: `+` is a generic function with promotion rules (`promote_type(Int, Float64)`),
  resolved at run time by multiple dispatch; no inference problem to solve.
- **Scala / Kotlin**: numeric widening built into the compiler, with local (not global)
  inference. Scala's weak conformance widens `Int` to `Double` at join points: (b) is that rule.
- **MLsub / simple-sub**: annotation-free subtyping inference with principal types; the way to
  do (c) if the owner ever wants it. Heavy for a proof (D1).

## 4. Interactions

- Options 2 and 3 together: `7 // 2.5` widens `7` and gives `2`; `i // 2.5` gives a `Float`.
- Options 1 and 3 together: `n = 3`, then `n + 1.5` and `xs.at(n)` need no `float(e)` on `n`
  at all; each use takes its own type. Widening is used only for a *computed* `Int`.
- The host boundary does not change: a `foreign` function that takes an `Int` still rejects a
  `Float`; one that takes a `Float` accepts an `Int` (ADR 0017).
- The embedded profile: `Int` is `i32`, `Float` is `f32`; widening rounds to `f32`.

## 5. Size, order and dead ends

Sizes are in PR-sized units (a PR a senior engineer lands in a day or two), counting the tests.

| piece | Option 2 (`//`, `%`) | Option 1 (numerals) | Option 3 (b) (widening) |
|---|---|---|---|
| checker | S: retype `type_whole_division` as generic | XS: drop one filter, update `query.rs` printer | L: replace eager `join_operands` and `widen_arguments` with flows plus a post-binding solver; new error text |
| mono / codegen | M: operand-type dispatch; two new float ops | none (rematerialization exists); maybe M for sharing (D6) | S-M: widen branches and list elements (mono re-derives widening from node types at operators and arguments today) |
| runtime (interpreter, wasm, embedded) | M: wasm `fmod` helper is the hard part | none | none |
| proofs: phase 1/2 rules | S-M: a `bin_sig` case, `bin_step` case, progress and preservation cases, examples | none | none |
| proofs: Algorithm W | S: `bin_arg` case; stays incomplete for generic operators | none | none by itself; completeness for `1 + 1.5` is a separate follow-up (ADR 0038 decision 4) |
| differential (Coq-extracted checker vs Rust) | S: re-extract | none | M: write `float(e)` at the new sites in the elaboration check |
| docs | `semantics.md`, ADR amendment | ADR 0017 amendment | `semantics.md` section 4 and 9, new ADR |

Recommended order: Option 2, then Option 1, then Option 3 (b). They are independent, except
that 3 is easier to explain once 1 and 2 have removed the commonest cases. Option 3 is the one
that needs a new ADR (it changes how the checker visits join sites, not what the rules say).

**Dead-end risks**

- **(c), full subtyping, is the dead end.** Records, lists and functions need copies and
  wrappers, break value sharing (ADR 0032, 0035), and need a subsumption rule and a
  coercion-elaboration theorem in the proofs. Do not start it.
- **A type-level `max`** has no principal type (section 3). Do not start it.
- **wasm `fmod`**: if a bit-exact helper proves hard, fall back to a host import (a cost to
  hosts) or to `a - b * floor(a / b)` with a documented range limit. Spike it first.
- **Solver termination and ordering**: the post-binding solver must treat mutually recursive
  groups and `self` records (ADR 0034) as one unit, the way `generalize_members` does. Flows
  that cross a generalization boundary are the likely source of bugs. Mitigation: the solver is
  a pure function of the flow list, so it is unit-testable on its own.
- **Reload and the model contract**: Option 1 generalizes the literals of `init`'s record, and
  the host contract unifies a *fresh instance* of `init` with `update`'s parameter. The spike
  passed every contract test except the sharing one, but the interactive suites are the first
  place to look for a regression.

## 6. Decisions for the owner

Each has options, a goat example, and a recommendation. None is decided here.

**D1. How far does widening go (Option 3)?**
(a) operators only (what the checker does today, made order-independent);
(b) every scalar join site: operators, call arguments, `if`/`match` branches, list elements;
(c) everywhere an `Int` meets a `Float`, structures included.
Example: `f(7 // 2, 2.5)` and `if c then 7 // 2 else 2.5 done` type-check under (b) and (c);
`h({a: 7 // 2})` with `h` wanting `{a: Float}` only under (c).
Recommendation: **(b)**. It keeps HM, needs no rule changes, and has no copies. (c) is a
research project (section 5).

**D2. Do `==`, `<` and the other comparisons widen?**
(a) widen, as `+` does (ADR 0017 decision 4 already says so);
(b) compare exactly: an `Int` and a `Float` compare as the mathematical numbers.
Example: `9007199254740993 == 9007199254740992.0`: `true` under (a), `false` under (b).
Recommendation: **(a)**. It is one rule for every operator; the cost is non-transitive
equality above 2^53, which a kid will not meet. (b) costs a runtime comparison routine.

**D3. What is the result type of `//` on `Float`?**
(a) `Float`, so `7.5 // 2` is `3` as a `Float`;
(b) `Int`, trapping when the value does not fit (as `truncate` does).
Example: `xs.at(x // 2)` with `x = 7.5`: (a) is an error that points at `round`; (b) works.
Recommendation: **(a)**. It makes `//` generic like `+ - *` and keeps `%` and `//` of one
type; a whole `Float` already prints as `3`. Use `floor` for an `Int`.

**D4. How exact is Float `//` and `%`, and what is a zero divisor?**
Rounding: (a) Python's exact floor of the quotient of the two doubles (`1 // 0.1 == 9`);
(b) the naive `floor(a / b)` (`1 // 0.1 == 10`, and `1 % 0.1` then is not what is left over).
Zero divisor: (a) IEEE like `/` (`inf`, `nan`); (b) trap like `Int` `//`.
Example: `7.5 % 0` is `nan` under IEEE and `trap: division by zero` under a trap.
Recommendation: **Python-exact rounding with the IEEE zero divisor.** It matches the ticket's
"as in Python" for the values kids meet, keeps `Float` free of traps (a trap needs a `Float`
trap outcome in the proofs), and is consistent with `1 / 0 == inf`.

**D5. Do `//` and `%` apply to records of numbers, like `+ - *`?**
(a) yes, field by field (they are `Numeric`; zero new proof cost);
(b) scalars only (needs a new `Ordered`-style sort in the proofs, ADR 0038 consequences).
Example: `{x: 7, y: 9} // 2`.
Recommendation: **(a)**, for one rule across the arithmetic operators. Low stakes.

**D6. Option 1 and record sharing: what happens to a record of literals?**
`init = {x: 0, y: 0}` is a syntactic value, so generalizing literals rebuilds it at every use.
(a) accept the rebuild (one allocation per use; breaks the reload sharing test as is);
(b) generalize only a bare numeral binding (`n = 3`, and `m = n`), and keep records of literals
shared as today;
(c) generalize everything, and have mono build one copy per distinct instantiation.
Example: `p = {x: 1, y: 2}`, `p.x + 1.5` and `p.y // 2`: (a) and (c) work in any order; under
(b) it works only through Option 3's deferred join: `p.x` stays one shared literal, which
takes the type the whole program forces, and a widening covers the rest.
Recommendation: **(b)**. Smallest change, no allocation or sharing regression, and Option 3
covers the rest; revisit (c) if kids hit it.

**D7. May a number that was an `Int` only because of `//` become a `Float`?**
Once `//` is generic (D3 (a)), `n = 5  m = n + 1.5  n // 0` has `n` a `Float` and gives `inf`;
today `n` is an `Int` and the division traps. Similarly overflow (`n * 2` above 2^62 traps as
an `Int`, rounds as a `Float`).
(a) accept: the type follows the uses;
(b) make a literal prefer `Int` whenever any use allows it (a defaulting rule that runs
before widening).
Recommendation: **(a)**; under Option 1 the question mostly goes away, since each use picks
its own type.

**D8. Should Option 1 extend to constant arithmetic (`n = 2 * 3`)?**
(a) no: only syntactic values (ADR 0027), the rest stays one number, with Option 3 hiding most
of the asymmetry;
(b) yes: treat arithmetic on numerals and constant names as generalizable. It needs a new
`is_gen_value` case in the proofs and moves a trap (`4e18 * 2`) from the definition to the
use.
Recommendation: **(a)**.

**D9. Do the changes need a new ADR, and which gate label applies?**
Option 1 changes the set of accepted programs but not a rule. The `proof-gate` fails a PR that
touches `checker/src/infer.rs` unless `proofs/` changes or the PR carries `no-semantics-change`
with a reason. The reason "the rules already accept it; this is a completeness fix" is true,
but it is not a wording-only change as ADR 0037 describes the label.
Options: (a) apply the label with that reason; (b) add a `docs/semantics.md` and
`proofs/README.md` note and a `GoatPhase2.v` example that pins the program as derivable, so the
gate is met honestly.
Recommendation: **(b)** (a small example proof is cheap and makes the claim checked), and a
single ADR 0039 covering all three options, amending ADR 0017 decisions 3 and 4 and its
"binding that is not a function" note.

**D10. The embedded profile.** Float `//` and `%` round to `f32`; widening an `Int` above 2^24
loses bits. (a) accept and document; (b) trap on a widening that loses bits (costly).
Recommendation: **(a)**.

## 7. Recommendation

1. **Option 2** first: `//` and `%` generic over `Numeric`, Python-exact, `Float` result, IEEE
   zero divisor (D3, D4, D5). Spike the wasm `fmod` helper before committing.
2. **Option 1** second, restricted to bare numerals (D6 (b)): a one-line checker change, the
   `query.rs` printer fix, and tests; mono already rematerializes.
3. **Option 3 (b)** third: a deferred flow solver at scalar join sites, `float(e)` elaboration,
   no rule changes. Needs its own ADR and a design review of the solver before code.
4. Never (c), never a type-level `max`.
5. One ADR (D9) and a `proofs/` touch in each PR so the gate passes without a waiver.
