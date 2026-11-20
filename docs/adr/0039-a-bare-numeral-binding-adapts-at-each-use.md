# ADR 0039 — A bare numeral binding adapts at each use

- Status: accepted (2026-11-20)
- Amends: [ADR 0017](0017-int-float-split.md) (the implementation note "a binding
  that is not a function keeps its literals' types shared").
- Context: #496, option 1; `docs/design/numbers-plan.md`.

## Context

ADR 0017 left `n = 3` as one shared number: a use that needed a `Float`
turned `n` into a `Float` for every other use. So `n = 3` followed by
`{a: n + 1.5, b: n // 2}` failed (`//` wants whole numbers and `n` had become a
`Float`), while the same two fields written in the other order type-checked,
because the checker visited `n // 2` first. One program had two answers,
depending on source order.

The calculus already generalizes the binding: `T-Let` quantifies a syntactic
value's variables with their sorts, and `T-Num` types a numeral at any
`Literal` type (`docs/semantics.md` section 5). The checker was the one that
disagreed.

## Decision

1. **A `=` binding whose value is a bare numeral generalizes.** `n = 3` has the
   scheme `forall a:Literal. a`; each use instantiates a fresh variable that
   settles on its own, as `Int` unless its context needs a `Float`. Mono already
   rematerializes a generalized value at each use's type (#376), so no mono or
   codegen change is needed.
2. **Only a bare numeral**, which includes a negated one: `-3` lowers to
   `0 - 3`, and a kid reads it as one number, so `n = -3` adapts. The checker
   recognizes `0 - e` of a numeral at any depth (a hand-written `0 - 3` is the
   same term, so it adapts too). The calculus treats `0 - 3` as a computation, so
   the differential corpus skips a `let` of one. A record or list of literals stays one shared value
   with its literals' types shared, so the reload snapshot keeps its sharing
   ([ADR 0035](0035-reload-keeps-data-and-rebinds-methods.md)) and a record is not
   rebuilt at every use.
3. **Only a syntactic value** ([ADR 0027](0027-rank1-hm-inference-ceiling.md)).
   `n = 2 * 3` is a computation, so it stays one monomorphic number.
4. **The type follows the uses.** `n` is an `Int` at a use that needs no
   `Float`, and a `Float` at one that does. Two visible consequences, both
   accepted:
   - Overflow. `n = 4611686018427387904` with `a = n + 1.5` and `b = n * 2`: `b`
     was `9.22e18` and now traps (`this number got too big`), because that use
     of `n` is an `Int`.
   - A zero divisor. `n // 0` traps where `n` is an `Int` use. When `//` takes
     `Float` operands, the same `n` may be a `Float` there and give `inf`.
5. **Proofs.** The rules need no change. `GoatPhase1.v` gains
   `numeral_binding_adapts_in_one_record`, which checks that the rules accept
   `n = 3 {a: n + 1.5, b: n * 2}` with `n` a `Float` in one field and an `Int`
   in the other. The differential corpus no longer skips a bare numeral `let`; a
   record or a name holding a numeral is still skipped, because the checker
   does not generalize those.

## Consequences

- The ticket's example type-checks in either field order.
- The editor shows a generalized numeral as `Number`, not as a type variable.
- `a_record_held_in_two_places_is_rebuilt_once` keeps passing: records are
  untouched.
