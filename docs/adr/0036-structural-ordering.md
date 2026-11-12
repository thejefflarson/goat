# ADR 0036 — `<`, `<=`, `>`, `>=` order any two values of one type that holds no function

- Status: accepted (2026-11-11). Numbered 0036 because a parallel change may
  take 0035.
- Context: ADR 0017 (`Int`/`Float`, mixed comparison widens), ADR 0016 (tag
  groups), the structural `==` in `mir/src/mono/structural.rs`.

## Context

`<` and its three siblings accepted only `Int` and `Float`. `"apple" < "banana"`
was a type error, so `sort`, `biggest`, `smallest` and `insert_sorted` (written
with `<` and `>` in the prelude) worked on numbers alone. Sorting words or
records needs an order on more than numbers.

## Decision

1. **One order, defined by structure** (OCaml's polymorphic compare):
   - numbers by value, with `Int` meeting `Float` widening as before;
   - strings by code point. UTF-8 bytes sort in code point order, so the
     comparison is bytewise, and a prefix comes before the longer string;
   - `Bool`: `false < true`;
   - records field by field in label order (the order the type already keeps),
     the first unequal field decides;
   - tags by label, then by payload left to right. Lists are the tags `Empty`
     and `Link(first, rest)`, so `Empty < Link` gives lexicographic order with
     a prefix first;
   - `Unit` equals itself.
2. **Typing reuses the `Eq` constraint.** `a < b` unifies its operands (an
   `Int` beside a `Float` still widens) and requires the shared type to have no
   function inside it, which is the rule `==` already uses. No annotation is
   needed and inference stays principal: `least = program(a, b) do ... a < b
   ... done` has the type `(a, a) -> a` with `a` constrained, checked wherever
   the function is called, exactly as `==` is. We did not add a separate
   `Comparable` kind because it would accept and reject the same types as `Eq`.
   The `Ordered` kind stays for `/`, which wants plain numbers.
3. **A function inside the operands is a spanned checker error**, with the
   message `can't compare `T` with `<`: it has a function inside` (or `can't
   compare functions with `<``) at the comparison. When the constraint is
   discovered later, at a call of a generic function, the message omits the
   operator because the constraint does not record which operator asked.
4. **Mono derives the order.** For a number, `<` stays one MIR `Cmp`. For any
   other ground type, mono derives a function memoized on the canonical type
   (the mechanism behind structural `==`) that returns an `Int` -1, 0 or 1,
   and the operator tests it against 0. Strings use a derived loop over
   `StrLen` and `StrByte`. The last field of a record, the payload of a tag
   and the rest of a list are tail calls, so ordering a long list uses constant
   stack. The interpreter and wasm run the derived MIR with no new primitive.
5. **Floats inside a larger value.** The three-way test is `==`, then `<`,
   else greater, so a NaN field sorts after everything. A bare `Float < Float`
   keeps IEEE semantics (any comparison with NaN is false).

## Consequences

- The prelude's `sort`, `biggest`, `smallest` and `insert_sorted` work on
  strings, records and lists unchanged.
- A for/repeat loop whose bound is not a number now reports the `+` of the
  counter step (`` `+` needs numbers or records of numbers ``) rather than the
  comparison, because the comparison accepts any ordered type.
- A tag group orders by label (alphabetical), not by declaration order: a row
  in a type holds labels sorted, and the declaration order is not part of
  `Ty`. Ordering by declaration order would need the checker to carry the
  group's order into the type; that is left open.
- The mismatch message for `true < 1` now reads `expected Bool, found Number`
  (the left operand sets the type) rather than blaming the `Bool` as a non-number.

## Deferred

- Declaration order for tag groups.
- A user-defined order (a method that overrides `<`).
