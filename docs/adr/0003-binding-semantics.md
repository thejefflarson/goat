# ADR 0003 — Binding semantics: functions recurse as a group, values shadow

- Status: accepted (2026-11-01)
- Context: Phase 0 / name resolution, `docs/plan.md`

## Context

`name = value  rest` is goat's only binding form. Two requirements pull in
opposite directions:

- A function must see its own name so it can recurse (`fib`), and two functions
  must see each other so they can be mutually recursive (`is_even`/`is_odd`) —
  ideally with no ceremony and no ordering constraint.
- A value binding should let a kid write `score = score + 1`, meaning "a new
  `score` from the old one" (shadowing), not a meaningless self-reference.

These cannot both hold for one namespace: if every name is visible everywhere in
a scope (needed for order-free mutual recursion), then `score + 1` on the
right of `score = …` is ambiguous. ML resolves this with an explicit
`let rec … and …`; Haskell makes every group recursive and has no sequential
`let`. Rust keeps two namespaces: `fn` items are an order-free recursive group,
`let` is sequential with shadowing. We take Rust's split.

## Decision

- A binding is **recursive exactly when its value is a `program(...)` literal.**
- **All function bindings in a scope form one mutually-recursive group:** the
  names are bound before any of their bodies are resolved, so functions may call
  each other (and themselves) regardless of definition order, with no keyword.
- **Value bindings are sequential and shadow:** a non-function binding's value
  is resolved in the enclosing scope, so `x = x + 1` reads the previous `x`.
- A function body sees every function in its scope, plus the value bindings in
  effect where its group begins — **not** value bindings introduced later in the
  scope. Name resolution stays static.

## Consequences

- `fib` (self-recursion) and `is_even`/`is_odd` (mutual recursion) work with no
  ceremony and no ordering constraint.
- `score = 1  score = score + 1  score` evaluates to 2 (shadowing). A kid's
  imperative-looking update does the intuitive thing.
- `score = score + 1` with no earlier `score`, and a self-referential value like
  `ones = Link(1, ones)`, are plain `unknown name` errors — honest, since goat
  is strict and cannot build such a value anyway.
- This **replaces** the plan's Phase-0 item "reject recursive bindings whose
  value is not a `program(...)`": under these semantics such a binding is not
  recursive, so there is nothing to reject — it shadows or is an unbound name.
- Lowering does a per-scope pre-pass binding the `program`-valued names before
  resolving bodies; value bindings are still lowered in order.
- Strengthens ADR 0002's no-cycle story: a value binding cannot name itself, so
  reference cycles in data are unconstructable; only functions self-reference,
  and (Phase 4) a closure references its binding via `env`, never storing itself.
- Out of scope: cross-scope mutual recursion and recursive *values* (lazy
  `letrec` over data) remain unsupported.
