# ADR 0012 — `trap` is a halting builtin: a literal-only message, a bottom type, checker-guarded

- Status: accepted (2026-11-04)
- Context: Phase 8 (P8d prelude stdlib), ADR 0005 (out-of-scope feature diagnostics),
  `docs/plan.md` ("Prelude"); ratified while integrating #155 (closes #96). The MIR
  `Expr::Trap` node predates this decision.

## Context

The pure-goat prelude (`prelude/prelude.goat`) needs to stop a program when a
partial function is misused — `first`/`rest`/`item`/`biggest`/`smallest` of an
empty or out-of-range list. goat had no way to halt:

- A `match` without `else` closes the row, so `match xs do [h, ...t] then h done`
  would make the checker *reject* any caller whose list could be `Empty`, rather
  than failing at run time on the empty case. That is the wrong semantics for a
  kid-facing `first` that should type as `List(a) -> a`.
- `1 / 0` is `inf`, not a halt.

So the prelude needs a primitive that (a) halts at run time and (b) types as
anything, so it can sit in either arm of a `match` or `if` without constraining
the result type.

## Decision

Add a compiler builtin `trap`, ratified as a permanent language primitive.

- **Surface.** `trap("message")` takes exactly one argument, which must be a
  string *literal*. `Builtin::named("trap")` resolves the bare name only when it
  is not shadowed by a user binding, so a user `trap = program(...)` wins (with
  the ordinary shadowing warning). This keeps `trap` out of the way of a name a
  kid might pick.
- **Type.** `trap(...)` types as a fresh type variable — a bottom that unifies
  with any expected type. This is what lets `[] then trap("...")` sit opposite
  `[h, ...t] then h` without forcing the arms to agree on anything but the
  non-trap arm's type.
- **Lowering.** `trap("m")` lowers to `ExprKind::Trap(String)` in the checker HIR,
  which mono lowers to the pre-existing MIR `Expr::Trap`. No new MIR, wasm, or CLI
  runtime node was added — `trap` reuses machinery already there.

### Soundness: the checker is the only source of errors

The repo invariant is that a user never sees an error from mono/MIR/codegen; those
failing is an internal compiler bug (`CLAUDE.md`). `trap` keeps that invariant:

- A bare `trap` (the builtin not applied to arguments) is a spanned checker error
  in inference (`` `trap` stops the program, so call it with a message ``).
- A `trap` call whose argument is missing, non-literal, or multiple is a spanned
  checker error in lowering (`` `trap` takes one message, written out in quotes ``).

So on any program that type-checks, the only `trap`-shaped node reaching mono is
`ExprKind::Trap(String)`. mono's `unreachable!("the checker rejects a bare trap")`
for `Builtin::Trap` is therefore dead on well-typed input — guarded, not a panic a
user can trigger.

## Consequences

- goat gains a halt primitive with a one-line prelude cost and no new backend node.
  The prelude's partial functions can type as total (`List(a) -> a`) and fail at
  run time, which is the behavior a kid expects.
- **Run-time blame is incomplete, and that is a known, tracked gap.** Neither
  backend carries a source span at run time. The interpreter reports the message
  (`first of an empty list`); wasm emits a bare `unreachable`, so `goat run` shows
  `trap:` with no text and loses lines printed before the trap. `at_call_site`
  re-blames only checker errors, so a runtime trap is not yet pointed at the user's
  call site. Fixing this (a `goat.trap` host import carrying the message, a
  trap-site → call-site source map, and flushing printed output before the trap) is
  #156, to land with the Phase 8.5/9 turtle runtime. This is a UX gap, not a
  soundness one: the interp==wasm differential oracle asserts that the program
  traps, not the wasm message text.
- A literal-only message means `trap` cannot interpolate a computed value (e.g. the
  out-of-range index). Accepted for now: goat has no run-time string construction
  (strings are immortal literals), so a computed message is not expressible anyway.
  Revisit when string construction lands.
