# ADR 0014 — Turtle builtins are global prelude names; the host caps a run at a million commands

- Status: accepted (2026-11-07)
- Context: Phase 8.5 (P85c headless SVG turtle), `docs/plan.md` ("turtle"),
  ADR 0003 (binding semantics: values shadow), ADR 0009 (strings are immortal
  literals), ADR 0012 (`trap` is a halting builtin, shadowed by a user binding);
  ratified while integrating #164 (closes #100). `prelude/turtle.goat`,
  `cli/src/turtle.rs`.

## Context

The turtle is the Phase 8.5/9 payoff: a kid writes `forward(100); right(90)` and
gets a drawing. P85c names the seven turtle actions as `foreign` declarations in
`prelude/turtle.goat` (`forward`/`back`/`left`/`right` as `Number -> Unit`,
`pen_up`/`pen_down` as `() -> Unit`, `color` as `String -> Unit`) and concatenates
that file into `checker::PRELUDE`. Two choices in that work are expensive to
reverse once programs and examples depend on them, so they are recorded here.

1. **Where the turtle names live.** goat has no module system — `import`,
   namespaces, and selective exposure are Phase 10+ (`docs/plan.md`). The only
   mechanism for a name every program can see is the prelude, which ADR 0012
   already uses for `trap` and P8d uses for the list stdlib. Putting the turtle
   behind a module that does not exist would block the Phase 8.5/9 payoff on
   Phase 10.

2. **How much a single run may draw.** `TurtleHost` records every turtle call
   into a `Vec<Command>` before replaying the log into an SVG. A program that
   loops forever calling `forward` would grow that vector until the host runs out
   of memory. The turtle is aimed at kids, who write infinite loops by accident.

## Decision

### Turtle builtins are ordinary, immortal, global prelude bindings

The seven turtle names are plain prelude `foreign` bindings, in scope in every
program, on the same footing as `first`/`length`/`trap`.

- **Shadowing preserves escape.** By ADR 0003 a value binding shadows, so a user
  who writes `forward = 7` or `color = program(c) do ... done` gets their own
  binding (with the ordinary shadowing warning), exactly as a user `trap` wins
  under ADR 0012. Nothing is stolen from the kid's namespace permanently; the
  global name is a default, not a reservation.
- **Unused turtle names cost nothing.** As with the rest of the prelude, mono
  only emits what the program reaches (`prelude/prelude.goat` header), so a
  program that never calls the turtle compiles to a module with no turtle import
  and runs unchanged under `NoHost`. Verified by the prelude round-trip test,
  which asserts non-turtle examples behave identically with the prelude around
  them.
- **The precedent is deliberate.** Immortal prelude declarations are how goat
  already ships a standard library (ADR 0012, P8d lists). The turtle adds host
  `foreign` decls to that same surface; it does not invent a second mechanism.

This is a bridge, not a permanent namespace decision. When a module system lands
(Phase 10), `forward`/`color`/… can move behind `turtle.forward` /
`import turtle` and the global prelude names can be deprecated without changing
the host or the SVG backend — the `foreign "turtle" "..."` wiring already carries
the module name `"turtle"`, so namespacing is a front-end change. Recorded as the
reversible follow-up, not a regret.

### A run is capped at 1,000,000 turtle commands

`TurtleHost::call` refuses the call once `commands.len() >= MAX_COMMANDS`
(1,000,000), returning a host `Err` that traps the program. This is ratified as a
denial-of-service guard on host memory, not a limit on any honest drawing: a
million line segments is far past anything a kid draws, and the constant is a
one-line change if a real program ever needs more.

## Consequences

- The turtle works today, with no module system, and reads the way a kid expects:
  `forward(100)`, not `turtle.forward(100)`.
- A user binding named after a turtle action shadows it and warns; the program
  still type-checks and runs. No turtle name is reserved against the user.
- A runaway loop that spams turtle commands halts as a trap
  (`the turtle drew more than 1000000 commands`) instead of exhausting memory.
  Like every `TurtleHost` refusal (a non-finite `forward`, a malformed `color`),
  this is a runtime host `Err` surfaced as a `trap:`, not a checker error — the
  "errors come only from the checker" invariant (`CLAUDE.md`) is about well-typed
  programs reaching the backend, which these do; the host refusing a value at run
  time is the same class as `trap` or `first([])`.
- A future module system (Phase 10) can namespace these names and deprecate the
  globals without touching the host or the SVG renderer, because the module name
  `"turtle"` already travels with each `foreign` declaration.
