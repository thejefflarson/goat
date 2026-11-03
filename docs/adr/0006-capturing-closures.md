# ADR 0006 — Capturing closures: representation and calling convention

- Status: accepted (2026-11-02)
- Context: Phase 4 (closures), `docs/plan.md`, `docs/mir.md`, extends ADR 0004

## Context

ADR 0004 shipped function *values* as zero-capture static immortal closures:
a top-level function used as a value becomes a `MakeClosure` of a wrapper with
no captures, and a function-typed parameter is called via `CallClosure`. Phase 4
adds the missing case — a `program(...)` that **captures** a variable from an
enclosing scope, and anonymous `program(...)` literals that are not bound to a
name. The checker already types these (capture is a non-issue for
Hindley-Milner: the inner body is inferred with the outer scope still in the
environment). The MIR node set (`MakeClosure(f, captures)`, `Capture(i)`), the
reference interpreter, the verifier, and the wasm backend already model and
emit **non-empty** capture lists. Only mono still rejects captures and
anonymous literals (ADR 0005 "not supported yet"). This ADR records how mono
closes that gap.

## Decision

- A `program(...)` whose free variables include a binding from an enclosing
  scope is materialized as a **general heap closure**
  `[header][drop_fn: i32][code: i32][captures...]` via `MakeClosure(f, captures)`
  and called through `CallClosure` / `call_indirect`. All closures of one goat
  function type share the signature `(env: i32, args...) -> ret`.
- **Capture set** = a literal's free variables, minus its own self-binding,
  minus top-level functions. Top-level functions are re-materialized in place
  (a `CallDirect`, or a static immortal closure in value position) and are
  never captured, so a top-level function's only free names are other globals
  and it never becomes a heap closure. Only nested `program`s capture.
- **Zero-capture function values keep ADR 0004 behavior**: a static immortal
  closure (`rc = u32::MAX`, `drop_fn = Noop`) and `CallDirect` for known
  top-level callees. The `CallDirect` shortcut is **gated on an empty capture
  set** — a nested capturing callee, including a recursive self-call, must be
  materialized and invoked via `CallClosure`.
- **Self-reference of a capturing closure compiles to the current `env`**, never
  a stored capture — the closure never holds a pointer to itself. A recursive
  capturing closure self-calls through `env`
  (`CallClosure` / `TailCall(Callee::Closure(env))`), because the env is the
  only live handle to its captures. This is the ADR 0003 self-reference rule
  applied to the calling convention; `Let` binds one name, so only
  self-recursion exists and no closure ever stores another that stores it.
- **Anonymous literals are lambda-lifted** and specialized per
  `(lexical identity, ground type)`, so each gets one ordered capture list per
  specialization, threaded to both the `Env.captures` types and every
  `MakeClosure` site so capture indices line up.
- The **Roc lambda-set / defunctionalization optimization** (compiling a
  closure whose targets are statically known as tagged data, with no heap
  allocation and no indirect call) is **out of scope this phase**. The general
  heap-closure path is the deliverable; `MakeClosure` / `CallClosure` are
  abstract enough to add defunctionalization later without an IR change, as a
  measured-need follow-up.

## Consequences

- The entire change is in `mir/src/mono.rs`: free-variable computation, capture
  bookkeeping, lambda-lifting anonymous literals, generalizing the zero-capture
  wrapper path to emit real captures, and gating `CallDirect` on an empty
  capture set. No change to `mir.rs`, `interp.rs`, `verify.rs`, or the wasm
  backend, which already handle non-empty captures.
- This removes the mono capture and anonymous-literal "not supported yet"
  diagnostics (ADR 0005), as 0005 anticipated.
- Closure env *lifetime* — when the heap block is freed — is ADR 0007.
