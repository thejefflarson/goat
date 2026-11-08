# ADR 0019 — On-device wasm runtime: start on WAMR, keep tail calls in the feature floor

- Status: proposed (2026-11-08)
- Context: Phase 12 (`docs/plan.md` "Microcontrollers"), #232 (this decision);
  gateway for the board work #115/#117/#118/#119 and the speculative #114
  (on-device runtime, interpreter → AOT) and #116 (embedded constraints: `f32`,
  pooled heap budget, bounded stack). Builds on ADR 0013 (loops lower to
  tail-position recursion; MIR has no loop node), ADR 0006 (capturing closures),
  ADR 0015 (the host owns the loop; the microcontroller is just another host of
  the same init/update/draw contract), ADR 0017 (the i32/f32 embedded profile,
  already landed via #235), and ADR 0018 (one Rust conformance suite, a thin
  driver per host). Interacts with #223 (operator/boolean-chain eval and wasm
  lowering are still recursive — a tight native-stack margin). Recorded before
  any board bring-up.

A term used throughout: a **tail call** is a call in the last position of a
function — its result *is* the caller's result, so the caller's stack frame can
be discarded before the callee runs and a chain of them runs in constant stack.
**AOT** here means *ahead-of-time compilation*: turning the `.wasm` into native
code (or into C that the board's compiler turns into native code) off-device, so
the board loads machine code rather than interpreting bytecode.

## Context

Phase 12 reaches microcontrollers only through wasm (Cranelift has no 32-bit ARM,
Xtensa, or riscv32 backend; `docs/plan.md`). So the board runs a wasm **runtime**,
and three things must be decided before bring-up: which interpreter runs a `.wasm`
at load time, which AOT path gives speed when the interpreter is too slow, and the
**wasm feature floor** — the set of proposals a goat-emitted module is allowed to
require. The floor is the sharp one, because of a fact about goat's own codegen.

**goat emits tail calls, and they are load-bearing.** ADR 0013 decided that goat
has *no loop node*: `repeat n times`, `for i from a to b`, and `for x in xs` all
lower, in the checker, to a local self-recursive function whose recursive call is
in tail position — "the tail call is the jump" (`checker/src/lower.rs`). The MIR
interpreter runs those in constant stack via a trampoline (`Flow::Tail`,
`mir/src/interp.rs`), and the wasm backend lowers `Expr::TailCall` to the
tail-call proposal's `return_call` / `return_call_indirect` (`wasm/src/lib.rs`),
with `wasm_tail_call(true)` set on every wasmtime config the project builds
(`goat/src/native/mod.rs`, `cli/tests/allocator.rs`). So tail calls are the
implementation of **all iteration in the language**, plus user self- and mutual
recursion — which, with no `while`/`for` primitive, is goat's *only* looping
construct. This is not an incidental optimization we could drop; it is how a kid's
`repeat` runs.

One sharper detail decides how expensive dropping them would be: a loop that
references any outer binding — `step` in `repeat n times do forward(step) done` —
becomes a **closure** (ADR 0006), so its self-tail-call lowers to the *indirect*
form, `return_call_indirect`, whose target is a function-table index discovered at
run time. The common loop is therefore an indirect tail call, not a direct one.

Several embedded wasm runtimes do not enable the tail-call proposal by default,
and one candidate does not document it at all. So either goat constrains its
runtime choice to engines that run tail calls, or goat changes codegen to stop
emitting them — and that second path is costly for exactly the reason above.

## Decision

### 1. On-device interpreter: WAMR fast-interpreter (wasm3 the fallback)

The interpreter choice:

| Runtime | Kind | Footprint (Cortex-M4F core VM) | Tail calls (guest `return_call`) | AOT path | ESP32 / RP2040 | Maintenance |
|---|---|---|---|---|---|---|
| **WAMR** | classic + fast interpreter, AOT, LLVM JIT | fast-interp ~59 KB, classic ~56 KB, AOT runtime ~29 KB (figures **already include** tail-call) | **Yes** — `WAMR_BUILD_TAIL_CALL=1` (default off); supported in classic-interp, fast-interp, AOT, and LLVM-JIT | **Yes**, same project (wamrc) | ESP32 first-party (Espressif component/fork); RP2040 via bare-metal builds | Active (Bytecode Alliance + Espressif) |
| **wasm3** | fast interpreter only | tens of KB; among the smallest | **Listed "Ready"** on main | **No** — interpreter only | Broad MCU matrix incl. ESP32/RP2040 | **Minimal-maintenance** — no new feature work, PRs reviewed/merged only |

Both run goat's tail calls today. The deciding differences are the AOT path and
maintenance: WAMR carries the interpreter *and* the AOT compiler under one
actively-maintained, ESP32-first dependency, so the Phase-12 "start with an
interpreter, add AOT" plan graduates without changing runtime vendor or
re-validating the tail-call story. wasm3 is smaller and famously fast, but it is
an interpreter with no AOT and is now in minimal-maintenance mode — a dependency
that will betray you later is one to keep off the critical path (Mickens). Keep
wasm3 as a named fallback for a board too small for WAMR, not as the default.

The tail-call flag's marginal cost is already folded into WAMR's published
Cortex-M4F figures above, so "keep tail calls" does not widen the footprint we
were going to ship anyway.

### 2. AOT path: WAMR AOT first; wasm→C (wasm2c / w2c2) only for a locked image

Two AOT shapes, for different needs:

- **WAMR AOT** — compile `.wasm` → `.aot` off-device with `wamrc` (LLVM-based),
  flash the `.aot` beside the ~29 KB on-device AOT runtime. Near-native speed;
  tail calls supported in AOT mode under the **same** `WAMR_BUILD_TAIL_CALL`
  flag; same project as the interpreter, so interp→AOT is a graduation, not a
  second vendor. This is the default speed path.
- **wasm→C (`wasm2c` / `w2c2`)** — translate `.wasm` → C off-device, compile with
  the board's own C toolchain (arm-gcc, xtensa-gcc), link into one firmware image.
  Smallest possible runtime overhead and a single statically-linked image; the
  right tool for a certification / locked-image scenario or a board WAMR cannot
  target. **Three costs** make it a deferred fallback, not the default:
  1. **Tail-call-in-C is not free.** Standard C guarantees no tail-call
     optimization. A `return_call` that must run in constant stack needs
     `[[clang::musttail]]` (Clang only) or a trampoline the translator emits; the
     Xtensa/ARM **GCC** toolchains these boards ship do not guarantee it. So
     goat's tail calls bite the wasm→C path *differently* from the interpreters —
     the translator accepting the opcode is necessary but not sufficient.
  2. **Support is unverified.** w2c2's documentation lists WebAssembly 2.0,
     extended-const, threads, SIMD, and WASI — but **not** tail calls; wabt's
     `wasm2c` tail-call support in generated C is unconfirmed. Either must be
     verified before a board plan depends on it.
  3. **Heavier iteration loop.** A full C compile per program cuts against
     live-coding-over-serial (Phase 12), where loading a `.wasm`/`.aot` is the
     fast path.

When each makes sense: **interpreter first** (load a `.wasm` at run time, fast
iteration, live coding, tens of KB), **WAMR AOT** when a program needs speed the
interpreter can't give, **wasm→C** only for the locked-image / unreachable-board
case above. WAMR gives the first two under one roof.

### 3. The feature floor is MVP + the tail-call proposal — we keep tail calls

The floor goat's emitted modules may require is **the WebAssembly MVP plus the
tail-call proposal**. Concretely: every host — browser, wasmtime, the Apple
shell, and the microcontroller — must run `return_call` / `return_call_indirect`.
The three real options and their costs:

**(a) Pick a runtime that supports tail calls — recommended.** Cost: constrains
§1/§2 to WAMR (flag on) or wasm3 (maintenance-mode), and excludes any runtime
whose tail-call support is unverified (w2c2 today) until it is confirmed. **Zero
codegen cost** — goat emits exactly what it emits now, and the browser/wasmtime
paths are unchanged. Available today.

**(b) Add a no-tail-call codegen variant in `goat_wasm` — rejected as default, a
real and large cost.** You cannot simply "stop emitting `return_call`": by ADR
0013 that makes *every loop* recurse once per iteration and consume native stack
proportional to the iteration count. ADR 0014 caps a turtle run at 1,000,000
commands, so a legitimate kid program would want on the order of 10⁵–10⁶ native
frames — fatal on #116's bounded MCU stack, the exact budget this work exists to
protect. To actually drop tail calls you must do one of:
  - **(i) Add a real loop/iteration node to MIR** and re-lower `repeat`/`for` to
    it. This *reverses* ADR 0013's deliberate "no Loop node" decision and touches
    lowering, mono, rc, verify, the interpreter, and wasm emit — and it still
    leaves genuine user tail recursion *and all mutual recursion* stack-bound,
    because those aren't loops.
  - **(ii) Emit a runtime trampoline in wasm** — a tail call returns a
    "call-target + args" sentinel and a driver loop re-dispatches. This handles
    the general case, including the `return_call_indirect` closure loops that are
    the common case, but it adds per-call overhead and complexity to the hot path
    and to the ABI the hosts depend on.

Either way it **compounds the two tickets it is meant to serve**: #223 (operator-
and boolean-chain eval and wasm lowering are still recursive, sitting ~5% under
the 2 MB test-thread stack) and #116 (bounded stack) — dropping native tail calls
*deepens* the runtime stack exactly where the margin is already thin. Net: option
(b) is a multi-pass compiler change plus either an ADR-0013 reversal or a hot-path
trampoline, and it degrades the embedded stack story it was supposed to improve.

**(c) Hybrid — emit tail calls only where they don't blow the stack — a future
optimization, not a floor.** Recognize *direct* self-tail-recursion and emit a
wasm `loop` block (a local jump, no `return_call`); keep `return_call` /
`return_call_indirect` for mutual and closure/indirect tail calls. The limit is
the Context's sharp detail: the common loop captures an outer binding, so it is a
closure and lowers to `return_call_indirect`, whose target is a runtime table
index the `loop`-block trick can't convert without closure-self-recursion
analysis; and mutual recursion can't become a single `loop` at all. So (c)
*reduces* how many `return_call`s we emit — a legitimate size/portability win —
but does **not** remove the runtime's tail-call requirement. It is a lever to pull
later, not a way to reach a zero-tail-call floor.

### Recommendation

Set the floor at **MVP + tail-call** and keep goat's codegen unchanged (option
a). Start Phase 12 on the **WAMR fast-interpreter with `WAMR_BUILD_TAIL_CALL=1`**;
graduate to **WAMR AOT** (same flag, same runtime, ~29 KB) when a program needs
the speed. Defer the wasm→C path to a locked-image or unreachable-board need, and
verify its tail-call story (cost 2 above) before depending on it. Hold (c) as a
future size optimization; reject (b) as the default because ADR 0013 makes tail
calls the implementation of every loop, so removing them is a language-level
change, not a backend flag.

The rationale in one line each: it is the only option with **no codegen change**;
it carries **both** the interpreter-first and the AOT-speed path under **one**
actively-maintained, ESP32-first dependency; and it keeps the embedded stack
budget honest (native tail calls = constant stack) instead of fighting it. The
trusted surface stays small — one runtime vendor, one build flag, no new hot-path
trampoline to reason about.

### 4. Coherence with the contract (ADR 0015), the profile (ADR 0017), and testing (ADR 0018)

- **ADR 0015 — same contract, new transport.** The microcontroller is just
  another host of the init/update/draw contract. The on-device runtime is the
  transport beneath it: it provides the host imports (the GPIO/LED/sensor/serial
  API of Phase 12 #755 in place of the browser's `scene.*`) and calls
  `goat_setup` / `goat_update` / `goat_draw`. ADR 0015 §5 already built the
  mechanism an MCU needs for bounded update time — a compiler-injected mutable
  `goat_fuel` global, spent at every function entry, that traps a runaway update
  in bounded steps; ADR 0015 names this "the portable mechanism a microcontroller
  host would use," so the MCU host refills fuel per event exactly as the browser
  does, with no new machinery. (ADR 0015's current "not yet supported:
  interactive programs on the embedded profile" — event exports take `Float`
  payloads at the program's width — is board work near #117, not this ADR.)
- **ADR 0017 — the embedded profile.** The i32 `Int` / f32 `Float` profile
  (chosen because the RP2040 has no FPU and the ESP32 is single-precision) is
  already landed (#235). This ADR picks the *runtime* that executes that
  profile's modules on-device. Keeping tail calls costs nothing extra on the
  embedded profile: `return_call_indirect` is width-agnostic.
- **ADR 0018 — one suite, a thin driver per host.** The on-device runtime becomes
  a new **driver** over the existing Rust conformance cases — a WAMR embedding
  driver that runs the shared `(source, expected observable outcome)` cases and
  asserts the same prints/scene-calls/traps/`live == 0` the CLI asserts — not a
  new hand-written suite. wasmtime already proves the tail-call lowering; the WAMR
  driver proves those same cases run on-device with the flag on.

## Consequences

- goat ships to boards with its codegen unchanged; the browser, wasmtime, and
  Apple paths are untouched. The embedded footprint is WAMR's published figures,
  which already include tail-call.
- The dependency surface is one runtime vendor and one build flag. The interp→AOT
  graduation is internal to that vendor.
- The feature floor is now explicit for *every* host: a new host that cannot run
  the tail-call proposal is out of scope until it can, rather than silently
  forcing a codegen rewrite.
- A later board may still want the wasm→C path; this ADR leaves it open as a
  fallback with a named precondition (verify tail-call-in-C), not a closed door.

### Reversible (not one-way doors)

- **Which runtime.** WAMR vs wasm3 vs a future engine is a *driver* swap behind
  ADR 0018's thin-driver boundary — a host change, not a language change.
- **The interp→AOT graduation**, and the per-board build/flash mechanics (#115).
- **The hybrid (c) codegen optimization** — it can land later purely as a size
  win, because it only *reduces* emitted `return_call`s within a floor that still
  permits them.
- **Adding the wasm→C path** later for a board WAMR can't reach.

### One-way door

The genuine one-way door is **the feature floor itself** — whether goat's emitted
modules are allowed to require the tail-call proposal. Every host and every
program compiled so far assumes tail calls; lowering the floor to "no tail calls"
later is the ADR-0013 reversal of option (b) and would have to hold for *all*
hosts at once. So the floor is the expensive-to-reverse decision, and the
recommendation is to set it at MVP + tail-call and keep it there.

## Open questions for a recorded decision

This ADR is **proposed**, not accepted; three points want the author's ratify or
redirect, and each becomes a recorded decision on acceptance:

1. **The tail-call floor (a / b / c).** Recommended: (a), keep tail calls. This is
   the load-bearing choice; everything else follows from it.
2. **Single runtime vendor (WAMR) vs keeping wasm3 as a tiny-footprint fallback.**
   Recommended: WAMR default, wasm3 named fallback — weighed against wasm3's
   minimal-maintenance status.
3. **The wasm→C tail-call unknown.** w2c2 doesn't document tail calls, wabt
   `wasm2c` is unconfirmed, and C has no guaranteed TCO. This is a genuine unknown
   to resolve *before* any board plan chooses the wasm→C path.

## References (external, as of 2026-11)

- WAMR `WAMR_BUILD_TAIL_CALL=1/0, default off … Supported in classic-interpreter,
  fast-interpreter, AOT and LLVM JIT modes` — `doc/build_wamr.md`; Cortex-M4F
  core-VM footprints (tail-call/bulk/shared enabled) — project README.
- wasm3 — "Tail call" listed *Ready* on the main README; project stated to be in
  a minimal-maintenance phase.
- w2c2 README — lists WebAssembly 2.0, extended-const, threads, SIMD, WASI; no
  tail-call entry.
- C tail calls — no standard guarantee; `[[clang::musttail]]` is Clang-specific.
