# ADR 0019 — Embedded strategy: WAMR on-device now, native host-compilation later

- Status: accepted (2026-11-08)
- Decision: a **two-phase embedded strategy**. Phase A (near-term) runs goat on a
  board through an on-device wasm runtime, **WAMR**, reusing the existing wasm
  backend to get boards running now. Phase B (endgame) replaces the on-device
  runtime with **native host-compilation** — goat compiled on the developer's
  machine straight to a native board binary, with no wasm runtime on the device —
  and this ADR records the migration plan and the one hard problem it must solve.
- Context: Phase 12 (`docs/plan.md` "Microcontrollers"), #232 (this decision);
  gateway for the board work — #114 (on-device runtime, interpreter → AOT), #115
  (off-device compile + flashing), #116 (embedded constraints: `f32`, pooled heap
  budget, bounded stack), #117 (embedded host API: GPIO, timers, LEDs, sensors,
  serial), #118 (embedded event model + interrupt queue), #119 (live coding over
  serial). Builds on ADR 0013 (loops lower to tail-position recursion; MIR has no
  loop node), ADR 0006 (capturing closures), ADR 0015 (the host owns the loop; the
  board is just another host of the same init/update/draw contract), ADR 0017 (the
  i32/f32 embedded profile, landed via #235), ADR 0018 (one Rust conformance suite,
  a thin driver per host), and ADR 0021 (the host owns preemption; goat emits no
  fuel). ADR 0021 §3 anticipated this reframe: it recorded that on-device wasm is
  "at most an intermediate step toward the embedded target," with the endgame being
  native host-compilation — this ADR is where that two-phase plan lives. Recorded
  before any board bring-up.

Three terms used throughout. A **tail call** is a call in the last position of a
function — its result *is* the caller's result, so the caller's stack frame can be
discarded before the callee runs, and a chain of them runs in constant stack.
**AOT** means *ahead-of-time compilation*: turning a `.wasm` into native code (or
into C that the board's compiler turns into native code) off-device, so the board
loads machine code rather than interpreting bytecode. **Native host-compilation**
means goat compiles a program on the developer's machine (the *host*) straight to a
native binary for the target board, which is flashed and run with **no wasm runtime
on the device** — no interpreter and no on-device AOT loader.

## Context

Phase 12 reaches microcontrollers only through wasm at first: Cranelift, goat's
desktop code generator, has no 32-bit ARM, Xtensa, or riscv32 backend
(`docs/plan.md`), so a board cannot run Cranelift output. The reachable near-term
path is therefore to emit a `.wasm` — which goat already does for every other host
— and run it on-device under a wasm **runtime** (an interpreter, or an AOT loader).
That is Phase A, and it is attractive precisely because it reuses the backend goat
ships today: a board becomes "just another host" of ADR 0015's contract with no new
code generator.

But a wasm runtime on a microcontroller is a cost — flash, RAM, and interpreter
overhead on a part with little of each — that the near-term convenience justifies
and the endgame should not keep paying. The endgame the user has chosen is **native
host-compilation**: compile each goat program on the developer's machine to a native
board binary and flash that, with no runtime on the device at all. Phase A gets
boards running by the cheapest route; Phase B removes the runtime once the board
story is proven. This ADR records both, and the migration between them.

**One fact about goat's codegen shapes every phase: goat emits tail calls, and they
are load-bearing.** ADR 0013 decided that goat has *no loop node*: `repeat n times`,
`for i from a to b`, and `for x in xs` all lower, in the checker, to a local
self-recursive function whose recursive call is in tail position — "the tail call is
the jump" (`checker/src/lower.rs`). The MIR interpreter runs those in constant stack
via a trampoline (`Flow::Tail`, `mir/src/interp.rs`), and the wasm backend lowers
`Expr::TailCall` to the tail-call proposal's `return_call` / `return_call_indirect`
(`wasm/src/lib.rs`). So tail calls are the implementation of **all iteration in the
language**, plus user self- and mutual recursion — goat's only looping construct.
This is not an incidental optimization to drop; it is how a kid's `repeat` runs.

One sharper detail decides how expensive it is to lower those loops on a target that
does not guarantee constant-stack tail calls: a loop that references any outer
binding — `step` in `repeat n times do forward(step) done` — becomes a **closure**
(ADR 0006), so its self-tail-call lowers to the *indirect* form,
`return_call_indirect`, whose target is a function-table index discovered at run
time. The common loop is therefore an indirect tail call, not a direct one. That
detail is the floor's load-bearing point in Phase A (§A3) and the hard problem's
load-bearing point in Phase B (§B2).

## Decision: a two-phase embedded strategy

- **Phase A — on-device wasm (WAMR).** Run goat's existing `.wasm` on the board
  under WAMR, fast-interpreter first and AOT when speed is wanted, with
  `WAMR_BUILD_TAIL_CALL=1` and bulk-memory on (the feature floor from the audit
  below). Preemption is the runtime's / board's, per ADR 0021 — not injected fuel.
  Phase A unblocks the board tickets now (§Sequencing).
- **Phase B — native host-compilation (endgame).** Compile goat on the host to a
  native board binary; no wasm runtime on the device. §B records the migration from
  A, the hard problem (native toolchains do not guarantee constant-stack tail
  calls, and goat's loops *are* tail calls), and the plan-of-record for solving it.

Phase B does not retire Phase A; it is the footprint/speed endgame for boards that
want it, reached after Phase A has proven the embedded profile, the host API, and
the conformance suite on real hardware. A board WAMR cannot leave can stay on Phase
A indefinitely.

## Phase A — on-device wasm: WAMR

### A1. On-device interpreter: WAMR fast-interpreter (wasm3 the fallback)

The interpreter choice:

| Runtime | Kind | Footprint (Cortex-M4F core VM) | Tail calls (guest `return_call`) | AOT path | ESP32 / RP2040 | Maintenance |
|---|---|---|---|---|---|---|
| **WAMR** | classic + fast interpreter, AOT, LLVM JIT | fast-interp ~59 KB, classic ~56 KB, AOT runtime ~29 KB (figures **already include** tail-call) | **Yes** — `WAMR_BUILD_TAIL_CALL=1` (default off); supported in classic-interp, fast-interp, AOT, and LLVM-JIT | **Yes**, same project (wamrc) | ESP32 first-party (Espressif component/fork); RP2040 via bare-metal builds | Active (Bytecode Alliance + Espressif) |
| **wasm3** | fast interpreter only | tens of KB; among the smallest | **Listed "Ready"** on main | **No** — interpreter only | Broad MCU matrix incl. ESP32/RP2040 | **Minimal-maintenance** — no new feature work, PRs reviewed/merged only |

Both run goat's tail calls today. The deciding differences are the AOT path and
maintenance: WAMR carries the interpreter *and* the AOT compiler under one
actively-maintained, ESP32-first dependency, so Phase 12's "start with an
interpreter, add AOT" plan graduates without changing runtime vendor or
re-validating the tail-call story. wasm3 is smaller and famously fast, but it is an
interpreter with no AOT and is now in minimal-maintenance mode — a dependency that
will betray you later is one to keep off the critical path (Mickens). Keep wasm3 as a
named fallback for a board too small for WAMR, not as the default.

The tail-call flag's marginal cost is already folded into WAMR's published
Cortex-M4F figures above, so "keep tail calls" does not widen the footprint Phase A
was going to ship anyway.

### A2. AOT path: WAMR AOT first; wasm→C (wasm2c / w2c2) only for a locked image

Two AOT shapes, for different needs:

- **WAMR AOT** — compile `.wasm` → `.aot` off-device with `wamrc` (LLVM-based),
  flash the `.aot` beside the ~29 KB on-device AOT runtime. Near-native speed; tail
  calls supported in AOT mode under the **same** `WAMR_BUILD_TAIL_CALL` flag; same
  project as the interpreter, so interp→AOT is a graduation, not a second vendor.
  This is Phase A's default speed path.
- **wasm→C (`wasm2c` / `w2c2`)** — translate `.wasm` → C off-device, compile with
  the board's own C toolchain (arm-gcc, xtensa-gcc), link into one firmware image.
  Smallest possible runtime overhead and a single statically-linked image; the right
  tool for a certification / locked-image scenario or a board WAMR cannot target.
  **Three costs** make it a deferred fallback within Phase A, not the default:
  1. **Tail-call-in-C is not free.** Standard C guarantees no tail-call
     optimization. A `return_call` that must run in constant stack needs
     `[[clang::musttail]]` (Clang only) or a trampoline the translator emits; the
     Xtensa/ARM **GCC** toolchains these boards ship do not guarantee it. So goat's
     tail calls bite the wasm→C path *differently* from the interpreters — the
     translator accepting the opcode is necessary but not sufficient. (This same
     problem returns, enlarged, as Phase B's hard problem — §B2.)
  2. **Support is unverified.** w2c2's documentation lists WebAssembly 2.0,
     extended-const, threads, SIMD, and WASI — but **not** tail calls; wabt's
     `wasm2c` tail-call support in generated C is unconfirmed. Either must be
     verified before a board plan depends on it.
  3. **Heavier iteration loop.** A full C compile per program cuts against
     live-coding-over-serial (#119), where loading a `.wasm`/`.aot` is the fast path.

When each makes sense: **interpreter first** (load a `.wasm` at run time, fast
iteration, live coding, tens of KB), **WAMR AOT** when a program needs speed the
interpreter can't give, **wasm→C** only for the locked-image / unreachable-board case
above. WAMR gives the first two under one roof.

### A3. The feature floor is MVP + tail-call + bulk-memory — we keep tail calls

The floor goat's emitted modules may require is **the WebAssembly MVP plus the
tail-call and bulk-memory proposals** — the full enumeration is in *Feature floor:
what goat emits vs. what the runtime must provide* below. This section decides the
load-bearing, expensive-to-reverse half, the tail-call requirement; the audit adds
one more opcode (`memory.fill`, in the allocator's `free`) that both candidate
runtimes already run. Concretely: every host — browser, wasmtime, the Apple shell,
and the microcontroller — must run `return_call` / `return_call_indirect` and
`memory.fill`. The three real options for the tail-call half and their costs:

**(a) Pick a runtime that supports tail calls — chosen.** Cost: constrains §A1/§A2 to
WAMR (flag on) or wasm3 (maintenance-mode), and excludes any runtime whose tail-call
support is unverified (w2c2 today) until it is confirmed. **Zero codegen cost** —
goat emits exactly what it emits now, and the browser/wasmtime paths are unchanged.
Available today.

**(b) Add a no-tail-call codegen variant in `goat_wasm` — rejected, a real and large
cost.** You cannot simply "stop emitting `return_call`": by ADR 0013 that makes
*every loop* recurse once per iteration and consume native stack proportional to the
iteration count. ADR 0014 caps a turtle run at 1,000,000 commands, so a legitimate
kid program would want on the order of 10⁵–10⁶ native frames — fatal on #116's
bounded MCU stack, the exact budget this work exists to protect. To actually drop
tail calls you must do one of:
  - **(i) Add a real loop/iteration node to MIR** and re-lower `repeat`/`for` to it.
    This *reverses* ADR 0013's deliberate "no Loop node" decision and touches
    lowering, mono, rc, verify, the interpreter, and wasm emit — and it still leaves
    genuine user tail recursion *and all mutual recursion* stack-bound, because those
    aren't loops.
  - **(ii) Emit a runtime trampoline in wasm** — a tail call returns a "call-target +
    args" sentinel and a driver loop re-dispatches. This handles the general case,
    including the `return_call_indirect` closure loops that are the common case, but
    it adds per-call overhead and complexity to the hot path and to the ABI the hosts
    depend on.

Either way it degrades the embedded stack story it was meant to improve: #116
(bounded stack), and the recursive-eval shape #223 tightened (closed), both get
*worse* if native tail calls become native recursion. Net: option (b) is a
multi-pass compiler change plus either an ADR-0013 reversal or a hot-path trampoline.

**(c) Hybrid — emit tail calls only where they don't blow the stack — a future
optimization and the seed of Phase B's loop lowering, not a floor.** Recognize
*direct* self-tail-recursion and emit a wasm `loop` block (a local jump, no
`return_call`); keep `return_call` / `return_call_indirect` for mutual and
closure/indirect tail calls. The limit is the Context's sharp detail: the common loop
captures an outer binding, so it is a closure and lowers to `return_call_indirect`,
whose target is a runtime table index the `loop`-block trick can't convert without
closure-self-recursion analysis; and mutual recursion can't become a single `loop` at
all. So (c) *reduces* how many `return_call`s goat emits — a legitimate
size/portability win — but does **not** remove the runtime's tail-call requirement. In
Phase A it is a lever to pull later; its real payoff is Phase B, where the *same*
"recognize self-tail-recursion, emit a loop" analysis becomes **loop recovery** on the
native backend (§B2). Do the analysis once, at the MIR level, and both phases use it.

**Chosen (a): set the floor at MVP + tail-call + bulk-memory and keep goat's codegen
unchanged.** It is the only option with no codegen change; it keeps the embedded
stack budget honest (native tail calls = constant stack) instead of fighting it; and
it carries both the interpreter-first and the AOT-speed path under one
actively-maintained, ESP32-first dependency. Reject (b) as a language-level change in
backend's clothing (ADR 0013 makes tail calls the implementation of every loop). Hold
(c) as both a Phase-A size optimization and the prototype of Phase B's loop recovery.

### A4. Preemption on the board is the runtime's / the board's — not injected fuel

**This supersedes the coherence claim in earlier drafts of this ADR** — that "the MCU
host refills a compiler-injected `goat_fuel` global per event exactly as the browser
does." ADR 0021 removed injected fuel from the language entirely: goat emits no
`goat_fuel` global and no per-function-entry fuel check on any host, and each host
owns preemption natively (ADR 0021 §2). The board is no exception, in either phase:

- **While a board runs the Phase-A on-device wasm interpreter**, preemption is **the
  runtime's own interruption API**: WAMR checks an interruption flag at loop
  back-edges and call sites and can be told to trap a runaway guest from another
  context (a timer interrupt, the board's event loop). That is the board analogue of
  wasmtime's epoch interruption (ADR 0021 §2a) — a host mechanism, not goat-emitted
  fuel.
- **Underneath that, and in Phase B's native binary**, preemption is **the board's
  own**: a hardware watchdog timer the firmware kicks each loop iteration (a missed
  kick resets the board on a true hang), and, if a software bound is ever wanted,
  compiler-inserted cooperative yield points — the native analogue of an epoch check,
  emitted by the native target when it asks for one, carrying no reserved global and
  taxing nothing on hosts that don't (ADR 0021 §2c).

So "the board stops a runaway program" is a board/runtime action — a WAMR interrupt, a
watchdog reset — in the same class as a `trap`, never a checker error; the
"errors come only from the checker" invariant holds. ADR 0021 T3 (embedded preemption
on-target, deferred and coupled to this ADR / #232) is the ticket that confirms it on
real hardware; it is E3 in §Proposed first embedded tickets.

### A5. Coherence with the profile (ADR 0017) and testing (ADR 0018)

- **ADR 0017 — the embedded profile.** The i32 `Int` / f32 `Float` profile (chosen
  because the RP2040 has no FPU and the ESP32 is single-precision) is already landed
  (#235). Phase A picks the *runtime* that executes that profile's modules on-device.
  Keeping tail calls costs nothing extra on the embedded profile:
  `return_call_indirect` is width-agnostic. (ADR 0017's current "not yet supported:
  interactive programs on the embedded profile" — event exports take `Float`
  payloads at the program's width — is board work near #117/#118, not this ADR.)
- **ADR 0018 — one suite, a thin driver per host.** The on-device runtime becomes a
  new **driver** over the existing Rust conformance cases — a WAMR embedding driver
  that runs the shared `(source, expected observable outcome)` cases and asserts the
  same prints / scene-calls / traps / `live == 0` the CLI asserts — not a new
  hand-written suite. wasmtime already proves the tail-call lowering; the WAMR driver
  proves those same cases run on-device with the flag on. Phase B reuses the same
  suite behind the same boundary, so the migration is driver-swappable.

## Phase B — native host-compilation (endgame)

### B1. The migration from A to B

Phase A ships boards on WAMR, reusing the wasm backend: boards run, kids get turtles,
and the embedded profile (ADR 0017), the host API (#117), the event/interrupt model
(#118), and the conformance suite (ADR 0018) are all proven on real hardware against a
`.wasm` the board interprets or AOT-loads. Phase B keeps everything above the final
lowering and changes only that final step: instead of a `.wasm` the board runs under a
runtime, goat compiles the program on the host to a **native board binary** that the
board runs directly, with no wasm runtime on the device.

The migration is incremental and reversible (the operator keeps their freedom — Ted
Nelson). Phase B is a new backend behind ADR 0018's thin-driver boundary, so during
bring-up a board can run WAMR and native side by side and the same conformance suite
judges both; a board WAMR cannot leave stays on Phase A; and nothing about Phase B
forces the browser, wasmtime, or Apple hosts to change. What carries over from A: the
embedded profile, the host-import API, the event model, the conformance suite, and —
load-bearing — the loop-recovery analysis seeded as Phase A's hybrid (c). What changes:
the target of the final lowering, and the preemption mechanism (from the runtime's
interrupt to the board's watchdog, both already ADR 0021 §2c).

### B2. The hard problem: native toolchains don't guarantee constant-stack tail calls

goat's loops **are** tail recursion (ADR 0013; "the tail call is the jump"), and the
floor keeps tail calls (§A3). On wasm this is free: `return_call` /
`return_call_indirect` run a tail-call chain in constant stack — the proposal
*guarantees* it, which is the whole reason Phase A is cheap. Native board toolchains
give no such guarantee. Standard C mandates no tail-call optimization (TCO);
`[[clang::musttail]]` is Clang-only; and the arm-gcc / xtensa-gcc toolchains these
boards ship promise nothing. So a native lowering that emitted each goat loop iteration
as an ordinary self-call would grow the native stack by one frame per iteration — and
ADR 0014 caps a run at 1,000,000 commands, so a legitimate kid loop would want ~10⁵–10⁶
native frames, fatal on the board's bounded stack (#116). **Native lowering of goat's
tail-recursive loops therefore needs an explicit constant-stack mechanism; the
toolchain will not supply one.** Two mechanisms, and goat wants both:

- **Trampoline** (portable, per-call overhead). A tail call returns a "next function +
  its arguments" sentinel instead of calling; a driver loop re-dispatches until a
  non-tail result comes back. It handles *every* case in constant stack — direct
  self-recursion, mutual recursion, and the `return_call_indirect` closure loop that is
  the common case (the Context's sharp detail) — at the cost of building a sentinel and
  an indirect dispatch on every tail call, including the hot kid loop.
- **Loop recovery** (a backend pass, per-case, zero overhead where it applies).
  Recognize direct self-tail-recursion and emit a **native loop** (a C `for`/`while`/
  `goto` — a real jump) instead of a self-call; fall back to the trampoline for what it
  can't prove. **This is not a language change.** ADR 0013 stands: goat still has no
  loop keyword and no `Loop` MIR node; the backend merely *recognizes* the
  tail-self-recursion pattern the checker already emits and lowers it to a native loop.
  Its limit is §A3(c)'s: the common loop captures an outer binding, so it is a closure
  that lowers to the indirect form, whose target is a runtime table index; loop
  recovery converts it only when it can prove the indirect target is the function
  itself (closure-self-recursion analysis), and mutual recursion never collapses to a
  single loop. So loop recovery covers the provable direct cases at zero per-call cost;
  the trampoline covers the residual.

**Recommendation: both — loop recovery as primary, trampoline as the fallback.** Loop
recovery keeps the common kid loop at zero per-call overhead and compiles to a native
jump; the trampoline guarantees constant stack for the general case the toolchain
won't. Neither alone suffices: a pure trampoline taxes the hot loop, and pure loop
recovery cannot handle mutual or unprovable-indirect recursion. This is the same
analysis Phase A's hybrid (c) prototypes against wasm `loop` blocks, done once at the
MIR level and reused — the shared concern factored out rather than duplicated per
backend (Hickey).

### B3. The fork: wasm→C vs a direct native backend

Two ways to reach native code, each with a different relationship to §B2:

- **wasm→C (`wasm2c` / `w2c2`).** Reuse the existing wasm backend; translate the
  `.wasm` → C off-device; compile with the board's C toolchain. It reuses everything
  already built and validated, which is its whole appeal. But it inherits the
  C-no-TCO problem *and* bets on the translator's handling of it: w2c2 doesn't document
  tail calls and wabt `wasm2c`'s is unconfirmed (§A2 cost 2). And goat does not control
  the loop lowering — it is the translator's to get right, so loop recovery would have
  to be bolted onto generated C rather than emitted by goat.
- **Direct native backend (goat MIR → native).** Lower MIR straight to native — via
  Cranelift, LLVM, or emitted C — so goat controls the loop lowering and emits the
  loop-recovery loop or the trampoline itself. Cranelift is out for these boards (no
  32-bit ARM / Xtensa / riscv32 backend — the Context's reason Phase 12 went through
  wasm at all). LLVM has the backends (arm and riscv32 upstream, Xtensa via Espressif's
  fork) but is a heavy host dependency. Emitting **portable C from MIR**, compiled by
  the board's own GCC, avoids both: no LLVM, no Cranelift-target gap, and goat owns the
  loop lowering.

**Recommendation (plan-of-record, steerable when Phase B starts): a direct native
backend that emits portable C from MIR, with wasm→C held as a named fallback.**
Rationale: (1) the crux of Phase B is loop lowering, and only a backend goat controls
can emit loop recovery + trampoline directly rather than hoping a third-party
translator preserved tail-call semantics in C; (2) it keeps w2c2's unconfirmed
tail-call support off the critical path (Mickens — the dependency will betray you); (3)
the loop-recovery analysis is wanted anyway as Phase A's hybrid (c), so doing it once
at MIR level pays in both phases (Hickey). The honest cost, stated plainly (Knuth): a
MIR→C backend is net-new — lowering, calling convention, the RC drops, the embedded
allocator — where wasm→C reuses the validated wasm backend. That build-vs-control
tradeoff is the genuine open question Phase B opens, and it is a plan-of-record, not a
closed door: when Phase B starts, the main loop records the fork as its own ADR, with
the loop-recovery spike's measurements (ticket E6) in hand.

## Sequencing: Phase A unblocks the board tickets now; Phase B is the follow-on

Phase A is buildable today and unblocks the board work:

| Ticket | What it is | Phase |
|---|---|---|
| #114 | On-device wasm runtime (interpreter → AOT) | **A** — this *is* WAMR fast-interp → WAMR AOT (§A1/§A2) |
| #115 | Off-device compile + flashing (WebSerial/WebUSB) | **A** — per-board build/flash mechanics |
| #116 | Embedded constraints: `f32`, pooled heap budget, bounded stack | **A** board work (`f32` landed via #235); its **bounded-stack** dimension is what makes Phase B's §B2 loop lowering load-bearing |
| #117 | Embedded host API (WIT): GPIO, timers, LEDs, sensors, serial | **A** — the transport beneath ADR 0015's contract, in place of the browser's `scene.*` |
| #118 | Embedded event model + interrupt queue | **A** — board bring-up |
| #119 | Live coding over serial | **A** — favors the interpreter / `.wasm` fast path (§A2 cost 3) |
| ADR 0021 T3 | Embedded preemption on-target | **A** — confirm WAMR interrupt / board watchdog stops a runaway loop, no fuel (§A4); = E3 |
| *(new)* native backend + loop-recovery/trampoline lowering | §B2/§B3 | **B** — follow-on; hybrid (c) is the shared seed, prototyped in Phase A as E6 |

#223 (the recursive operator/boolean-chain eval that sat on a tight native-stack
margin) is **closed**, but the native-stack shape it addressed is exactly what Phase
B's §B2 must keep bounded — relevant to Phase B, resolved for Phase A.

## Proposed first embedded tickets (Phase A), in dependency order

Each is one line of scope + one of acceptance. E1 is the gateway; E2→E3→E4 are the
on-hardware sequence; E5 runs parallel to E2; E6 is the Phase-B design spike that can
start in parallel because it writes no production code.

- **E1 — WAMR embedding + conformance driver** *(maps to #114, interpreter half).*
  Scope: vendor and pin WAMR, build the fast-interpreter with
  `WAMR_BUILD_TAIL_CALL=1` and `WAMR_BUILD_BULK_MEMORY=1`, and wire it as an ADR-0018
  thin driver over the shared Rust conformance suite. Acceptance: the shared
  `(source, expected observable)` cases run under WAMR fast-interp and assert the same
  prints / scene-calls / traps / `live == 0` the CLI asserts; the board config asserts
  both flags and refuses to load a module if either is off; CI runs the driver.
  Depends on: nothing.
- **E2 — Board bring-up: flash and run a goat `.wasm` on one target** *(maps to #115 +
  #117).* Scope: get `goat build --target embedded` output loaded and executing on one
  physical board (ESP32 or RP2040) under WAMR fast-interp, with the GPIO/LED/serial
  host imports standing in for `scene.*`. Acceptance: a minimal embedded goat program
  runs on-device and drives an LED or serial output; `live == 0` holds after teardown
  on-device. Depends on: E1.
- **E3 — Embedded preemption on-target** *(= ADR 0021 T3; maps near #118).* Scope:
  confirm the board watchdog (and WAMR's interruption API at loop back-edges while on
  the interpreter) stops a non-terminating goat loop without re-introducing injected
  fuel. Acceptance: a runaway loop is stopped and the board recovers; no `goat_fuel`
  global is present; the result is recorded (closes ADR 0021 T3). Depends on: E2.
- **E4 — WAMR AOT graduation** *(maps to #114, AOT half).* Scope: add the `wamrc`
  path (`.wasm` → `.aot`, same `WAMR_BUILD_TAIL_CALL` flag) and the ~29 KB on-device
  AOT runtime; run the same conformance cases through AOT. Acceptance: the conformance
  suite passes under WAMR AOT on-device, a speed-sensitive example runs materially
  faster than fast-interp, and interp and AOT remain one runtime vendor. Depends on:
  E2 (and E1).
- **E5 — Pooled embedded allocator (bounded heap)** *(maps to #116).* Scope: the
  pooled-heap / bounded-stack budget behind the allocator's existing three functions;
  optionally a variant without `memory.fill`/`memory.copy` that drops bulk-memory from
  the *board* floor (the lever named in the audit §4). Acceptance: the board runs under
  a fixed heap pool with no unbounded growth; if the no-bulk-memory variant is taken, a
  board build with `WAMR_BUILD_BULK_MEMORY=0` still loads and runs every conformance
  case. Depends on: E1 (parallel to E2–E4).
- **E6 — Phase-B design spike: native tail-recursive-loop lowering (loop recovery vs
  trampoline)** *(new; informs Phase B §B2/§B3).* Scope: prototype the MIR-level
  loop-recovery analysis as Phase A's hybrid (c) — recognize direct self-tail-recursion
  and emit a wasm `loop` block, measure coverage and the trampoline's per-call overhead
  — so the same pass feeds Phase B's MIR→C backend. Acceptance: a recorded decision
  (an ADR, written when Phase B starts) on the Phase-B fork (direct MIR→C vs wasm→C)
  and the loop-lowering mechanism, backed by the spike's measured trampoline per-call
  overhead and loop-recovery coverage (what fraction of goat loops convert to a native
  loop); no production backend change is required to land the design. Depends on:
  nothing (design; can start in parallel).

## Feature floor: what goat emits vs. what the runtime must provide

§A3 fixed the floor by reasoning from tail calls alone. Reading the backend end to end
— `wasm/src/lib.rs` and the allocator it emits, `wasm/src/allocator.rs` — shows the
emitted floor is one proposal wider: **MVP + the tail-call proposal + the bulk-memory
proposal**. "Bulk memory" is the proposal that adds `memory.fill` / `memory.copy` /
`memory.init` / `data.drop` and *passive* data segments (a data segment the module
copies into memory with an explicit `memory.init` at run time, rather than an *active*
segment the engine lays down at instantiation). The extra requirement over §A3 is one
opcode, `memory.fill`, emitted unconditionally by the allocator's `free`; everything
else goat emits is MVP or tail-call. This section lists the whole emitted set, maps
each item to WAMR and wasm3 at their 2026 defaults, and separates what the *board*
needs from what only desktop/browser hot-reload needs.

### What the codegen actually emits

| Emitted feature | Proposal tier | Where in the output | In which modules |
|---|---|---|---|
| i32/i64/f32/f64 numerics; `if`/`block`/`loop`/`br*`; `call`; `call_indirect` on a funcref table (`CallIndirect { table_index: 0 }`); active element + active data segments; owned, exported `memory`; `memory.size`/`memory.grow`; mutable globals, including *exporting* `goat_site` (and, until ADR 0021's fuel-removal lands, `goat_fuel`); `unreachable` | **MVP** | throughout `lib.rs` / `allocator.rs` | every module |
| Trapping `i32.trunc_f32_s` / `i64.trunc_f64_s` behind an explicit range guard (`truncate_to_int`); `f32.trunc`/`f64.trunc`; `f32.sqrt`/`f64.sqrt`; `i64.extend_i32_s`, `i32.wrap_i64`, `f64.promote_f32`, `f32.demote_f64` at the host/profile boundary | **MVP** | `truncate_to_int`, `checked_int32`, `narrow_int`, `call_foreign` | every module |
| `return_call` (direct tail call) and `return_call_indirect` (closure-loop tail call — the common case, per the Context) | **tail-call** | `Expr::TailCall` lowering | every module |
| `memory.fill` — the allocator's `free` poisons a freed block for use-after-free detection (`allocator.rs` invariants) | **bulk-memory** | `FreeList::free` | **every module** |
| passive data segment + `DataCountSection` + `memory.init` + `data.drop`; *imported* `memory`; *imported* mutable globals `heap`/`live`; a `start` function; an immutable `i64` fingerprint global | **bulk-memory** (init/drop/passive) + **MVP** (imported memory/globals, start, i64 global) | `emit_reloadable` / `load_data` | **hosted/reloadable only** — interactive hot-reload; `emit_module` rejects interactive programs on the embedded profile, so the board emits none of it |

**Candidates the audit refutes** — proposals goat does *not* require, each read out of
the code rather than assumed:

| Candidate proposal | Verdict | Why |
|---|---|---|
| reference types (externref, multiple tables, `table.get`/`set`, typed function refs) | **not used** | the closure table is a plain funcref table reached by `call_indirect` / `return_call_indirect` — MVP (the table) + tail-call (the `return_` form), not reference-types |
| non-trapping float-to-int (`trunc_sat`) | **not used** | `math.truncate` lowers to the *trapping* `trunc_f*_s` behind a range guard that raises goat's own `NOT_A_WHOLE_NUMBER` diagnostic |
| sign-extension operators (`i32.extend8_s`, …) | **not used** | the only `extend` emitted is `i64.extend_i32_s`, the MVP i32→i64 widening — a different instruction |
| multi-value (a function or block returning ≥2 values) | **not used** | every `func_signature` and every block type returns 0 or 1 value |
| SIMD, threads/atomics, GC, memory64, custom page size | **not used** | `memory64: false`, `page_size_log2: None` (default 64 KiB — what #116's custom-page-size check guards), no SIMD/atomic/GC opcodes emitted |

Two things the "i32/f32 embedded profile" label can hide: a board module still
*imports* `print_int` with an `i64` parameter and widens `Int`→`i64`
(`i64.extend_i32_s`) at that boundary, so the module is not i64-free — but `i64` is MVP
and universal, a note, not a risk. And `memory.fill` is load-bearing for a *safety*
feature (poison-on-free), not an incidental optimization that could be dropped for free.

### Runtime support, 2026 defaults

| Feature goat needs | WAMR (classic-interp / fast-interp / AOT) | wasm3 (fallback) |
|---|---|---|
| **tail-call** (`return_call[_indirect]`) | `WAMR_BUILD_TAIL_CALL` — **default OFF**; set `=1` (all four modes) | "Tail call" listed **Ready** (main `README` proposals group) |
| **bulk-memory** `memory.fill` (every module) | `WAMR_BUILD_BULK_MEMORY` — **default ON** (also turns on `bulk-memory-opt`) | "Bulk memory operations" listed **Ready** |
| **bulk-memory** passive + `memory.init`/`data.drop` (hosted reload; desktop/browser only) | same `WAMR_BUILD_BULK_MEMORY`, default ON | same, Ready |
| imported memory / imported mutable globals / `start` (hosted only) | MVP / mutable-globals baseline — on | supported (Lime1 "Import/Export of Mutable Globals") |
| funcref table + `call_indirect` | MVP; on older WAMR, table ops sit under `WAMR_BUILD_REF_TYPES` (**default ON**) | MVP — supported |
| non-trapping-float-to-int, sign-ext, multi-value (**not emitted**) | "always on" in WAMR's Wasm-2.0 preset — zero risk even unused | Lime1 group, Ready — zero risk |
| SIMD / threads / GC / memory64 / custom page size (**not emitted**) | irrelevant | `⛔ N/A` for SIMD/threads/GC — irrelevant, goat emits none |

WAMR flag defaults are from the upstream `doc/build_wamr.md`. The wasm3 rows are the
current `wasm3/wasm3` `main` `README` "Features" table, whose Status column marks whole
proposal *groups* "⭐ Ready" — a milestone marker, not a per-opcode guarantee.

### Differences that matter

1. **The board build carries two flags, not one.** The "one build flag" (tail-call,
   default off) is half the story. `memory.fill` in `free` means a goat module also
   needs `WAMR_BUILD_BULK_MEMORY`. That flag is *on* by default, so the ordinary build
   is fine — but a footprint-minimized board build that turns it off would fail to
   *load* every goat module (WAMR validates the whole module at load, so the opcode is
   rejected even in a program that never frees). The board config must assert both:
   `WAMR_BUILD_TAIL_CALL=1` (flip on) and `WAMR_BUILD_BULK_MEMORY` (keep on).
2. **§A3's floor label undercounts.** "MVP + tail-call" reads "MVP + tail-call +
   bulk-memory" throughout this ADR. The *decision* is unchanged — both candidate
   runtimes support bulk memory out of the box — but a future host that ran tail calls
   yet not bulk memory would otherwise be mis-judged in-floor.
3. **The board/desktop delta is real and runs the favorable way.** The whole
   reloadable path — passive data, `memory.init`/`data.drop`, imported memory, imported
   mutable globals, `start` — is interactive-only and rejected on the embedded profile,
   so the board emits *none* of it. The board's only above-MVP requirements are
   tail-call and the single `memory.fill`. Desktop and browser hot-reload need the full
   bulk-memory set; the board needs one opcode of it.
4. **A future embedded allocator could lower the board floor by one proposal — but
   nothing emitted today does.** `memory.fill` is required only because the shared bump
   allocator poisons freed blocks. `allocator.rs` already anticipates a pooled embedded
   allocator "behind the same three functions"; one written without
   `memory.fill`/`memory.copy` would drop bulk-memory from the *board* floor (desktop
   reload would still need it). That is allocator work (ticket E5) — recorded here as a
   lever, not a change this ADR makes.
5. **wasm3 now has two proposals to verify, and it is minimal-maintenance.** Both
   tail-call and bulk-memory sit in "Ready" groups of the current `main` README,
   consistent with keeping wasm3 a fallback — but a README milestone marker is not a
   verified per-opcode guarantee, and if wasm3's bulk-memory were incomplete (an older
   vendored snapshot marked it "partial"), wasm3 could run *no* goat module at all,
   tail calls or not. Verify tail-call **and** `memory.fill` against the pinned wasm3
   build before the fallback is trusted.

### Bottom line

"Keep tail calls, no codegen change" **survives** the whole emitted-feature set — with
two asterisks, both about the floor's *membership*, neither about codegen:

- **(\*) The floor is MVP + tail-call + bulk-memory.** No codegen change follows (WAMR
  enables bulk memory by default; wasm3 lists it Ready), but the floor wording, the
  Consequences, and the one-way-door name bulk-memory, or the recorded floor is smaller
  than the bytes goat emits.
- **(\*) Two build flags on the board, not one** — `WAMR_BUILD_TAIL_CALL=1` (default
  off) and `WAMR_BUILD_BULK_MEMORY` (default on, must stay on). Both are checked at
  load.

No feature goat emits is unsupported by, or behaves differently on, WAMR with those two
flags set. Every other candidate proposal — reference types, sign-extension ops,
non-trapping float-to-int, multi-value, SIMD, threads, memory64, custom page size — is
absent from the output, so none forces a codegen change or a codegen variant. The one
genuine residual unknown in Phase A is wasm3's per-opcode support at its pinned version
(two proposals now, not one), which §A1 routes around by making WAMR the default and
wasm3 the named, to-be-verified fallback.

## Consequences

- **Phase A ships to boards with goat's codegen unchanged**; the browser, wasmtime, and
  Apple paths are untouched. The embedded footprint is WAMR's published figures, which
  already include tail-call. The dependency surface is one runtime vendor and two build
  flags — `WAMR_BUILD_TAIL_CALL` (off by default, flip on) and `WAMR_BUILD_BULK_MEMORY`
  (on by default, keep on); the interp→AOT graduation is internal to that vendor.
- **The feature floor is now explicit for *every* host:** a new host that cannot run the
  tail-call *and* bulk-memory proposals is out of scope until it can, rather than
  silently forcing a codegen rewrite.
- **Preemption is the host's on the board too** (ADR 0021): a runaway loop is stopped by
  a WAMR interrupt or a board watchdog, in the same class as a `trap`, never a checker
  error — and no `goat_fuel` is reintroduced to do it.
- **Phase B is committed as a direction, not yet as an implementation.** The native
  backend's fork (direct MIR→C vs wasm→C) and its loop-lowering mechanism (loop recovery
  + trampoline) are the plan-of-record above; both become a recorded ADR, informed by
  the E6 spike, when Phase B actually starts. ADR 0013 stands either way — loop recovery
  recognizes a pattern, it does not add a loop to the language.

### Reversible (not one-way doors)

- **Which runtime.** WAMR vs wasm3 vs a future engine is a *driver* swap behind ADR
  0018's thin-driver boundary — a host change, not a language change. The same boundary
  makes **Phase B itself** reversible: a direct native backend is another driver, and a
  board can run WAMR and native side by side during bring-up.
- **The interp→AOT graduation**, and the per-board build/flash mechanics (#115).
- **The hybrid (c) / loop-recovery analysis** — it can land first purely as a Phase-A
  wasm size win, then be reused for Phase B's native loop lowering; it only *reduces*
  emitted `return_call`s within a floor that still permits them.
- **Adding the wasm→C path** later, for a locked image or a board a direct native
  backend can't reach.

### One-way door

The genuine one-way door is **the feature floor itself** — whether goat's emitted
modules are allowed to require the tail-call proposal (and, per the audit, bulk-memory).
Every host and every program compiled so far assumes tail calls; lowering the floor to
"no tail calls" later is the ADR-0013 reversal of option (b) and would have to hold for
*all* hosts at once. Phase B does **not** open that door: native host-compilation keeps
goat's tail calls and solves their constant-stack lowering on the target (§B2), rather
than dropping them. So the floor is the expensive-to-reverse decision, and it is set at
MVP + tail-call + bulk-memory and kept there across both phases.

## References (external, as of 2026-11)

- WAMR `WAMR_BUILD_TAIL_CALL=1/0, default off … Supported in classic-interpreter,
  fast-interpreter, AOT and LLVM JIT modes` — `doc/build_wamr.md`; Cortex-M4F core-VM
  footprints (tail-call/bulk/shared enabled) — project README.
- WAMR `WAMR_BUILD_BULK_MEMORY=1/0, default on` (also enables `bulk-memory-opt`);
  `WAMR_BUILD_REF_TYPES` default on; `memory64` default off; "Multi-value, Non-trapping
  float-to-int Conversions and Sign-extension Operators are always on" in the Wasm-2.0
  preset — `doc/build_wamr.md`. WAMR runtime interruption (interrupt flag checked at
  loop back-edges / call sites) is the board analogue of wasmtime epoch interruption.
- wasm3 — "Tail call" and "Bulk memory operations" both listed under "⭐ Ready" groups
  in the `wasm3/wasm3` `main` `README` "Features" table (a milestone marker, not a
  per-opcode guarantee); project stated to be in a minimal-maintenance phase. An older
  vendored snapshot marked bulk memory "partial" / tail call unsupported, so the pinned
  build's support is worth confirming.
- w2c2 README — lists WebAssembly 2.0, extended-const, threads, SIMD, WASI; no
  tail-call entry.
- C tail calls — no standard guarantee; `[[clang::musttail]]` is Clang-specific; arm-gcc
  and xtensa-gcc guarantee no tail-call optimization.
- Cranelift target coverage — no 32-bit ARM (Cortex-M), Xtensa, or riscv32 backend
  (`docs/plan.md`), which is why Phase A reaches boards through wasm and a Phase-B direct
  native backend would use emitted C or LLVM rather than Cranelift.
