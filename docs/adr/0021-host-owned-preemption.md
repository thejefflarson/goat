# ADR 0021 — The host owns preemption; goat emits no execution bound

- Status: accepted (2026-11-08)
- Context: ADR 0015 §5 ("Bounded update time via a compiler-injected fuel
  global") and its as-built note (#107 — the `goat_fuel` global, a 5,000,000
  per-call refill, the per-function-entry `fuel -= 1; trap-if-zero`); #249, which
  hardened the mechanism (`FUEL_START = i32::MAX` as a default bound, host-owned
  refill framing); ADR 0013 (loops lower to tail calls — there is no loop node)
  and ADR 0006 (a loop that captures is a closure), which together make tail
  calls the only unbounded construct; ADR 0019 (proposed in PR #243, issue #232 —
  the on-device wasm runtime / Phase 12 gateway), whose coherence note cites
  injected fuel as "the MCU mechanism"; #244 (the editor's COOP/COEP response
  headers, which cross-origin-isolate the page and so unlock `SharedArrayBuffer`);
  ADR 0018 (one Rust conformance suite, a thin driver per host). Recorded as the
  decision to remove fuel is taken, before the implementation tickets below.
  **This ADR supersedes ADR 0015 §5.**

## Context

goat injects a watchdog into every program it compiles. ADR 0015 §5 decided it
and #107 built it: the wasm backend emits a mutable `i32` global exported as
`goat_fuel`, and every compiled function begins with `fuel -= 1; if fuel <= 0 {
unreachable }`. A host resets the global to a budget before each call in; a
runaway call chain spends the budget in a bounded number of steps and traps,
which the host catches and reports as *"your program got stuck."* #249 later set
the module's starting value to `i32::MAX` so a host that never refills still gets
a bound, and framed the refill as the host's job.

Fuel exists for exactly one reason. The browser main thread cannot be preempted
from outside: once wasm is running, nothing on that thread can interrupt it, and
goat's only source of non-termination is unbounded recursion. Non-tail recursion
self-limits by exhausting the wasm stack, but tail calls do not — and by ADR 0013
every loop in the language *is* a tail call (`repeat`/`for` lower to tail-position
self-recursion; "the tail call is the jump"). So a `while`-shaped goat loop with
no exit runs forever in constant stack, and on the browser main thread that
freezes the tab. Fuel was the portable answer: a software bound the program
carries with it, checkable without any host preemption primitive.

That answer has three standing costs. It taxes the hot path — every function
entry, in every program, on every host, pays a load, a subtract, a store, a
compare, and a branch, whether or not the host could preempt. It complicates
codegen — a reserved global, a fixed global index that everything downstream
counts from, and a preamble on every function body. And it puts a resource bound
*in the language*, which is a strange place for one: a general-purpose language's
programs are allowed to take a long time.

The browser is the only host that cannot preempt natively. wasmtime has epoch
interruption. A native binary on a board has a hardware watchdog timer. The
browser itself has had an answer since workers shipped: run the untrusted code on
a thread you can kill. So fuel is a workaround for a single host's missing
primitive, imposed as a tax on all of them. Move preemption to where each host
already does it well, and the reason for fuel disappears.

## Decision

### 1. The language imposes no execution bound

goat's codegen stops emitting the `goat_fuel` global and stops emitting the
per-function-entry `fuel -= 1; trap-if-zero` preamble. A compiled goat function
begins doing its own work. There is no reserved fuel global, no `goat_fuel`
export, and no language-level step limit. **Each host owns preemption natively**
(§2), the way each host already owns the loop (ADR 0015 §1) and the side effects.

Rationale: fuel existed only to stand in for a preemption primitive the browser
main thread lacks; every host either has that primitive or can be given one
cheaply, so the stand-in is pure cost. Removing it simplifies codegen, removes a
tax from every function entry in every program, and restores the ordinary
expectation that a long-running program runs long rather than being killed by the
compiler.

**What this does not remove.** The output-size resource caps are a different
mechanism and they stay: ADR 0014's one-million-command cap on a run-once turtle
program, and ADR 0015 §3's per-frame cap of 100,000 shapes-plus-vertices on a
`draw`. Those bound how much a *terminating* call can emit, protecting host
memory; they are not a watchdog on execution time and nothing here touches them.
Fuel was solely about non-termination, and only non-termination is moving to the
host.

### 2. Each host owns preemption natively

| Host | Preemption mechanism | Default |
|---|---|---|
| CLI / wasmtime | wasmtime **epoch interruption** — a background thread advances an epoch; the store traps when a deadline passes | **Unbounded.** A long program runs; `Ctrl-C` stops it. `--timeout` arms an epoch deadline when a bound is wanted. |
| Browser | goat runs in a **terminable Web Worker**; a main-thread supervisor enforces a wall-clock deadline and `terminate()`s + restarts a stuck worker | A per-frame deadline on `update`/`draw`, and a whole-program deadline on a run-once program. The UI thread is never blocked, so it can always kill a spinning worker. |
| Embedded (endgame) | **native / board-level** — a hardware watchdog timer, or compiler-inserted cooperative yield points in the native code if a software bound is ever wanted | **Unbounded** native execution; the board's watchdog resets a true hang. Same spirit as the CLI: the board owns it. |

#### 2a. CLI / wasmtime — epoch interruption

wasmtime preempts natively: `Config::epoch_interruption(true)`, a background
thread that calls `Engine::increment_epoch` on a timer, and
`Store::set_epoch_deadline` turn a deadline into a trap at the next loop
back-edge or call. The native driver configures this once on the `Engine`/`Store`
and the CLI exposes it as an optional `--timeout`; with no flag the program is
unbounded and `Ctrl-C` is the stop. This is what ADR 0015 §5 already said the CLI
"prefers"; it now becomes the CLI's only mechanism, with no fuel underneath it.

#### 2b. Browser — a terminable Web Worker under a main-thread supervisor

goat executes in a Web Worker, not on the main thread. A **supervisor** on the
main thread owns the clock and the kill switch: it starts the worker, forwards
DOM input to it, and holds a wall-clock deadline — per frame for an interactive
program's `update`/`draw`, and whole-program for a run-once program. When the
deadline passes with no progress, the supervisor calls `Worker.terminate()`,
reports *"your program got stuck"* (the existing `STUCK_MESSAGE`), and
re-instantiates the worker. Because `terminate()` runs on the main thread against
the worker handle, it kills a worker that is spinning inside wasm — which is
exactly the case fuel existed to catch — and the UI stays live throughout.

Restart semantics, stated plainly: `terminate()` discards the worker's wasm heap,
so the model is gone. A terminated program restarts from `init` (or, under Phase
11 hot reload, from the last kept checkpoint). "Stuck" is a user error reported
and recovered, the same observable outcome as today's "the loop stops," not a
hang.

**The synchronous `update`/`draw` frame bridge.** ADR 0015's contract is
synchronous — the host calls `goat_update(model, event) -> model` and
`goat_draw(model)` and uses the result right away. A Worker, though, talks to the
main thread only by asynchronous `postMessage`. Two ways preserve the contract:

- **(A) `SharedArrayBuffer` + `Atomics`, with the frame loop inside the worker.**
  The worker owns the goat module *and* its per-frame loop, so `update`/`draw`
  stay synchronous exactly as the wasm ABI defines them — nothing about the
  compiled contract changes. `draw` renders through an `OffscreenCanvas`
  transferred to the worker, so the `scene.*` stream never crosses a thread
  boundary per call. DOM input is forwarded main-to-worker by `postMessage`
  (input is asynchronous anyway) and coalesced into the next frame. Preemption
  rides a one-word `SharedArrayBuffer`: the worker writes a progress counter at
  the top of each frame, and the supervisor — which cannot be told by a stuck
  worker, since a spinning worker sends no message — polls that word on its own
  timer and `terminate()`s when it has not advanced within the deadline. #244's
  COOP/COEP headers already cross-origin-isolate the page, which is the
  precondition `SharedArrayBuffer` requires, so this cost is paid.

- **(B) An async restructure.** Keep the loop driver on the main thread and make
  every call in a `postMessage` round-trip the driver `await`s. This needs no
  `SharedArrayBuffer` and no cross-origin isolation, but it turns ADR 0015's
  synchronous frame shape into a promise-based protocol end to end, doubles the
  per-frame thread crossings (the model and each `scene.*` call cross back), and
  makes ordering and backpressure the driver's problem.

**Pick: (A).** Cross-origin isolation is already in place (#244), so the cost that
makes (A) expensive is already paid; (A) keeps the compiled `update`/`draw`
contract byte-for-byte and keeps the per-frame transport on one thread, where (B)
would rewrite the contract into async and add thread hops for no gain in
preemption power — `terminate()` is the kill either way. The ergonomic cost of
(A) is honest and worth naming: `OffscreenCanvas` makes the canvas worker-owned,
the progress word is a hand-laid shared buffer, and `Atomics.wait` is forbidden
on the main thread (so the supervisor polls rather than blocks). These are
mechanical, not conceptual, and they buy an unchanged language contract.

#### 2c. Embedded — native host-compilation; preemption is a board concern

The embedded endgame is **host compilation to native code**: goat compiles on the
developer's machine to a native binary for the target board, which is flashed
directly. In the endgame there is **no wasm runtime — no interpreter, no on-device
AOT loader — on the device at all.** Preemption there is therefore a native,
board-level concern, not a wasm concern:

- **Default: unbounded native execution, with a hardware watchdog timer** the
  board resets on each loop iteration (or from the superloop); a true hang misses
  the kick and the watchdog resets the board. This is the CLI's stance — the host
  owns the stop — expressed in the board's own hardware.
- **If a software bound is ever wanted**, the native code backend inserts
  cooperative yield points (a deadline check at loop back-edges), the native
  analogue of an epoch check. This is a backend option, not a language feature,
  and it is not fuel: it is emitted by the native target when that target asks
  for it, carries no reserved global, and taxes nothing on the hosts that do not.

A bare-metal native binary genuinely cannot be preempted by an external software
supervisor the way a worker can be terminated. That is fine and it does not
reintroduce goat-injected fuel: the fallback is the board's hardware watchdog (or
the optional yield points above), i.e. the **native target's own preemption**,
chosen and owned by the target.

### 3. Reconciling ADR 0019 (PR #243)

ADR 0019 — proposed in PR #243, resolving issue #232 — argues for keeping goat's
tail calls and selecting an on-device wasm runtime (WAMR fast-interpreter, wasm3
fallback). Its coherence section calls the microcontroller "just another host of
ADR 0015's init/update/draw contract (its injected-fuel bound is explicitly the
MCU mechanism)." That clause is wrong under this ADR and must change before ADR
0019 is accepted.

The correction has two parts. First, on-device wasm (WAMR or wasm3) is at most an
**intermediate** step toward the embedded target; the endgame is native
host-compilation with no on-device wasm runtime (§2c). Second, and regardless of
which step the board is at, the MCU's preemption is **the native target's own
preemption — a board watchdog timer, or optional compiler-inserted yield points —
not an injected-fuel global.** (While a board still runs an intermediate on-device
wasm interpreter, that interpreter's own interruption API — WAMR checks an
interruption flag at loop back-edges — is the mechanism, still not goat-injected
fuel.) So ADR 0019's "injected-fuel bound is explicitly the MCU mechanism" is
replaced by "the native target's own preemption (board watchdog / optional yield
points)." ADR 0013's point that dropping tail calls is a language change stands
untouched; this ADR removes fuel, not tail calls.

### 4. Sequencing

The order is load-bearing and is stated plainly because getting it wrong freezes
a browser tab. **The browser must gain Worker-based preemption before, or in the
same change as, the removal of injected fuel from codegen.** Removing fuel first
would leave a stuck browser program with no watchdog at all — the exact tab-freeze
fuel was built to prevent.

1. **Browser worker supervisor (T1) lands first.** It is additive and safe to
   merge while fuel still exists: a module compiled with `FUEL_START = i32::MAX`
   that the worker never refills is effectively inert, so the supervisor's
   `terminate()` becomes the live watchdog with fuel doing nothing underneath it.
2. **Codegen removal + CLI epoch + native driver (T2) lands second**, once the
   browser no longer depends on fuel for its watchdog. The CLI gains epoch
   interruption in the same change, so no host loses its stop at any point.
3. **Embedded (T3) is deferred** and coupled to board bring-up (#243/#232); it
   confirms the native/board preemption on-target and records the result.

## Consequences

- **The hot path is faster and codegen is simpler.** Every compiled function
  drops its entry preamble; the backend drops a reserved global, a fixed global
  index, and the `spend_fuel` emitter.
- **The MIR is untouched.** Fuel was injected during wasm lowering, never
  represented in MIR, so the removal is confined to the wasm backend and the
  hosts. This confirms the change is localized.
- **"Errors come only from the checker" is preserved.** A stuck program is
  stopped by a host action — a wasmtime epoch trap, a worker `terminate()`, a
  board watchdog reset — in the same class as a `trap`/`first([])` runtime trap,
  never a checker error. Well-typed programs still reach the backend.
- **Reversibility.** This removes a mechanism rather than adding a contract, so it
  is not a one-way door: a host that later needs a software bound adds its own
  (an epoch deadline, a yield-point pass) without the language re-imposing one on
  every other host. The genuine commitment is the stance — *the host owns
  preemption* — which this ADR shares with ADR 0015's "the host owns the loop."
- **The browser's trusted surface shifts, not grows.** The worker boundary is a
  stronger isolation than fuel ever was (a spinning worker is killable; spinning
  wasm on the main thread was not), at the cost of the `OffscreenCanvas` +
  `SharedArrayBuffer` plumbing in §2b.

## Touch-points

Every reference to fuel in the tree, from a full grep of `wasm/src`, `mir/src`,
`goat/src`, `cli/`, and `web/`. (MIR has no fuel reference — confirming §Consequences.)

| Location | What it is | Change |
|---|---|---|
| `wasm/src/lib.rs:36–42` | `FUEL_GLOBAL = 2`, `FUEL_START = i32::MAX` consts + doc | Delete. |
| `wasm/src/lib.rs:415–425` | globals section builds `…chain([FUEL_START, 0])…` | Drop `FUEL_START`; emit only the site global. |
| `wasm/src/lib.rs:46, 50–51` | `SITE_GLOBAL = 3`, `UPDATE_GLOBAL = 4`, `DRAW_GLOBAL = 5` (and the interactive fingerprint / hosted static-base offsets) | Renumber down by one: site→2, update→3, draw→4, etc. All count from fuel at 2. |
| `wasm/src/lib.rs:449` | `exports.export("goat_fuel", Global, FUEL_GLOBAL)` | Delete the export. |
| `wasm/src/lib.rs:1260–1275` | `fn spend_fuel` | Delete. |
| `wasm/src/lib.rs:1295` | `spend_fuel(&mut code)` in `lower_func` (runs on every function body) | Delete the call. |
| `wasm/tests/golden/*.wat` (all 8: apply_double, arithmetic, capturing_closure, conditional, fib, point_sum, string, variant_length) | Each encodes `(global (;2;) … 2147483647)`, `(export "goat_fuel" (global 2))`, the per-function spend preamble, and `goat_site` at global 3 | Regenerate with `UPDATE_GOLDEN=1`; verify each dropped the global, the export, the preamble, and renumbered `goat_site` to global 2. |
| `wasm/tests/emit.rs`, `wasm/tests/text.rs` | golden harness + any `text.rs` assertions on exports/global indices | Re-check assertions after regeneration. |
| `goat/src/native/mod.rs:554–575` | `set_fuel`, `fuel`, `fuel_global` methods on `Guest` | Delete; replace with epoch-deadline configuration on the `Engine`/`Store`. |
| `goat/src/native/mod.rs:16` | `pub use interactive::{…, UPDATE_FUEL}` | Drop `UPDATE_FUEL` from the re-export. |
| `goat/src/native/interactive.rs:7–9` | `pub const UPDATE_FUEL: i32 = 5_000_000` | Delete. |
| `goat/src/native/interactive.rs:171–185` | `fn call` refills fuel, calls, and maps a drained call to "ran out of fuel" | Rewrite: call directly; a runaway call traps via the epoch deadline, surfaced with the stuck message. |
| `cli/tests/interactive.rs:497–541` | `an_update_that_never_returns_runs_out_of_fuel_and_traps`, `refilled_fuel_lets_ordinary_updates_run_many_times`, `fuel_that_is_never_refilled_runs_out` | Rewrite against the epoch deadline: a runaway `update` traps under a deadline; ordinary updates run unbounded. |
| `web/loop.ts:7–10` | header comment describing the fuel watchdog | Rewrite for the worker/terminate model. |
| `web/loop.ts:23` | `FUEL_BUDGET = 5_000_000` | Delete (supervisor deadline replaces it). |
| `web/loop.ts:25, 24` | `STUCK_MESSAGE`, `FRAME_BUDGET_MS` | Keep; move ownership to the supervisor. |
| `web/loop.ts:55–62` | `InteractiveExports.goat_fuel: WebAssembly.Global` | Remove the field. |
| `web/loop.ts:78–81, 88–104` | `refuel()`, and `guarded()`'s refill + `fuel.value <= 0` "spent" check | Replace with the worker call + supervisor deadline; "stuck" becomes "deadline passed," not "fuel spent." |
| `web/loop.test.ts:145–179` | the two fuel tests (runaway stopped by fuel; refilled fuel runs many frames) + the frame-budget test at 181 | Rewrite for the worker supervisor: a runaway worker is `terminate()`d and reported stuck; a well-behaved program runs many frames. |
| `web/scene.ts`, new worker module | scene streaming / canvas wiring | T1 moves draw to an `OffscreenCanvas` in the worker. |
| `docs/adr/0015-host-owned-event-loop-contract.md:136–154, 171–175, 198` | §5, the "fuel-exhausted update" consequence, the "fuel budget" reversible bullet | Add a "superseded by ADR 0021" marker to §5; §5 stays as historical record. |
| `docs/plan.md:680–693` | "Bounded update time: fuel/epoch limits plus a watchdog," and the superloop line | Reword to host-owned preemption. |
| ADR 0019 (PR #243, branch `docs/adr-0019-on-device-wasm-runtime`, **not in master**) | coherence point 4: "its injected-fuel bound is explicitly the MCU mechanism" | Replace per §3 before ADR 0019 is accepted. |

Correction to the brief's touch-point hint: the browser refill-and-"stuck" logic
lives in **`web/loop.ts`**, not `web/runtime.ts` — a grep of `web/runtime.ts`
finds no fuel reference. The tickets are grounded on `loop.ts`.

## Implementation tickets

Sequenced; T1 before T2 is the critical ordering from §4.

- **T1 — Browser Worker supervisor + synchronous frame bridge.** Move goat
  execution into a terminable Web Worker; run the per-frame loop inside the worker
  with `update`/`draw` synchronous; render via an `OffscreenCanvas` transferred to
  the worker; forward DOM input main→worker by `postMessage`; add a main-thread
  supervisor that holds a per-frame (and run-once whole-program) wall-clock
  deadline, reads a one-word `SharedArrayBuffer` progress heartbeat, and
  `terminate()`s + restarts a stuck worker. Lands first; works against today's
  fuel-bearing module. *Acceptance:* a spinning `update` freezes no tab — the
  supervisor reports the stuck message and the page stays live; a well-behaved
  program runs many frames; cross-origin isolation (COOP/COEP from #244) is
  asserted; the web test suite is green.
- **T2 — Remove injected-fuel codegen; CLI epoch; native driver.** Delete the
  `goat_fuel` global, the export, and the per-entry `spend_fuel`; renumber
  globals; regenerate the 8 goldens. Add wasmtime epoch interruption to the native
  `Guest`/`Engine` with an optional CLI `--timeout`, unbounded by default; drop
  `set_fuel`/`fuel`/`UPDATE_FUEL`; rewrite the three native fuel tests against the
  epoch deadline. Lands after T1. *Acceptance:* no emitted module exports
  `goat_fuel`; goldens regenerated and green; a runaway CLI `update` traps under
  `--timeout` and runs unbounded without it; `cargo fmt --all -- --check`,
  `cargo clippy --all-targets -- -D warnings`, `cargo test` green, and the
  compiler crates still build for `wasm32-unknown-unknown`.
- **T3 — Embedded preemption on-target (deferred, coupled to #243/#232).** Confirm
  native host-compilation preemption on the chosen board: a hardware watchdog
  timer by default, and/or compiler-inserted cooperative yield points if a
  software bound is wanted. Record the result. *Acceptance:* a recorded decision
  (an ADR update) that the board's watchdog stops a hung program without
  re-introducing goat-injected fuel. Gated behind the #243/#232 board bring-up —
  the one coupled open item.
