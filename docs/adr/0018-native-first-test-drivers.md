# ADR 0018 — One conformance suite in Rust; each platform a thin native test driver

- Status: accepted (2026-11-07)
- Context: the Phase 10–12 hosts/shells work (`docs/plan.md`), ADR 0015
  (host-owned event-loop contract — "same contract, new transport"), the
  existing differential harness (`cli/tests/support/mod.rs`), the embedded
  target profile (#229/#235), and the Apple editor shell (#108). Recorded as
  the first host beyond the CLI/browser is built, so the test strategy is fixed
  before per-platform suites diverge. Supersedes nothing; it names a pattern the
  differential harness already embodies and makes it the rule for new hosts.

## Context

goat is one language with a growing set of **execution targets**: the
interpreter oracle, wasm under wasmtime (desktop CLI), wasm in the browser
(`goat_web`), the i32/f32 **embedded** profile, and — starting with #108 — a
native Apple shell. Each target runs the *same language*, so a goat program's
observable behavior — what it prints, the scene it draws (ADR 0015's `scene.*`
calls), whether it traps, and the `goat_live_allocs == 0` balance — must be
**identical** across all of them. That sameness is exactly what ADR 0015 fixed
for the runtime ("the same contract must hold on every host"); the open question
is how we *test* that it holds without rewriting the behavior checks once per
platform.

The differential harness already answers this for two targets: it holds one set
of goat programs and runs each through both the interpreter and wasm, asserting
the two agree and that nothing leaks. That is the whole idea, generalized: the
*cases* are platform-agnostic, the *driver* is per-target. The risk if we don't
name it is that each new host (Apple, then a microcontroller) grows its own
hand-written suite in its own language, the suites drift, and a behavior that
holds on the CLI silently regresses on a phone with no test to catch it.

A competing pull is real: the Apple shell is Swift, the browser glue is
TypeScript, and the natural reflex is to test each in its own ecosystem's
framework (XCTest, `node:test`). That reflex is right for the *glue* and wrong
for the *language behavior* — and the two must not be conflated.

## Decision

### 1. Conformance cases live once, in Rust, platform-agnostic

A goat conformance case is `(source, expected observable outcome)` — expected
prints, expected `scene.*` call sequence, expected trap, and `live == 0`. These
cases are **data**, defined one time in Rust (the `goat_cli` test binaries —
`numbers`, `embedded`, `differential`, `stdlib`, `interactive`, … — and the
shared `support` module are where they live today). No target re-expresses a
behavior case in another language. Adding a behavior adds a case here, and every
target picks it up.

### 2. Each target is a thin **driver** over that one suite

A *driver* takes the shared cases and runs each one through its target's **real**
execution path, then asserts the shared expected outcome. "Native-first" means
the driver exercises the actual platform runtime — not a mock, not a
re-implementation of goat's semantics in the host language. Today's drivers:

| Target | Driver | Runs the program by |
|---|---|---|
| interpreter oracle | `interpret_on(profile, …)` | walking MIR directly |
| desktop wasm | the wasmtime harness | compiling to wasm, running under wasmtime |
| embedded profile | `interpret_on(Profile::Embedded, …)` + the embedded differential | the i32/f32 lowering, diffed against desktop |
| browser | `web/*.test.ts` (`node --test`) | loading `goat_web.wasm` and driving the `scene`/event bridge |

A new host adds a driver, not a suite. The Apple shell's conformance driver runs
the shared cases through the native embedding path (#228's `SceneSink`/wasmtime
host, ADR 0015) and asserts the same scene calls the CLI asserts.

### 3. Stay in Rust; drop to native test code only for the irreducible glue

Prefer Rust for the suite **and** for every driver that can be written in Rust —
which is every target that runs through a Rust host (interp, wasmtime, the
embedding driver). A target drops to a platform-native test framework (Swift
XCTest, `node:test`) **only** for the surface that is genuinely not Rust: the
UI, the file open/save, and the native↔runtime bridge. Even there, the split is
strict — the native test covers only the **glue it adds** (does the bridge
forward source and marshal a `scene.*` call correctly), while the **language
behavior** the glue carries stays a case in the Rust suite. A Swift test that
re-asserts "a triangle program draws three lines" is a drift risk and is not
written; the Rust suite owns that, and the Swift layer is tested for forwarding,
not for goat semantics.

## Consequences

- One place defines what goat does; N thin drivers prove each platform does it.
  A new behavior is tested everywhere by being added once, and a per-platform
  regression has a test that was going to run anyway.
- This is ADR 0015's "same contract, new transport" applied to tests: **same
  conformance suite, new driver.** The differential harness stops being a
  one-off and becomes the template every host instantiates.
- The compiler crates stay portable (they already build for
  `wasm32-unknown-unknown`); the Rust suite and Rust drivers impose no new
  native-only dependency on them. Native-only test code (wasmtime driver, Swift
  XCTest) stays in the host that owns it — out of `parser`/`checker`/`mir`/`wasm`
  — mirroring the existing rule that wasmtime/`cc` live only in `goat_cli`.
- Cost acknowledged: a target whose host is not Rust (the Apple shell) needs a
  small amount of native test code for its bridge regardless. The rule bounds
  that code to the glue and keeps it from growing into a parallel behavior suite.
- The genuine one-way door is **where behavior cases live** (one Rust suite) and
  **the suite/driver split**. Which Rust crate holds the cases, and the exact
  driver mechanics per host, are reversible details.
