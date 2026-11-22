# ADR 0042 — A second backend emits LLVM IR for native binaries

- Status: accepted (2026-11-22)
- Supersedes: the "one backend: WebAssembly" decision in `docs/plan.md`
  ("Platform and backends").
- Resolves: [ADR 0019](0019-on-device-wasm-runtime.md) §B3, the fork between
  wasm→C and a direct native backend.
- Amends: [ADR 0019](0019-on-device-wasm-runtime.md) (WAMR AOT, ticket E4, is
  dropped; boards are native) and
  [ADR 0029](0029-embedded-bring-up-boards-and-ci-gate.md) (the RP2040 is a
  native target).
- Builds on: [ADR 0002](0002-object-header.md) (object header),
  [ADR 0010](0010-mono-layout-identity-for-width-polymorphic-variants.md)
  (layout identity), [ADR 0013](0013-sequencing-boolean-operators-and-loops.md)
  (loops are tail calls), [ADR 0015](0015-host-owned-event-loop-contract.md)
  (the export contract), [ADR 0018](0018-native-first-test-drivers.md) (one
  suite, thin drivers), [ADR 0021](0021-host-owned-preemption.md) (hosts own
  preemption), [ADR 0026](0026-embedded-heap-budget-and-bounded-stack.md)
  (heap budget and call depth).
- Design note: [`docs/ideas/native-backend.md`](../ideas/native-backend.md).

## Context

Every goat program runs as wasm under a runtime: wasmtime, a browser engine or
WAMR. The owner wants self-contained, optimized native binaries, and room later
for SIMD and direct calls into C libraries.

Wrapping wasm does not get there. WAMR AOT loads machine code into executable
memory at run time, which Apple treats as a JIT (an entitlement on a notarized
Mac, forbidden on iOS). It also keeps goat's data in a 32-bit sandboxed memory,
so every C call is marshalled. Cranelift has no riscv32 or thumbv6m backend, so
it cannot reach the boards. Emitting C leaves tail calls to the C compiler, which
guarantees none, and goat's loops are tail calls (ADR 0013).

LLVM guarantees tail calls with the `tailcc` calling convention and `musttail`,
and makes a call it cannot honor a compile error. Checked locally with Apple
clang 21: `tailcc` mutual recursion with differing signatures ran 10^8 deep in
constant stack on aarch64, and the same IR compiles for x86-64 Linux, iOS and
Thumb-2. Thumb-1 (thumbv6m, the RP2040's Cortex-M0+) has no tail calls in LLVM.
At -O1 and above on aarch64, a `tailcc` function with stack arguments fails to
pop them on return.

## Decision

1. **Two backends.** Wasm stays for the web editor, desktop `goat run` and live
   coding. A second backend lowers MIR to textual LLVM IR, which clang compiles
   and links (`clang -x ir`) into native binaries. goat links no LLVM library.
2. **The emitter is a compiler crate.** `goat_llvm` is pure text, depends only on
   `goat_mir`, and builds for `wasm32-unknown-unknown`. Native-only work (running
   clang, the host library, the test driver) lives in a separate `goat_native`
   crate.
3. **No runtime.** The generated code carries the allocator, reference counting,
   the drop loop, traps and the interactive glue, as the wasm backend's does. The
   exports keep ADR 0015's names, use the C calling convention, and reach the
   host through a `goat_host` table of function pointers named one-to-one after
   the wasm imports. Each target supplies a host library: `main` and the loop,
   the memory region, the trap, number formatting and the vocabulary bindings.
4. **Tail calls.** On every target, a self tail call becomes a loop, and a group
   of functions joined by direct tail calls merges into one function that
   switches on the member to run. A remaining tail call is `musttail call tailcc`
   where the target guarantees it; on a target that does not (thumbv6m), it stores
   its target and arguments and returns to a dispatch loop at the nearest
   non-tail call site. A `tailcc` signature keeps its arguments in registers and
   passes any extra through a static spill area, because of the aarch64 bug above.
5. **Layouts.** One named struct type per MIR layout, with offsets from the
   target's data layout; the `.ll` names no triple. ADR 0002's header, the string
   layout and ADR 0010's identity are unchanged. Closures hold code pointers.
   `Addr` and `Retain` use an offset from the heap base.
6. **Semantics are explicit in the IR.** The emitter never writes `nsw`, `nuw`,
   fast-math flags, `contract` or TBAA. Integer `+ - *` use the
   `llvm.s*.with.overflow` intrinsics and branch to the spanned trap; division
   guards a zero divisor and MIN / −1; every function is `nounwind`.
7. **Targets.** Native covers macOS and Linux desktop first, then the ESP32-C6
   and C3, the RP2040 and the RP2350. Boards are native-only. WAMR AOT (ADR 0019,
   ticket E4) is dropped. The existing WAMR code stays, with no new work, until
   native boards run; the owner then decides whether to remove it. Board live
   coding is not a goal; the compiler still emits wasm for anyone who wants it.
8. **Toolchain floor.** LLVM 17 or later on desktop, the first release with only
   opaque pointers (Apple clang from Xcode 15). Boards use a pinned upstream
   clang with RISC-V and Arm, because Apple clang has no RISC-V backend. CI runs
   the native suites on the floor and the latest clang.

## Consequences

- The conformance suite gains a third execution path, `GOAT_RUNTIME=native`,
  beside the interpreter and wasm (ADR 0018). The three must agree on prints,
  scene calls, traps and live allocations.
- Deep non-tail recursion traps at different depths under wasmtime and native
  desktop; those cases are tagged as resource limits. The embedded profile uses
  the same depth counter on both and stays exact.
- A native build needs clang on the machine. On a Mac that is the Command Line
  Tools; `goat build --native` says so when it is missing.
- A board on the native path gets its whole spare RAM as heap rather than whole
  64 KiB wasm pages, and carries no runtime in flash.
- The new one-way door is the native host ABI: the `goat_host` table and the
  export names. It stays one-to-one with the wasm imports and exports.

### Reversible

- The trampoline lowering, the spill-area register limits and the exact clang
  floor.
- Which window library the desktop host uses.
- Removing the WAMR code, which the owner decides after native boards run.
