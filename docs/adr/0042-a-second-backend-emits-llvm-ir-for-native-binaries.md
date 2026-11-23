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
   The generated code keeps no global state: its heap, live count, call-depth
   counter and tail-call spill area live in a `goat_instance` the host allocates,
   and every export takes the table, its context pointer and the instance. So an
   app can embed compiled goat code and run several programs in one process, as
   it can run several Lua states (owner, 2026-11-22). The table and the instance
   both start with a version and only grow at the end. A standalone binary's
   `main` builds the table and the instance itself. `foreign "c"` calls (M5) are
   direct calls and do not go through the table. A trap does not return: the
   host's trap entry leaves generated code, by `longjmp` to the host's call
   site for an in-process host, or by printing and exiting for a standalone
   `main`. After a trap the `goat_instance` is dead, because the trap can fire
   in the middle of an allocation or a reference-count update. The host must
   reset or discard it and never call into it again.
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
   and C3, the RP2040 and the RP2350. A board runs a native build for release
   and WAMR's interpreter for hot-swap development: the board is flashed once
   with WAMR, then takes new wasm modules over serial without reflashing (#119).
   WAMR AOT (ADR 0019, ticket E4) is dropped, since native release builds replace
   it. So goat runs three ways: wasm for development, native for release, and
   WAMR for hot-swap development on boards. Two backends serve all three.
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
- The new one-way door is the native host ABI: the `goat_host` table, the
  `goat_instance` layout rule and the export names. The table stays one-to-one
  with the wasm imports and exports.
- CI runs the native suites on the self-hosted Linux runners (clang installed in
  the job) and on GitHub's `macos-latest`, path-filtered to backend and host
  changes; macOS has no self-hosted runner.

### Reversible

- The trampoline lowering, the spill-area register limits and the exact clang
  floor.
- Which window library the desktop host uses.

### Amendment 2026-11-22: the heap

The generated code now carries the allocator, reference counting and the drop
loop of `wasm/src/allocator.rs`, with the same size classes and the same
checks. Where it differs:

- **Instance.** `goat_instance` grows at its end by `heap_top` (the bump
  offset into the host's region), `allocs` (every allocation, freed or not) and
  `free` (one list head per size class). `INSTANCE_VERSION` is 2. The host gives
  a fixed region, 8-byte aligned, and the allocator traps with the heap-budget
  message when it is used up; it never grows it.
- **Slots.** Every object has ADR 0002's 8-byte header and 8-byte slots, a
  pointer slot holding an `i64`, so a layout's size depends on its slot count
  and not on the target's pointer width (ADR 0010).
- **Drop list.** A dying child's `rc` word cannot hold a native pointer, so it
  holds the child's heap offset divided by 8, and the high 24 bits of `pad` hold
  the id of its drop function, which `drop_loop` switches on in place of a
  function table.
- **Checks.** The double-release and write-after-free traps are always on.
  Poisoning a freed block is behind `EmitOptions::poison_freed`, which defaults
  on in debug builds as the wasm option does.
- **`Addr` and `Retain`.** An address is the offset from the heap base, so the
  embedded profile's 32-bit `Int` holds it on a 64-bit host. An immortal object
  is not in the heap, so its offset is meaningful only on the desktop profile;
  the only user, reload's snapshot, is not on the native backend yet.
- **Foreign strings.** A `foreign` call returns a string as host memory valid
  until the next call, and the generated code copies it into a heap string.

### Amendment 2026-11-22: closures and calls

- **Calling convention.** Every goat function and closure body is `tailcc`,
  and every goat-internal call says so, so a later `musttail` needs no change
  of signature. The exports (`goat_main`) and the runtime helpers keep the C
  convention. A function takes the instance, then (a closure body) its
  environment, then its arguments.
- **Closure object.** `[header][drop id: u32][pad][code: i64][capture slots]`.
  The code word is the body's address as an `i64`, so the layout does not
  depend on the pointer width. A closure carries its own drop id (the high
  bits of `pad` hold it while it waits on the drop list) because its type
  names a signature, not the captures that decide what dies with it. A
  closure that captures nothing is one immortal object and allocates nothing.
- **Call depth.** On the embedded profile each non-tail `CallDirect` and
  `CallClosure` adds one to the instance's `depth` before the call and removes
  it after, and traps with the stack-overflow message past
  `EmitOptions::call_depth` (default 1024), at the same call and with the same
  blamed site as the embedded wasm build. The desktop profile keeps no count.
- **Not yet.** Method sites (`MethodKey`) and the thumbv6m trampoline still
  fall back with a reason.

### Amendment 2026-11-22: tail calls

- **Loops.** A function whose body tail-calls itself, directly or (for a
  closure body) through its own environment, has a `loop` block that holds a
  `phi` per parameter; the tail call branches back to it.
- **Merged groups.** The functions of a strongly connected component of the
  direct-tail-call graph become one `@goat_gN(inst, which, slots...)` with a
  `switch` on `which`. A member's parameters take slots by LLVM type, so
  members with different signatures share registers. A call to a member, tail
  or not, goes to the group's function and names the member in `which`; the
  members have no function of their own. The entry and closure bodies are not
  members.
- **Everything else** is `musttail call tailcc` followed by `ret`, direct or
  through a closure's code pointer.
- **Register rule.** `EmitOptions::abi` gives the integer and float argument
  registers a `tailcc` signature may use. The default is 6 and 8: x86-64's six
  integer registers, and the eight vector registers both desktop targets have
  (aarch64 has eight integer registers, so the default leaves two spare). The
  instance, the environment and `which` count against the integer budget. An
  argument past a class's budget travels as an `i64` word in
  `goat_instance.spill`, which the caller stores after it has evaluated every
  argument and the callee loads before it runs anything. A call that needs more
  than `SPILL_WORDS` (8) words is `Unsupported`.
  `native/tests/ll/tailcc_stack_arguments.ll` keeps the miscompile as a
  regression file; its test prints whether the local clang still has the bug,
  and the rule holds either way. Apple clang 21 (2026-11-22) still miscompiles
  it at -O1 and -O2.
- **No guaranteed tail calls.** `Abi::musttail` is false for thumbv6m: a tail
  call that is not a loop is then `Unsupported`, until the M4 trampoline.
- **Embedded Arm.** The default budget is the 64-bit one. A Thumb-2 build,
  which has four integer argument registers, sets `int_registers` to 4.
