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

### Amendment 2026-11-22: traps, interactive programs and the desktop stack

- **Trap text.** Generated code passes the trap entry the bare message, and the
  host reads the blamed range from the instance's `site_start` and `site_end`
  and renders it against the source it holds. goat_native's `Stopped` carries
  both, and `goat::render_trap` words them (`trap: 2:1: first of an empty
  list`, with the source line) exactly as the wasm CLI does. The emitter never
  sees the source: embedding line and column text in the code would cost flash
  on a board and tie the binary to one file, so the pre-rendered form is the
  host's to build.
- **Instance version 3.** The instance grows at its end by `update`, `draw`,
  `sites` and `reason` (the closures `goat_setup` stores and the reason of a
  failed refresh), `frame`, `frame_len` and `frame_cap` (the frame buffer) and
  `stack_limit`. All start null or zero.
- **Interactive exports.** An interactive program has no `goat_main`. It
  exports ADR 0015's names, each taking `(host, ctx, instance)` first and
  returning a zero value without running when either struct is older than the
  code: `goat_setup`, `goat_update`, `goat_draw`, `goat_release_model`,
  `goat_shutdown`, `goat_snapshot`, `goat_refresh`, `goat_reason_part`,
  `goat_free_static` (a no-op: static data lives in the library) and
  `goat_event_<Tag>`, plus `goat_alloc` for the host's strings, `goat_attach`
  (the version checks alone, returning a status) and `goat_subscriptions` (the
  event labels, NUL-separated and closed by an empty one). The embedded profile
  stays out, as it is for wasm.
- **Frames.** `draw` encodes into the instance's `frame` block through
  `frame_reserve`, `frame_reset` and `frame_present`, which follow
  `wasm/src/frame.rs`, and `present` calls the table's `scene_frame` once. The
  bytes are `mir/src/frame.rs`'s, so a host replays them with the same decoder
  it uses for wasm.
- **Method sites.** `MethodKey` compares the closure's code word with each
  site function's address and yields the key's string constant, or traps with
  "this closure is not a method".
- **Reload.** Two modules run over one instance. The fields a module keeps
  (`update`, `draw`, `sites`, `reason`) are saved per module by the host and put
  in the instance around that module's calls (`ModuleState`), the way each wasm
  module has its own globals. The old library is unloaded after
  `goat_shutdown` and `goat_free_static`. A trap during a reload kills the
  instance, so the reload fails; a wasm reload would carry on with a reset.
- **Desktop stack.** The desktop profile traps with the stack-overflow message
  when the stack pointer is below `stack_limit`, checked at each non-tail call
  by comparing `llvm.frameaddress` with the field. The host sets the limit
  before every call into generated code to the low end of the calling thread's
  stack plus 256 KiB, which leaves room for the host functions the program
  calls and for the frame that trips the check (`goat_native::stack`, from
  `pthread_getattr_np` or `pthread_get_stackaddr_np`). A null limit turns the
  check off. This replaces "the desktop profile keeps no count" above and
  blames the same site as wasm. The embedded profile keeps the depth counter.
  - Why not a depth counter: the stack a call needs depends on the callee's
    frame, so a bound derived from the stack's size is either too small for
    shallow frames or too large for fat ones; the address is exact.
  - Why not a guard-page handler: it needs a process-wide signal handler, which
    an embedding application may own, and leaving a faulting frame by `longjmp`
    from a signal handler is not defined for the code the fault interrupted.
  - Cost: one load and one compare per non-tail call, and a frame pointer in
    functions that call.
- **Preemption.** M1 has none: the timeout of ADR 0021 is wasmtime's epoch,
  and a native loop that never returns runs until the host kills the process.
  A host that needs one runs the program on its own thread.

### Amendment 2026-11-23: the macOS window host

An interactive program built with `goat build --native` opens an AppKit window
on macOS (owner, 2026-11-23: platform-native, not a cross-platform Rust windowing
stack; Linux gets its own thin host later, behind the same `goat_host` table).
Everywhere else the build still refuses, saying the window host is macOS only.

- **Swift, linked by `swiftc`.** The host is Swift (`native/appkit/`). `goat build`
  compiles the program's IR and a generated `entry.c` with clang, then has `swiftc`
  compile the host and link everything with `libgoat_native.a`, so the Swift
  runtime links with no extra step. Objective-C was not needed. The Swift files
  and the C header ship inside `goat_native` as strings (`goat_native::appkit`), so
  the `goat` executable needs no files beside it other than the library.
- **Who does what.** Rust runs the program; Swift draws and takes input.
  `goat_native::session` starts a worker thread with its own `goat_instance`,
  runs `setup`, `update` and `draw`, delivers a frame event every 16 ms and each
  key or pointer event through the program's `goat_event_<Label>` constructors,
  and hands the host one `scene.frame` buffer per `draw`. The entry code gives the
  session the exports as a `GoatProgram` table: the exports `goat_llvm` emitted are
  found by name only in the generated `entry.c`, so the shared staticlib never
  references a symbol a non-interactive program lacks. The session knows both the
  canvas labels (`Frame`, `KeyPress`, `MouseMove`, ...) and the turtle's (`Tick`,
  `KeyDown`, `PointerMove`, ...); `goat build --native` picks the canvas
  vocabulary from the names the program uses, and `--canvas` or `--turtle`
  overrides that.
- **Drawing.** `Frame.swift` ports `mir/src/frame.rs`'s decoder. The buffer is
  the program's output, so every read is bounds-checked, a malformed frame is an
  error, and colors pass the same alphanumeric-or-`#` rule as `check_color`.
  `Painter.swift` follows `web/scene.ts` with Core Graphics.
- **Trap.** The trap entry in the table reports the rendered message
  (`goat::render_trap`) to the host and parks the worker for good; the window
  shows the message over the picture.
- **Watchdog (ADR 0021).** The session times each call into the program on a
  separate thread. A call that outlives its budget (one second, ten for `setup`;
  `$GOAT_STUCK_MS` replaces the first) is reported as stuck and its thread is
  parked with a signal, since a thread spinning in generated code cannot be asked
  to stop. The process stays up and shows the message.
- **Headless mode.** The binary accepts `--headless N [--key K]... [--png FILE]`,
  which runs without a window, prints the last picture's shapes and exits; a trap
  or a stuck call prints its message and exits 1. The tests drive it, since a
  window needs a display.
- **App bundles (ADR 0043).** When `-o` ends in `.app`, `goat build --native`
  writes `Contents/MacOS/<name>` (this same host), an `Info.plist`
  (`local.goat.<slug>` identifier, macOS 13.0 minimum, high-resolution capable),
  and a default `AppIcon.icns` that `goat_native::appkit::ICON` carries, then signs
  the bundle ad hoc with `/usr/bin/codesign --force --sign -`. A run-once program
  refuses `.app`, as does a non-macOS host.
