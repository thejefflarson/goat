# goat goes native: MIR → LLVM IR

Status: settled with the owner, 2026-11-22. Decisions recorded in
[ADR 0042](../adr/0042-a-second-backend-emits-llvm-ir-for-native-binaries.md).

## Bottom line

goat gets a second backend. It writes textual LLVM IR (a `.ll` file) from MIR,
and the system clang compiles and links that file into a self-contained,
optimized native binary. No LLVM library is linked into goat: the emitter is a
pure-text crate that still builds for `wasm32-unknown-unknown`.

The wasm backend stays. It serves the web editor, `goat run` on the desktop and
live coding. The native backend serves release binaries: desktop first, then
boards, the RP2040 included. On boards, WAMR's interpreter runs the wasm build
for hot-swap development, so goat runs three ways: wasm for development, native
for release, and WAMR for hot-swap development on boards.

A native binary needs no runtime. The generated code already holds the
allocator, reference counting, the drop loop, traps and the interactive glue;
what remains is a small host library per target, and most of that exists today.

## Questions the owner asked

### Why not WAMR AOT? Do we need Cranelift?

Neither. WAMR AOT (`wamrc`, which is built on LLVM) gives good code and works for
a command-line binary on Linux or an unsigned Mac. These requirements break it:

- **Apple platforms.** WAMR maps AOT code into executable memory at run time with
  `MAP_JIT` (`wamr/vendor/wasm-micro-runtime/core/shared/platform/common/posix/posix_memmap.c`).
  To the OS that is a JIT: a notarized, hardened-runtime macOS app needs the
  allow-jit entitlement, and iOS forbids it. The binary is a loader carrying a
  wasm payload.
- **Calling C libraries directly.** goat's data lives in a 32-bit sandboxed
  linear memory, so every C call is marshalled and a goat buffer passed to C must
  be translated or copied.
- **SIMD.** Only wasm's 128-bit SIMD, and goat builds WAMR with SIMD off.
- **Memory.** 4 GiB at most; WAMR's memory64 is off by default and limited to
  the classic interpreter and AOT.
- **Toolchain.** `wamrc` ships LLVM, so it saves nothing over requiring clang.
- **Debugging.** AOT code sits in an anonymous mapping, so lldb and Instruments
  see no goat symbols.

Cranelift has no riscv32 or thumbv6m backend, so it cannot reach the boards. Its
code quality is about what wasmtime already gives goat today. Its `.o` output
still needs the system linker, which on macOS comes from the same Command Line
Tools as clang.

### Isn't a 30 KB runtime frustrating?

Yes, and RAM matters more than flash.

| | WAMR plus goat's host | Native: goat's host alone |
|---|---|---|
| Runtime code in flash | AOT runtime about 29 KB, fast interpreter about 59 KB (published Cortex-M4F text sizes) | none |
| Heap RAM | whole 64 KiB wasm pages: the RP2040 gets one page, about 56 KiB of heap (ADR 0029) | whatever the board can spare: about 180–200 KiB on the RP2040's 264 KB (estimate) |
| WAMR's own RAM | module, instance and execution-environment structures, plus code copied into RAM; not measured for goat | none; code runs in place from flash |
| Support code | number formatting, 3–20 KB depending on the algorithm (estimate), on both paths | arena, trap, serial write and main loop, about 1–3 KB (estimate) |

For a program the user compiled from their own source, WAMR's extra buys one
thing that is hard to replace: loading new code without reflashing. Boards do
not need that (decision 2 of ADR 0042).

### Why do we need a runtime?

We don't. Checked against the code:

- **Allocation is generated.** `alloc`, `free`, the live count and the drop loop
  are emitted into each module (`wasm/src/allocator.rs`). The native backend
  emits them too. Only the source of memory differs: one reserved region on
  desktop, a static array on a board.
- **Traps** call the host's `trap` with a message. Today the span comes from the
  `goat_site` global and a site table the host decodes (`site_table` in
  `goat/src/native/mod.rs`). Natively the compiler has the source, so it passes a
  ready-made `file:line:col` string, and the host only writes it and exits.
- **Printing numbers** is host behavior today: `print_number` and `write_*` are
  imports, formatted by `goat::format_number`. On desktop the native host links
  that same function, so output matches by construction. Boards need a `no_std`
  port.
- **The vocabulary is a library, not a runtime.** But there is no native window
  host yet: `goat/src/native` and `canvas/src/native.rs` are headless wasmtime
  embeddings, and the only window is the Swift app's WKWebView. A native window
  is new code (M2).
- **Also generated already:** the call-depth counter of ADR 0026 and the
  interactive glue (event constructors, the `draw` streaming, snapshot and
  refresh), which are MIR functions in `mir/src/mono/interactive.rs` and
  `mir/src/mono/reload.rs`.

What stays hand-written per target is `main` and the host loop, the memory
region, the trap, number formatting and the vocabulary bindings: a few hundred
lines, mostly the existing Rust `Host` implementations.

### Don't we skip the sandbox and the rest of WAMR?

Yes. goat is memory-safe by construction, so the sandbox only guards against
compiler bugs. The MIR verifier (which already runs in release), checked builds
and a nightly sanitizer job take that job over. The rest of what WAMR provides:

| Need | Desktop native | Board native |
|---|---|---|
| Stop a runaway loop (ADR 0021) | nothing generated: Ctrl-C kills the process; a windowed host runs goat on a worker thread with an optional watchdog thread | the hardware watchdog, kicked between `update` calls |
| Stack overflow | the ADR 0026 depth counter, with goat on a thread that reserves a large stack; the OS guard page is the backstop | the same counter with the board's `call_depth` |
| Load code without reflashing | not needed: live coding stays on wasm | WAMR's interpreter runs the wasm build for hot-swap development (#119); the native build is the one you flash and keep |
| Hot reload | deferred; a dylib swap works later because the ADR 0035 snapshot is self-describing | not applicable |

## Approaches

| | MIR → textual LLVM IR, clang (chosen) | MIR → C, clang or gcc | MIR → Cranelift | WAMR AOT |
|---|---|---|---|---|
| Tail calls | guaranteed by `tailcc` + `musttail` on x86-64, aarch64, Thumb-2 and RISC-V; a failure is a compile error | not guaranteed; GCC added `musttail` only in version 15 | guaranteed on 64-bit | guaranteed |
| Semantics | explicit: undefined behavior only where the IR opts in | pinned by flags and builtins | explicit | wasm |
| Targets | desktop, iOS, RISC-V, Thumb | everything | 64-bit only | WAMR's |
| Code quality | LLVM -O2 | LLVM or GCC -O2 | about today's | LLVM, sandboxed |
| Readability of output | lower | higher | low | n/a |
| Version drift | real: pin a range and test it | low | pinned crate | n/a |

C's one remaining advantage is GCC-only targets such as Xtensa, and no goat
board is one. Linking the LLVM library (`llvm-sys`) was rejected: the version pin
would become a build dependency of goat, and the emitter could not build for
wasm32.

## What was verified locally

Apple clang 21.0.0 on arm64 macOS, 2026-11-22:

- Mutual recursion between `tailcc` functions with different signatures, joined
  by `musttail`, ran 100,000,000 deep in constant stack. An indirect,
  closure-style loop ran 300,000,000 iterations at -O0 and -O2.
- The same IR compiles for `x86_64-unknown-linux-gnu`, `aarch64-apple-ios`,
  `thumbv7m` and `thumbv8m.main` (Cortex-M33, the RP2350).
- `thumbv6m` (Cortex-M0+, the RP2040) fails every non-self `musttail` with
  "failed to perform tail call elimination". LLVM's ARM backend has no tail calls
  on Thumb-1.
- Apple clang has no RISC-V backend, so the ESP32-C3 and C6 need an upstream
  clang.
- At -O1 and above on aarch64, a `tailcc` function with stack arguments returns
  without popping them, and the caller crashes (SIGBUS at depth 10). At -O0 it is
  correct, and register-only signatures are correct at -O2.
- `frem` lowers to `fmod`, which is exact. Functions not marked `nounwind` pull in
  `__aeabi_unwind_cpp_pr0` on Arm.

## Decisions

D1–D6, D8 and D10 are recorded in ADR 0042; the rest are working decisions for
the milestones.

- **D1. Two backends.** Wasm and MIR → textual LLVM IR, compiled by clang with
  `clang -x ir`.
- **D2. Crates.** `goat_llvm` is the emitter: pure text, depending only on
  `goat_mir`, so it is a compiler crate under the wasm32 rule.
  `goat::compile_ll(profile, source, host) -> String` sits beside `compile`.
  `goat_native` is native-only: the host adapter, the clang invocation and a
  dlopen test driver; it builds as an rlib and a staticlib.
- **D3. No runtime; a host table.** `goat_main`, `goat_setup`, `goat_update`,
  `goat_draw` and the rest mirror the wasm exports and use the C calling
  convention. Host calls go through a `goat_host` struct of function pointers
  named one-to-one after the wasm imports, so the test driver plugs in the
  existing Rust `Host` implementations. User `foreign "c"` declarations become
  direct calls later.
  **Layout (v1).** `goat_host` is `{ u32 version, then one function pointer
  per name in goat_llvm::HOST_FUNCTIONS }`; every entry takes the `ctx` the
  export received first, a string is a pointer and a `u64` byte length, and a
  frame (`scene_frame`) is the bytes of `mir/src/frame.rs`. `goat_instance` is
  `{ u32 version, live, depth, site_start, site_end; ptr heap; u64 heap_size;
  ptr host, ctx; [8 x u64] spill }`, laid out as C does. `goat_main(host, ctx,
  inst) -> i32` returns 1 or 2 when the table or the instance is older than the
  code. `goat_native` mirrors both and a test compares offsets with clang's.
- **D4. Tail calls.** On every target, a self tail call becomes a loop (a direct
  call to the same function, or a closure calling itself through its own `env`),
  and a group of mutually recursive functions joined by direct tail calls merges
  into one function that switches on which member to run. The remaining tail
  calls use `musttail call tailcc` where the target guarantees it. On a target
  without guaranteed tail calls (thumbv6m), a remaining tail call stores its
  target and arguments and returns, and the nearest non-tail call site runs a
  dispatch loop until no call is pending. Every `tailcc` signature keeps its
  arguments in registers; extra arguments go through a static spill area, which
  sidesteps the aarch64 stack-argument bug and RISC-V's late stack-argument
  support.
- **D5. Layouts.** One named struct type per MIR layout; offsets come from each
  target's data layout, and the `.ll` file carries no triple or data layout. The
  object header (ADR 0002), string layout and ADR 0010 identity are unchanged.
  Closures hold real code pointers. `Addr` and `Retain` use an offset from the
  heap base, so the embedded profile also runs natively on a 64-bit desktop.
- **D6. Semantics spelled out in IR.** No `nsw`, `nuw`, fast-math, `contract` or
  TBAA. `Int` `+ - *` use `llvm.s{add,sub,mul}.with.overflow` and branch to the
  spanned trap. `sdiv` and `srem` guard a zero divisor and MIN / −1. `fptosi`
  keeps goat's range guard. Every function is `nounwind`. clang verifies the IR
  as it parses, so an emitter bug fails the build.
- **D7. Checked and release builds.** Checked builds (RC checks and
  poison-on-free) run in every test. Release builds follow the poison policy the
  owner sets for wasm.
- **D8. Targets.** Live coding stays on wasm. Native covers macOS and Linux
  first, then the ESP32-C6 and C3 (RV32) and the RP2040 and RP2350, for release
  builds. WAMR's interpreter stays the hot-swap development path on boards
  (#119). WAMR AOT (ADR 0019, ticket E4) is dropped.
- **D9. Preemption and stack.** As in the table above: nothing generated for
  preemption, the depth counter everywhere.
- **D10. Toolchain floor.** LLVM 17 or later on desktop (opaque pointers only;
  Apple clang from Xcode 15). Boards use a pinned upstream clang with RISC-V and
  Arm, LLVM 22 or later recommended. CI runs the floor and the latest clang on
  Linux and Apple clang on macOS. A regression test keeps the stack-argument
  `.ll` from the checks above.
- **D11. Debug info.** None in M1; line tables from goat spans in M3.
- **D12. No C emitter**, unless a GCC-only board becomes a target.

## Linking into board SDKs

goat compiles the `.ll` to an object and wraps it as a static library; the SDK's
own GCC build and linker scripts do the final link. Pin per board: `-march`
(C3 `rv32imc`, C6 `rv32imac`, RP2040 `thumbv6m`, RP2350 `thumbv8m.main`),
`-mabi=ilp32`, and the float ABI the SDK uses. Emit `nounwind` everywhere and
avoid compiler-rt-only helpers that libgcc lacks; the embedded profile's `i32`
and `f32` keep this to soft-float helpers libgcc has, plus `fmodf`.

## Risks

- **`tailcc` maturity.** One miscompile found already. The register rule, the
  three-way differential (interpreter, wasm, native), a nightly sanitizer job and
  a 10^8-deep recursion test on every target guard it.
- **IR drift across clang versions.** The CI range and a conservative IR subset
  guard it.
- **The trampoline on thumbv6m** costs a store, a return and a dispatch per
  remaining tail call. How often it fires after loops and merging is unmeasured;
  M4 measures it on the examples and fuzz programs.
- **Deep non-tail recursion** traps at different depths under wasmtime and native
  desktop. Those cases are tagged resource-bound; the embedded profile stays
  exact.
- **The speed gain** was unmeasured here; see "Results: the particles
  benchmark" below.
- **Packaging.** The CLI finds `libgoat_native.a` next to its own executable or
  through `GOAT_NATIVE_LIB`. A missing clang gets an actionable message.

## Results: the particles benchmark

Measured for issue 589 with the method of
[the record-arithmetic study](../design/record-arithmetic-performance.md): the
1,000, 10,000 and 100,000 particle programs (`examples/bench/particles.goat` and
`particles_flat.goat`), median of 300 frames after 30 warm-up frames, Apple M1
Pro, Apple clang 21.0.0 at `-O2`, against wasmtime 50.0.2 and V8 14.6 (node
v26.13.1) in the same session. Machine load was 7 to 11 (1-minute average, 10
cores) after being 28 to 45 earlier; two runs agree within 5%. The harness is
`goat/examples/record_arith_bench.rs --native`, outside CI.

Update + draw, microseconds per frame (1,000 particles, nested records):

| | wasmtime | V8 | native -O2 |
|---|---|---|---|
| update | 79.5 | 40.7 | 25.8 |
| draw | 129.5 | 166.8 | 82.9 |

- Update is 3.1x to 3.6x faster than wasmtime and 1.6x to 2.0x faster than V8
  across 1,000 to 100,000 particles and both layouts. Draw is 1.5x to 1.6x
  faster than wasmtime and about 2x faster than V8; most of it is the host
  decoding the frame, which the backend does not change.
- Allocations per frame match: 4,002 in `update` for the nested program (the
  figure the wasm module had after the reuse and static-cell work) and 3,002 for
  the flat one; `draw` makes 4 per shape plus the batching buffer's doublings.
  Both engines end with zero live blocks.
- Compile time for the nested program: 11-15 ms goat to `.ll` (583 KB), 0.69 s
  for `clang -O2`, against 14 ms goat to wasm. Native pays for its speed with a
  second-scale build, which is why live coding stays on wasm.

The full table, the allocation counts and the reading are in the study.

## Milestones

- **M1, one sprint: a standalone run-once binary on macOS and Linux.**
  `goat build --native` turns a run-once turtle program into a binary whose SVG is
  byte-identical to `goat run -o`. Every existing suite passes under
  `GOAT_RUNTIME=native`, beside the existing `wamr` switch. Interactive programs
  run headless through the driver. The particles benchmark is timed against
  wasmtime.
- **M2: a windowed interactive binary.** A native window host (minifb with
  tiny-skia, or AppKit), goat on a worker thread, and the stuck-update watchdog.
- **M3: hardening.** Line tables, nightly fuzzing on native, the sanitizer job and
  the release profile.
- **M4: boards.** C6, then C3, RP2040 and RP2350, with a pinned upstream clang,
  the SDK link above and the thumbv6m trampoline. WAMR stays the hot-swap
  development path.
- **M5: the Julia path.** Direct `foreign "c"` calls first; SIMD only after a flat
  `Float` array exists, which is a language decision of its own.

## Deferred

Native hot reload, a JIT, Windows, linking into iOS apps, a bundled toolchain,
SIMD and flat arrays, and a C emitter. Nothing in M1–M4 needs them, and nothing
above rules them out.
