# ADR 0026 — Embedded profile: a fixed heap arena, a call-depth bound, default-size pages

- Status: accepted (2026-11-09)
- Decision: on the embedded profile (ADR 0017) the wasm module owns a **fixed heap
  arena** with a declared byte budget and never calls `memory.grow`; calls that wait
  on a result nest at most a declared **call depth**; memory uses the default 64 KiB
  page. Running past the heap budget or the depth bound is a **runtime trap** with a
  message, raised through the same `goat.trap` import as the `trap` builtin
  (ADR 0023), never a checker error and never a compiler panic.
- Context: Phase 12 (`docs/plan.md` "Microcontrollers"), ADR 0019 ticket E5. The
  desktop allocator grows memory a page at a time with no ceiling, and wasm's own
  stack limit is whatever the host runtime configures. A microcontroller has a few
  hundred KiB of RAM in total, so the embedded profile needs both bounds declared in
  the module, where a CI run under wasmtime or the `wamr` driver can prove them with
  no board.

## The heap: size-class pools inside one arena

The allocator keeps its three functions (`alloc`, `free`, `goat_live_allocs`) and its
size-class free lists (`wasm/src/allocator.rs`). On the embedded profile the bump
region that feeds the free lists ends at `heap_start + heap_bytes` instead of growing:
`alloc` traps with `the program ran out of memory` when a fresh block would pass that
end. Memory is declared with `minimum == maximum` pages covering the arena, so a
runtime that tracks the declared maximum can reserve all of it up front.
`EmbeddedLimits::default()` declares 256 KiB; `emit_with_limits` takes another.

The plan's second strategy was "fixed-size pools per object size". Two ways to build
it:

| | Size-class free lists over a fixed arena (chosen) | Arena pre-partitioned into one region per size class |
|---|---|---|
| Sizing input | one number, the byte budget | a budget per class, which means knowing the program's object-size mix |
| Fragmentation | a freed block serves only its own class, as on desktop | none across classes, but an idle class's region is dead weight |
| Code | the desktop path with the growth step swapped for a bound | a second allocator |

We chose the left column. Goat objects come in a handful of sizes (every record,
variant and closure is a multiple of 8 bytes), so free lists recycle blocks well, and a
per-class split needs a static analysis of the program that nothing needs yet. A block
freed by a loop is reused by the next iteration, which is what lets a long-running
`update` run in a small arena (tested with a 1 KiB budget and 100000 iterations).
Revisit with per-class regions if a real board shows class-mix fragmentation.

`free` still poisons freed blocks with `memory.fill`, so the board floor keeps
bulk-memory (ADR 0019). A poison-free allocator would drop that requirement; it is not
part of this decision.

## The stack: a depth counter, not a byte count

Wasm gives a module no way to read its stack pointer, and the byte size of a frame
differs by runtime (wasmtime, WAMR classic, WAMR fast, AOT). So the embedded profile
bounds **calls waiting on a result**: each non-tail `CallDirect` / `CallClosure` adds
one to a global before the call and removes it after, and traps with
`the program called itself too deeply` when the count passes `call_depth` (default
1024). A tail call replaces its frame and does not count, which keeps the loops goat
writes as tail calls unbounded in time and constant in depth. The iterative drop loop
runs in constant stack, so it is outside the count.

The counter costs a few instructions per non-tail call and exists only on the embedded
profile. The depth bound is a proxy: the host must still give the interpreter enough
stack for `call_depth` frames, and on a board that is a link-time choice.

Where the trap lands: both traps go through `goat.trap`, so a host that reads
`goat_site` blames the last user call into the prelude (ADR 0023). A trap with no site
(deep recursion in user code that never called the prelude) shows the message alone.
The `wamr` driver does not read `goat_site` yet, so under WAMR a trap carries its
message but no range.

## Custom page sizes: checked, not used

`wasmtime` 50 runs modules with a custom page size once `wasm_custom_page_sizes` is
enabled; WAMR 2.4.5 refuses to load them on either interpreter. Because the board
runtime is WAMR (ADR 0019), the embedded heap uses the default 64 KiB page and gets its
byte-level budget from the allocator's arena end, not from the page size. Both facts are
pinned by tests (`cli/tests/embedded_limits.rs`, `wamr/tests/custom_pages.rs`); the WAMR
one fails if an upgrade starts loading custom pages, which is the signal to reconsider.
The cost of the fallback is that memory is a whole number of 64 KiB pages, so the
arena's declared end is a bound and the module's `memory` is rounded up past it.

## WAMR's per-function cell limit (ADR 0025)

The embedded profile has one more documented limit: WAMR's fast interpreter refuses at
load any function whose locals, operand stack and constants exceed **32767 cells**; its
classic interpreter has no such cap. goat emits such a function unchanged. The `wamr`
driver links both interpreters (WAMR picks its interpreter at compile time, so the build
produces a second copy of the runtime with every global symbol renamed
`goat_classic_*`) and `interp_for` chooses classic for a module with a function whose
parameters, locals and two cells per operator pass the limit. That bound errs toward
classic, which runs everything the fast interpreter does. A differential case
(`differential::a_chain_of_thousands_of_bindings_runs` under `tests/wamr.rs`) checks that
the fast interpreter refuses the chain, the driver runs it on classic, and the output
matches the oracle. No function-splitting pass is built.

## Consequences

- A program that fits a desktop can trap on the embedded profile for lack of heap or
  depth. The differential suite on `GOAT_PROFILE=embedded` therefore fails, besides the
  width differences in `cli/tests/embedded.rs`, on the tests that build
  million-element structures.
- The interpreter and the desktop profile have no budget: only compiled embedded wasm
  traps, so the interp==wasm oracle asserts only that a program which exceeds a budget
  traps, with the message.
- The defaults (256 KiB, depth 1024) are placeholders until a board sets them. They are
  fields of `EmbeddedLimits`, so a CLI flag or per-board config can supply real ones.
