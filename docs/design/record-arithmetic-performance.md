# Where a record-arithmetic frame spends its time

Measurement for issue 544. It recommends; it decides nothing. A SIMD backend is a
one-way door on the codegen, so that call belongs to the owner.

## Question

The owner's aspiration is that goat could become "a sort of Julia" for graphics:
numeric work that scales with SIMD. Today `a + b` on records is a plain MIR
function derived by mono (`mir/src/mono/structural.rs`). It loads each field,
operates, and allocates a fresh reference-counted record for the result. No SIMD
exists anywhere (ADR 0019 builds WAMR with `WASM_ENABLE_SIMD=0`). Before anyone
designs `f64x2` lowering, where does a frame's time actually go?

## Answer in one paragraph

Field arithmetic is about 1% of a frame's update step. Between half (measured
directly: a flat-record rewrite that removes 4 of 7 records per particle saves
48%) and about 85% (estimated, if every record costs the same) is the lifecycle
of heap records: allocate, initialise, reference-count, drop through a
type-specific destructor, free. Drawing adds a host call per shape that costs
more than the whole update. A float-record `f64x2` path, patched by hand into the
two derived functions of the real compiled module, moved a frame by -3% under
wasmtime and by nothing measurable under V8. Poisoning every freed block costs
a quarter of the update step in both engines and is a one-line policy change.
Unboxing small records and reusing dead records each remove most of the rest.
SIMD pays only after the data stops being boxed records, which is a language
feature (flat float arrays), not a codegen flag.

## Method

Machine: Apple M1 Pro, 10 cores, macOS (Darwin 27.2.0), not otherwise isolated
(repeat runs differ by about 3%).
Toolchain: rustc 1.99.1, wasmtime 50.0.2 (Cranelift, the engine the native host
embeds), node v26.13.1 with V8 14.6 (the engine behind Chrome; Safari and Firefox
differ). Source at commit `b02695a`. All builds are `--release`.

Benchmark: `examples/bench/particles.goat` is a canvas program with 1,000
particles, each `{p: {x, y}, v: {x, y}}`. Each `Frame` event runs `step` over the
list with the prelude's `change_each`: `p = q.p + q.v` (record `+`),
`v = q.v * {x: 0.999, y: 0.999}` (record `*`, damping), and a bounce off the
canvas edges (four float comparisons, two negations). `draw` returns one `Dot`
per particle, so a frame is `update` then `draw`.

Two harnesses time the same modules, the same way: `Frame` event construction
plus `goat_update`, then `goat_draw`; 30 (wasmtime) or 100 (V8) warm-up frames,
then the median of 300.

- Native: `goat/examples/record_arith_bench.rs` under wasmtime. The sink counts
  shapes and keeps nothing, so host cost here is the lower bound.
- V8: `web/record-arith.bench.ts` under node, with `scene.circle` going through
  the web runtime's own `sceneImports` (string read, color allow-list regex,
  finite check) into a counting scene. No canvas is touched.

Neither harness paints pixels. Real canvas work comes on top of the "host call"
rows below in a browser.

No sampling profiler could attribute time inside JIT-compiled wasm here (the
module has no name section and wasmtime's perf-map output needs Linux `perf`).
So the breakdown comes from three techniques that need no symbol table:

1. **Variants.** The harness rewrites the `step` block (or `draw`, or the
   particle count) and differences the times. For example `list-only` steps with
   `step = program(q) do q done`, which is pure list machinery.
2. **Exact counts.** The emitted wasm was disassembled (`wasm-dis`), a counter
   added to the allocator and free functions, and reassembled (`wasm-as`). One
   update frame of the full benchmark runs 7,002 allocations and 7,002 frees:
   seven per particle, five from `step` (the `+` result, the `{0.999, 0.999}`
   literal, the `*` result, the new `v`, the new particle) and two list cells
   (`change_each` builds a reversed list, then `reverse` builds another). One
   `draw` runs 4,000 (a `Dot` record, its payload, two list cells).
3. **Hand-patched wasm.** The same disassemble-edit-reassemble loop replaced the
   body of a function with a variant: no poison fill, or `f64x2` arithmetic in
   the derived `+` and `*`. The edited module runs unchanged otherwise, so the
   effect is isolated on the real code.

The cost of one record is inferred by differencing variants that differ in record
count, assuming each record costs about the same. That assumption is the weakest
link in the percentages below.

## Results

### Frame time

Microseconds per frame, 1,000 particles, median.

| variant | what it isolates | wasmtime update | V8 update |
|---|---|---|---|
| `full` | the benchmark | 147 | 88 |
| `list-only` | `step = q`: list traversal, two list cells per particle | 54 | 27 |
| `add-only` | `+` on records, 2 records per particle beyond the list | 91 | 53 |
| `mul-only` | `*` on records, 3 records per particle | 116 | 82 |
| `scalar-add` | same sum written per field, 2 records | 92 | 54 |
| `scalar-full` | whole step per field, 3 records | 114 | 68 |
| `scalar-heavy` | `scalar-full` plus about 15 more float ops, 3 records | 115 | 70 |
| `hoisted` | damping literal bound at top level, 6 records | 142 | 84 |
| `flat` | one flat 4-field record per particle, 3 records incl. list cells | 77 | 40 |

`draw`, the same runs:

| variant | wasmtime draw | V8 draw |
|---|---|---|
| `full` (build 1,000 `Dot`s, 1,000 `scene.circle` calls) | 254 | 302 |
| `draw-build` (build the `Dot` list, send nothing) | 89 | 57 |
| `draw-empty` | 0.3 | 0.2 |

Scaling, `full`: 1,000 particles 147 + 254 us, 10,000 particles 1,469 + 2,566 us,
100,000 particles 14,630 + 25,549 us under wasmtime. The cost is linear and
cache pressure at 100,000 (several MB of records) adds nothing visible. V8:
88 + 302, 899 + 3,191, 9,086 + 31,502.

### Time breakdown, one frame

Wasmtime, 1,000 particles, update plus draw = 401 us (2.4% of a 16.7 ms frame;
about 41,000 particles fill the frame at this cost, before any real painting).

| category | us | share | how obtained |
|---|---|---|---|
| Record allocation, init, RC, drop, free (7 per particle in `update`) | 70-122 | 17-30% | floor: `full` less `flat` (4 records fewer: 70 us); ceiling: 7 records x 17.5 ns average |
| Same lifecycle for the 4 allocations per `Dot` in `draw` | ~70 | 17% | `draw-build` (89) less its list traversal (~19) |
| Host calls: 1,000 `scene.circle` | ~165 | 41% | `full` draw 254 less `draw-build` 89 |
| List traversal, closure calls, event dispatch | ~23 | 6% | `list-only` 54 less its 2 records (35) |
| Field arithmetic | 1-2 | <0.5% | `scalar-heavy` vs `scalar-full`: 15 extra float ops cost 1 us |
| Remaining (model swap, the part of the lifecycle the floor leaves out) | 19-71 | 5-18% | by difference |

Inside the update lifecycle, poisoning on free is about 35 us (see below).

V8: update 88 + draw 302 = 390 us. Per-record cost is about 12 ns, so the same
seven records are about 85 us of 88; the host calls are 245 us (63% of the
frame), mostly the runtime's color regex and string decode per call.

Field arithmetic is 1 ns per particle in isolation. `examples/bench/inner_loop.wat`
runs the step's four float operations over a flat array with no allocation:
wasmtime 1.0 ns scalar, 0.5 ns `f64x2`; V8 0.9 ns scalar, 0.5 ns `f64x2`. Against
147 ns per particle for the update, even an infinitely fast arithmetic unit saves
under 1%.

### What an `f64x2` path buys

Hand-patched into the real module's derived `+` and `*` (one `v128.load` per
operand, `f64x2.add`/`f64x2.mul`, one `v128.store` to the new record), then run
as the full benchmark:

| | wasmtime update | V8 update |
|---|---|---|
| `full` | 146 | 89 |
| `full` + `f64x2` in derived `+`, `*` | 142 (-3%) | 89 (0%) |
| `full` without poison fill | 110 (-25%) | 67 (-24%) |
| `full` without poison + `f64x2` | 108 | 64-67 |

The SIMD saving is small because the allocation the result needs is still there.
The patch also keeps the records boxed and reference-counted, which is what the
lowering would have to do today: a two-field record is 24 bytes (8-byte header,
two `f64`), and `v128.load` from offset 8 is only 8-byte aligned.

Integer records cannot use this path. Goat's `Int` ops carry spanned overflow
traps, and wasm's integer vector ops wrap silently. Only `Float` fields map.
WAMR (the embedded runtime, ADR 0019) is built without SIMD, so a scalar
fallback must stay, and the derived scalar function is that fallback.

### The cheaper wins

Measured or bounded on this program, wasmtime update, 1,000 particles:

| change | update us | saved | evidence |
|---|---|---|---|
| Stop poisoning freed blocks (or poison only in test builds) | 110 | -25% | hand-patched wasm, both engines |
| Constant record literals built once (the `hoisted` variant) | 142 | -3% | measured; one record fewer, but a shared literal still takes a `dup` and `drop` per use |
| Fuse the step's temporaries, three records per particle (`scalar-full`) | 114 | -22% | measured |
| Unbox small records, nested flat (`flat`, 1 record per particle) | 77 | -48% | measured; V8 40 vs 88, -55% |
| In-place reuse of dead records in the step | ~75-90 | -40% to -50% | estimate: 5 records at ~17.5 ns, minus a uniqueness check |
| Reuse list cells in `change_each` as well | ~40 | ~-75% | estimate: 7 records to 0 |

The `flat` row is a source-level rewrite (`examples/bench/particles_flat.goat`),
not a compiler feature. It shows the target an unboxing pass would approach, and
it was measured, not guessed.

Perceus reuse exists in the compiler but does not fire here. `mir/src/rc.rs`
handles `ReuseRecord` for spread updates (`{...r, f: x}`), and the derived `+`
and `*` never take it: the five `step` records are fresh allocations in the
counter run. Reuse would also need uniqueness at runtime. `q.p` is loaded out of
`q` with a `dup`, so its count is 2 at the `+` and the dead-operand test fails
unless `q` is freed first (drop specialisation, borrowing the fields out of a
unique `q`). That is real compiler work, which is why the table marks reuse as
an estimate.

### Findings outside the question

- **Poison on free.** `wasm/src/allocator.rs` fills every freed block with 0xFE
  via `memory.fill`. A `memory.fill` call per free is 5 ns here and is about a
  quarter of `update` in both engines. It is a safety net against stale reads.
  Whether it belongs in release modules is a policy decision for the owner.
- **Host call per shape.** A frame of 1,000 dots costs 165 ns (wasmtime) to
  245 ns (V8) per `scene.circle` before painting. Batching shapes, or a typed
  array handed across once, would remove most of 41% to 63% of the frame. That
  is a host-vocabulary question (ADR 0020), not a codegen one.
- **The cost per record is not uniform.** `hoisted` removes one record per
  particle (the counters read 6,003 allocations against 7,002) but saves 5 us,
  not the 17.5 us the average predicts. A float-only temporary is cheaper than a
  record that holds pointers, which needs its children released. So the
  per-record figures in this document are averages over a mix, and the
  lifecycle share below is an estimate.

## Recommendation

Do not build an `f64x2` backend for records now. On the workload the owner
described it moves the frame by 0 to 3%, against two path costs: a second
lowering to keep correct for the proofs and the differential tests, and the
scalar fallback that stays regardless. In order of return per effort:

1. **Decide the poison policy.** About -25% of update in both engines, no
   language or codegen change beyond one allocator function. Owner call because
   it trades a safety net for speed.
2. **Cut the per-shape host call.** The largest single item at this scale:
   41% (wasmtime) to 63% (V8) of the frame. Needs a vocabulary decision.
3. **Unbox small records and make the derived arithmetic reuse dead operands.**
   Measured ceiling -48% to -55% of update; reuse for the step and list cells
   estimated -40% to -75%. This is the Perceus work already underway in spirit,
   and it compounds with everything above.
4. **Revisit SIMD with flat float arrays.** If the Julia aspiration means
   numeric loops over many values, the enabler is an unboxed `Float` array
   (contiguous, no header, no per-element RC). There `f64x2` halves the
   arithmetic (1.0 to 0.5 ns per particle measured, memory-bound beyond that)
   and arithmetic can finally be the dominant cost. Record SIMD would then fall
   out of the array lowering rather than being its own backend. That decision,
   and the array feature, are the one-way doors; measure again once arrays
   exist.

## Reproducing

```
cargo run --release -p goat --features native --example record_arith_bench
cargo run --release -p goat --features native --example record_arith_bench -- --inner
cargo run --release -p goat --features native --example record_arith_bench -- --emit DIR
node web/record-arith.bench.ts DIR
wasm-as --enable-simd examples/bench/inner_loop.wat -o inner_loop.wasm
node web/record-arith.bench.ts --inner inner_loop.wasm
```

`--wasm A.wasm B.wasm` times modules already built, such as the hand-patched
ones. The allocation counters and the patched modules (no poison, `f64x2`) came
from `wasm-dis`, a text edit of the disassembly, and `wasm-as
--enable-tail-call --enable-bulk-memory --enable-sign-ext --enable-mutable-globals
--enable-multivalue --enable-nontrapping-float-to-int` (plus `--enable-simd`); the
edits are two lines each (remove the `memory.fill` in the free function, or
replace the two scalar arithmetic blocks in the derived functions with one
vector op).

## After the reuse change (issue 558)

Two compiler changes, no language or layout change (ADR 0010 identity holds):

- The derived record `+ - * /` builds its result with `ReuseRecord` on its first
  operand, so an operand nothing else holds is overwritten in place.
- `mir/src/hoist.rs` loads the fields of a record that is only read through
  `Field`, on the straight line below its binding, right after the binding. The
  RC pass then releases the record before the call that consumes the loads
  (`drop_before_call` in `mir/src/rc.rs`), so a field of a dying record has one
  reference when it reaches the derived function.

One update frame of the benchmark allocates 5,002 records, down from 7,002
(`mir/tests/reuse.rs` counts 5 per particle, down from 7). Update time, median
of 300 frames, 1,000 particles, same machine:

| | before | after |
|---|---|---|
| wasmtime `full` | 144-149 us | 121-123 us (-17%) |
| V8 `full` (default tiers) | 88.4 us | 87.0 us (-1.5%) |
| V8 `add-only` / `mul-only` / `hoisted` | 54 / 81 / 84 us | 42 / 71 / 60 us |
| V8 `full`, `--no-liftoff` | 109.5 us | 94.5 us (-14%) |

V8's `full` result under default tiering is unexplained: the variants around it
improve 13-29% while `full` does not. Not yet measured: reuse of the particle's
own cell for the new particle, the damping literal built once, and the list cells
in `change_each`.

## After constant records became static cells (issue 558)

A record whose fields are all constants, such as the damping literal
`{x: 0.999, y: 0.999}`, is now one immortal cell in the module's data section,
the way a nullary tag is. It costs no allocation, no count change and no free.
Layouts are unchanged (ADR 0010 identity holds); a reload copies the cell into
the refreshed model like any record, and an operation that would overwrite a
unique record allocates instead, because the cell's count is never 1.

One update frame now allocates 4,002 records, down from 5,002
(`mir/tests/reuse.rs` counts 4 per particle). Median of 300 frames, 1,000
particles, Apple M1 Pro, same tree with and without the change, two runs each
(this session's machine runs faster than the table above, so compare within
this table only):

| | before | after |
|---|---|---|
| wasmtime `full` update | 90.8 us | 79-81 us (-12%) |
| wasmtime `mul-only` | 79 us | 56 us |
| V8 `full` update | 49.7-52.2 us | 42.0-42.9 us (-16%) |
| V8 `mul-only` | 36-39 us | 30-31 us |

Unmoved: the hand-flattened `flat` variant (52 us wasmtime, 28-29 us V8), so
the nested-record layout still costs about 28 us (wasmtime) and 14 us (V8) per
frame. Closing that needs the nested record stored inline in its parent with the
derived arithmetic inlined, so that `q.p + q.v` reads the four scalars from one
cell; scalar replacement alone gains nothing here, because the `*` result already
reuses `q.v`'s cell. Still open: reuse of the particle's own cell for the new
particle, and list cells in `change_each`.

## After batching a frame's shapes into one host call (issue 576)

`draw` used to make one `scene.*` host call per shape (1,000 `scene.circle`
calls in this benchmark). The glue now encodes the frame's shapes into one buffer
in the module's memory and makes one `scene.frame(ptr, len)` call (ADR 0015,
second addendum). The host decodes the buffer and still drives its per-shape
handlers, so the host's own work (color check, finite check, the counting scene)
is unchanged; what disappears is the boundary crossing and the per-call
argument marshaling, and what appears is the encode in the module and the decode
in the host. `draw` still returns `List(Shape)`.

`draw` time, median of 300 frames, 1,000 particles, Apple M1 Pro, master at
`806c10f` against this change built and run the same way on the same machine in
one session (the update step is unchanged and omitted):

| `draw` | before | after |
|---|---|---|
| wasmtime `full`, 1,000 shapes | 235 us | 136 us (-42%) |
| wasmtime `full-10k`, 10,000 shapes | 2,544 us | 1,351 us (-47%) |
| wasmtime `full-100k`, 100,000 shapes | 24,057 us | 13,427 us (-44%) |
| V8 `full`, 1,000 shapes | 268-280 us | 173-177 us (-36%) |
| V8 `full-10k` | 2,791-2,852 us | 1,840-2,106 us (-27% to -35%) |
| V8 `full-100k` | 27,612-27,945 us | 18,463-19,143 us (-31%) |

`draw-build`, which builds the `Dot` list and sends nothing, is 71-72 us
(wasmtime) and 44-46 us (V8) in both trees, so the host share of a frame's draw
falls from about 164 us to 65 us under wasmtime and from about 225 us to about 128
us under V8. In V8 the remaining cost is the decode and the host's per-shape
work in JavaScript, not the boundary. Two changes to the decoder moved V8
`full` draw from 225 us to 173 us: a loop instead of `TextDecoder.decode` for
strings of 24 bytes or fewer that are ASCII (a color is `"red"`), and parsing
the frame's call declarations once per distinct header instead of once per
frame.

A frame of this benchmark is a 14-byte header (one declared call, `circle`) and
35 bytes per shape (the call index, three `f64`s, a length and `"tomato"`), so
1,000 shapes encode to about 35 KB. The buffer is allocated by a
frame's first write, grows by doubling, and is freed when the frame is handed
over, so a program that draws nothing holds nothing between frames.

To reproduce, run the three commands under "Reproducing" against each tree.

## The native backend, same benchmark (issue 589)

The same two programs, built by the LLVM backend (ADR 0042): goat to `.ll`, then
`clang -O2 -shared`, loaded with `dlopen` and driven by `goat_native::Interactive`
with the same counting sink and the same method as above (30 warm-up frames, then
the median of 300 `Frame` + `update`, then `draw`). Wasmtime, V8 and native all
run the same tree (`a44fc28` plus this change; the wasmtime and native numbers
come from one process, V8 from `node web/record-arith.bench.ts` right after).
Apple M1 Pro, 10 cores, Apple clang 21.0.0, wasmtime 50.0.2, node v26.13.1.

Machine load: the box was heavily loaded earlier in the session (1-minute load
average 28 to 45 on 10 cores), so measurement waited. Both measured runs started
at load averages of 9.3 and 7.7 (11 at the first warm-up run). Two runs of the
wasmtime and native pair agree within 5% on every row (the worst is native
`full` draw, 80.6 against 85.1 us); two V8 runs agree within 1.5%. The tables
show the mean of the two runs.

Microseconds per frame, median of 300, update + draw:

| particles | wasmtime | V8 | native -O2 | native vs wasmtime (update / draw) | native vs V8 (update / draw) |
|---|---|---|---|---|---|
| `full` 1,000 | 79.5 + 129.5 | 40.7 + 166.8 | 25.8 + 82.9 | 3.1x / 1.6x | 1.6x / 2.0x |
| `full` 10,000 | 797 + 1,307 | 424 + 1,780 | 242 + 832 | 3.3x / 1.6x | 1.8x / 2.1x |
| `full` 100,000 | 8,021 + 13,143 | 4,255 + 17,977 | 2,472 + 8,519 | 3.2x / 1.5x | 1.7x / 2.1x |
| `flat` 1,000 | 51.4 + 128.2 | 27.5 + 168.4 | 16.1 + 81.8 | 3.2x / 1.6x | 1.7x / 2.1x |
| `flat` 10,000 | 518 + 1,284 | 285 + 1,779 | 144 + 812 | 3.6x / 1.6x | 2.0x / 2.2x |
| `flat` 100,000 | 5,280 + 13,111 | 2,891 + 18,059 | 1,472 + 8,358 | 3.6x / 1.6x | 2.0x / 2.2x |

`full` is `examples/bench/particles.goat` (nested `{p: {x, y}, v: {x, y}}`),
`flat` is `examples/bench/particles_flat.goat`. Cost stays linear in all three
engines up to 100,000 particles.

Allocations per frame, counted by the native instance (`goat_instance.allocs`):

| | update | draw |
|---|---|---|
| `full`, 1,000 particles | 4,002 | 4,009 |
| `full`, 10,000 / 100,000 | 40,002 / 400,002 | 40,012 / 400,015 |
| `flat`, 1,000 / 10,000 / 100,000 | 3,002 / 30,002 / 300,002 | 4,009 / 40,012 / 400,015 |

Update matches the wasm count after the reuse and static-cell changes above
(4,002 per frame, 4 per particle plus the frame's own; `mir/tests/reuse.rs`
asserts 4 per particle in the interpreter). `draw` is 4 per shape (a `Dot`, its
payload, two list cells) plus the batching buffer's doublings (9 at 1,000 shapes
up to 15 at 100,000). The wasm module exposes no allocation counter outside a
hand-instrumented module, so the match is against that counted figure and the
interpreter, not a fresh wasm count; both engines also finish with zero live
blocks.

Compile time, `full` (the flat variant is within 5%):

| step | time |
|---|---|
| goat to wasm (parse, check, mono, MIR, emit) | 14 ms |
| goat to `.ll` (same front end, LLVM emitter; 583 KB of text) | 11-15 ms |
| `clang -O2 -shared` on the `.ll` plus the C shim | 0.69 s (0.60-0.72 s across variants) |

The native backend therefore costs about 0.7 s of clang per build against 14 ms
for wasm (which wasmtime then compiles with Cranelift at instantiation). That is
fine for a release build and rules native out for live coding, as ADR 0042
already says.

Reading the table:

- **Update is 3.1x to 3.6x faster than wasmtime and 1.6x to 2.0x faster than
  V8.** The work is the record lifecycle; the cause of the gap
  was not profiled (it is plausibly LLVM's inlining of the allocator and drop
  paths against Cranelift's, and native's unchecked memory access). 4,002 allocations in 25 us is about 6 ns per
  allocation and per particle step, against 20 ns under wasmtime.
- **Draw gains less (1.5x to 1.6x over wasmtime), and V8's is the slowest of the
  three.** The module's side (building 1,000 `Dot`s, encoding the frame) is fast;
  what remains is the host decoding the frame buffer and driving the sink, which
  is Rust in the native and wasmtime cases and JavaScript in V8's. Native draw
  was not split into module and host time.
- **The nested-record tax shrinks in absolute terms, not in ratio.** `full` less
  `flat` is 9.7 us native, 28 us wasmtime, 13 us V8 (1,000 particles).
- **Not measured:** the other `Variant`s under native (the harness runs them
  with `--native` and no `--only`), a painted canvas, and the native host's real
  window (M2).

Reproduce (the native column needs clang on `PATH`):

```
cargo run --release -p goat --features native --example record_arith_bench -- --native --only full,full-10k,full-100k,flat,flat-10k,flat-100k
cargo run --release -p goat --features native --example record_arith_bench -- --emit DIR
node web/record-arith.bench.ts DIR
```
