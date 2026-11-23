# ADR 0015 — The host owns the loop; goat exports a pure init/update/draw contract

- Status: accepted (2026-11-07)
- Context: Phase 9.5 (event loop), `docs/plan.md` ("Phase 9.5 — Event loop
  (host-owned)"), ADR 0002 (object header), ADR 0009 (strings are immortal,
  length at `ptr+8`, bytes at `ptr+12`), ADR 0010 (first-use layout pinning /
  width-independent variant families), ADR 0023 (`trap`; prelude builtins),
  ADR 0014 (turtle builtins, color allowlist, the million-command cap). Recorded
  before implementing #105/#106/#107. Supersedes nothing; adds a second,
  parallel entry surface beside the run-once `goat_entry`.

## Context

A goat program never writes a loop or blocks; the host owns the loop and calls
pure goat exports. The interactive program is three top-level bindings in the
Elm shape: `init` (the starting model), `update(model, event) -> model`, and
`draw(model) -> List(Shape)` (a picture as **data**, not imperative draw calls).
The host runs `model = init()`, feeds events through `update`, and renders
`draw(model)` on a frame. The same contract must hold on every host — browser,
CLI/wasmtime, and (later) a microcontroller — so the decisions here are the
boundary, and the boundary is a one-way door once programs and hosts depend on
it.

The hard constraint shaping every choice: **the host must not know goat's
internal heap layout.** Variant tag numbers are assigned mono-globally in
sorted-label order and payload slot offsets are mono-internal (ADR 0010);
coupling a host to them is fragile. So the model crossing the boundary is one
**opaque** heap pointer the host never inspects, and the two directions that
*do* need structure — the host building an event, and the host reading a
picture — are bridged by compiler-emitted glue, not by the host parsing goat
memory.

## Decision

### 1. Interactive mode is detected by the names `init`/`update`/`draw`

A program is *interactive* iff its root let-chain binds all three of `init`,
`update`, and `draw`, un-shadowed. Otherwise it is *run-once* — today's
`goat_entry` with the imperative turtle, unchanged. Detection is over the HIR
root `Let` chain. As with `trap` (ADR 0023) and the turtle names (ADR 0014), a
user binding of one of these names shadows with the ordinary warning and reverts
the program to run-once; the names are a default, not a reservation.

The model type **M must be a record** (a checker error otherwise, with a span:
*"init must be a record, like {x: 0, y: 0}"*). A record is always an `i32` heap
pointer, so the host ABI is uniform and opaque; a scalar/boxed model is a
deliberate v1 non-goal. The checker gains a new cross-binding pass (none exists
today — HM does not link the three signatures) that unifies `init : M`,
`update : (M, E) -> M`, and `draw : (M) -> List(Shape)`, requires `E` to be a
variant (the event row) and the result a `List` of a `Shape` variant, and emits
spanned errors on mismatch.

### 2. The export ABI and its ownership/RC convention

Interactive mode emits these exports beside `memory`, `goat_alloc`, and
`goat_live_allocs`:

| Export | Wasm sig | Meaning |
|---|---|---|
| `goat_setup` | `() -> i32` | Run the top-level chain once; store the `update`/`draw` closures in module globals; return the initial model (`rc=1`, owned by the host). |
| `goat_update` | `(i32 model, i32 event) -> i32` | Call the stored `update`; **consumes** both arguments (standard Perceus owned-parameter convention); returns the new model. |
| `goat_draw` | `(i32 model) -> ()` | `Dup` the model, call the stored `draw`, stream the `[Shape]` out through `scene.*`, drop the picture. Does **not** consume the model. |
| `goat_event_<Tag>` | per §4 | Construct the event variant `<Tag>`; returns an owned event (`rc=1`). |
| `goat_release_model` | `(i32) -> ()` | Drop an owned model. |
| `goat_shutdown` | `() -> ()` | Drop the stored closure globals (teardown hygiene). |

Top-level values referenced by `update`/`draw` become **captures**, so the two
are generally closures with an environment, not bare functions. `goat_setup`
runs the top-level chain exactly once — evaluating `init` and constructing the
`update`/`draw` closures with their captures — then writes the two closure
pointers into module globals (new `i32` globals beyond the allocator's) and
returns `init`'s value. `goat_update`/`goat_draw` load the stored closure and
call it. This is the Elm `main`-wiring analogue and solves "where does top-level
code run" and "how are captures persisted across calls" together.

**The live-allocation balance is the invariant** (`goat_live_allocs == 0` after
teardown):
- `update` consumes `model` and `event`; after `goat_update` returns, the host's
  old handles are dead and it holds only the returned new model. Perceus reuses
  the old model's cells in place for spread updates (`{...model, x: ...}`), so a
  steady-state loop allocates ~nothing.
  > Note (as built): a spread that keeps the base's layout lowers to MIR
  > `ReuseRecord`, which overwrites the base's cell when its count is 1 (the
  > host's old handle is dead, nothing else shares it) and allocates otherwise.
  > Variant reuse (`ReuseVariant`) is not yet produced.
- `goat_draw` `Dup`s the model (O(1) rc-inc) so `draw` can consume its copy while
  the host keeps the original; the returned picture is streamed and dropped
  inside the wrapper, so the host never holds a picture pointer and has nothing
  picture-shaped to free.
- Teardown: `goat_release_model(model)` then `goat_shutdown()`.

The existing `EmitError::Unsupported("heap-valued root")` and the "drop a
non-string pointer root" behavior of the rc pass assume the program's value is
never handed out; the interactive exports deliberately **return and accept** heap
pointers, so they are carved out of that drop/print path.

### 3. `draw` returns data; the compiler streams it to the host

> Amended by the second addendum below: the shapes reach the host in one
> `scene.frame` call per frame, not one `scene.*` call per shape.

`draw(model) -> List(Shape)`. The host cannot read a goat list, so the compiler
emits the `goat_draw` wrapper that walks the `Empty | Link(head, tail)` list and,
for each shape, switches on its tag, reads its payload record, and calls the
matching `scene.*` host import — the same import-callback transport the turtle
already uses. `draw` stays a **pure data-returning function in the language**; the
imperative streaming is compiler glue, invisible to the program. The walk is
bracketed by `scene.begin()` / `scene.end()` so the host renders exactly one
frame, and a per-frame shape cap (same spirit as ADR 0014's command cap) traps a
runaway `draw` instead of exhausting host memory.

### 4. The exported event constructors *are* the subscription interface

The host cannot build a goat variant, so for each event tag that `update`'s match
**handles**, the compiler emits a `goat_event_<Tag>` constructor export. The host
enumerates `instance.exports`, and for each `goat_event_(.*)` it enables exactly
that listener and uses that same export to build the event. So the subscription
set *is* the set of emitted constructors — there is no separate custom section or
bitset that could drift from what the module can actually construct, and
subscription inference and event construction are one mechanism. The host enables
a **superset** of the handled events (an `else` arm adds no subscription);
handling an un-enabled event is unreachable. An event tag `update` matches that
is not in the host vocabulary is a checker error (*"the host doesn't send a
`Frobnicate` event"*).

> Note (as built, #106): the checker closes the event row to the tags `update`
> handles — an `else` arm leaves the row at the tags named before it — and
> unifies each payload with the vocabulary, so a `match` on a key without an
> `else` must name all five `Key` tags. `draw`'s list is unified with one list
> type, so every element is the same closed `Shape` row. A per-frame budget of
> 100,000 shapes plus vertices traps an oversized picture.

Inference is at **event granularity, not key granularity**: `KeyDown(k)` matched
with a nested `match` on `k` subscribes to `KeyDown` and receives every keydown;
the arrow-vs-other discrimination happens inside goat, one level below the row the
compiler reads. (goat patterns do not nest — `KeyDown(Up)` is written as
`KeyDown(k) then match k do Up then ...`.)

### 5. Bounded update time via a compiler-injected fuel global

> Superseded by ADR 0021: goat emits no fuel; each host owns preemption. Kept as
> the historical record.

The browser cannot preempt wasm, and goat's only non-termination is infinite
recursion; non-tail recursion self-limits via stack exhaustion, but tail calls
(enabled) do not. So the backend emits a mutable `i32` `fuel` global and, at each
function entry, `fuel -= 1; if fuel <= 0 { unreachable }`. The host resets `fuel`
to a generous budget before each `goat_update`; a runaway update exhausts it in
bounded steps and traps, which the host catches and surfaces as *"your update got
stuck"* — stopping the program, not hanging the tab. The browser additionally
keeps a wall-clock frame-budget guard for a terminating-but-pathologically-slow
update. > Note (as built, #107): the global is exported as `goat_fuel` (a mutable wasm
> global the host sets), starts at `i32::MAX` in every module so a host that
> never refills it still gets a bound, and is spent by every compiled goat
> function entry. The browser refills it to 5,000,000 before each call into goat
> and treats a trap with the fuel at or below zero as "stuck"; a call that
> returns after more than one second also stops the loop.

The CLI/wasmtime driver prefers wasmtime's native epoch interruption; the
injected-fuel global is the portable mechanism a microcontroller host would use.

## Consequences

- An interactive program is three pure functions; the host owns the loop and the
  side effects. The same three exports drive the browser, the CLI, and a future
  microcontroller — only the `scene.*`/event transport differs per host.
- The host's trusted surface is tiny: one opaque pointer and a set of
  compiler-emitted, self-describing exports. No host parses goat's heap, so
  mono-internal layout (tag numbers, slot offsets) stays private and ADR 0010's
  first-use pinning is unaffected (the model type is pinned at `init`;
  `update`/`draw` resolve to the same layout family).
- Run-once programs (the imperative turtle) are untouched. Interactive mode is
  **shapes-exclusively**: the interactive host provides `scene.*` and not
  `turtle.*`, so an interactive `draw` cannot smuggle in imperative turtle calls
  (the checker rejects imperative-turtle use in interactive mode rather than let
  instantiation fail). `print` stays available in both modes.
- Host-side refusals — a color outside ADR 0014's `/^[A-Za-z0-9#]{1,32}$/`
  allowlist, the per-frame shape cap, a fuel-exhausted update — surface as traps,
  the same class as `trap`/`first([])`, not checker errors; the
  "errors-come-only-from-the-checker" invariant (well-typed programs reach the
  backend) is preserved.

### Reversible (versioned) parts, deliberately not one-way doors

Recorded as data on top of the ABI, growable without a new ADR (mirroring ADR
0014's "bridge, not a permanent decision"):

- **The v1 Shape vocabulary:** `Polyline {points: List({x,y}), color}`,
  `Line {x1,y1,x2,y2,color}`, `Circle {x,y,r,color}`, `Rect {x,y,w,h,color}`,
  `Text {x,y,text,color}`; coordinates are `Number`, origin top-left, y down
  (canvas-native — note this differs from the turtle's y-up stroke math). v1
  ships **Polyline + Line**; **Circle, Rect and Text** followed as single
  `scene.circle` / `scene.rect` / `scene.text` calls (filled, not stroked; a
  `Rect` and a `Text` anchor at their top left). A `Polyline` expresses the accumulating arrow-draw
  path as one shape rather than N `Line`s; the `goat_draw` wrapper streams it with
  a nested list walk — `scene.polyline_begin(color)`, then `scene.vertex(x, y)`
  per point, then `scene.polyline_end()` — reusing the same `Switch`/`Payload`
  machinery one level deeper, and the per-frame cap also bounds total vertices.
- **The v1 browser event vocabulary:** `Tick(dt)`, `KeyDown(key)`, `KeyUp(key)`,
  `Pointer{Move,Down,Up}({x,y})`, where `key : Key = Up | Down | Left | Right |
  Other(String)`. The host always passes the raw `KeyboardEvent.key` string; the
  compiler-generated `goat_event_KeyDown` maps `"ArrowUp"/"ArrowDown"/…` to
  `Up/Down/Left/Right` (via `StrEq` against immortal literals) and everything else
  to `Other`, so the string→arrow mapping is authoritative in one place.
- **The fuel budget and per-frame shape cap numbers.**

The genuine one-way door is the ABI *shape*: the export set, the owned-pointer
ownership convention, exports-as-subscription, and the scene-streaming protocol.

## Addendum (2026-11-08): hot reload keeps the model, so the model holds no function

- Status: accepted (2026-11-08)
- Context: Phase 11 hot reload (`docs/plan.md`). Recompile, instantiate the new
  module over the same heap, keep the model, swap `update`/`draw`. Builds on §1
  (the model is one opaque record pointer) and ADR 0010 (a layout is pinned per
  mono run).

### 1. A model type that contains a function is a checker error

> Amended by ADR 0035: the model may hold methods (record fields marked by
> `self`, ADR 0034). A plain function in the model is still an error.

The model is the record type that `init`, `update`, and `draw` share (§1). A
function anywhere inside it — a record field, a variant payload, a list item —
is rejected with a spanned error on `init`. A closure holds an index into its
own module's function table, so a closure that survives a reload would call
into code that is gone. Rejecting it up front keeps "errors come only from the
checker" intact: no later stage has to cope with a model it cannot carry across.
Functions stay available at the top level, where they become `update`/`draw`
captures that each reload rebuilds. This is the one new restriction; it applies
to every interactive program, reloaded or not.

### 2. A reloadable module imports its heap

`goat_wasm::emit_reloadable` builds an interactive module that imports `memory`,
the allocator's `heap` pointer, and its `live` count from `goat`, instead of
defining them. The host creates all three once, starts `heap` at
`goat_wasm::HOSTED_HEAP_START` and `live` at zero, and passes the same three to
every module it instantiates. The free-list table sits at a fixed address, so
every module's allocator agrees on it. The module's strings, nullary variant
cells, and static closures cannot sit at a fixed address (a longer program would
overwrite the old model), so a start function takes one block from the shared
allocator, hands its count back to `live`, copies the data in, and every static
address becomes an offset from a global. Run-once modules and `emit` are
unchanged.

### 3. The model-layout fingerprint decides keep or reset

> Superseded by ADR 0035: the fingerprint is gone. The old module snapshots the
> model by field and tag name, the new one refreshes a model of its own type
> from the snapshot, and the reload reports `refreshed` or `reset` with a reason.

Each interactive module exports an immutable `i64` global,
`goat_model_fingerprint`: FNV-1a over a canonical walk of the model's mono
layout — scalar kinds, record slot order, and every variant's tag numbers and
payload slots. Layouts are numbered by first visit, not by `LayoutId`, so an
unrelated type elsewhere does not change it. On reload the host instantiates the
new module and runs its `goat_setup`; if the fingerprints match, it releases the
new `init` value and keeps the running model, otherwise it releases the running
model through the old module and takes the new `init`. Either way it then runs
the old module's `goat_shutdown`, so the old closures are dropped by the code
that built them, and `goat_live_allocs` stays at zero. If the new module fails
to start, the old one keeps running.

### Consequences

- The fingerprint is conservative: tag numbers are assigned across the whole
  program (ADR 0010), so handling an event that sorts before a list's `Link`
  renumbers it and resets the model. Renaming a field without changing its slot
  or type keeps the model, because a layout records positions, not names.
- Each reload leaves its static data in the heap for good, because a kept model
  may point into it. That is roughly the size of the program's string literals per
  reload, and it is not counted by `goat_live_allocs`.
- A model that survives a reload is only as valid as the fingerprint: it
  compares layouts, not meaning.

## Addendum (2026-11-22): a frame's shapes reach the host in one call

- Status: accepted (2026-11-22)
- Context: #576, which the owner approved on the condition that batching is a
  host-side change and `draw` still returns shapes. §3 above makes one `scene.*`
  host call per shape. In the particle benchmark of
  `docs/design/record-arithmetic-performance.md` those calls were 41% of a
  frame under wasmtime and 63% under V8. ADR 0020 gives each shape the scene
  call or calls it streams through. This addendum changes the transport, not
  the vocabulary and not the language.

### 1. One `scene.frame(ptr, len)` per frame, inside the bracket

The `goat_draw` glue still walks the `List(Shape)` that `draw` returned. It no
longer calls a host import per shape. It encodes each shape into one buffer in
the module's linear memory and, when the walk ends, makes one call:

```
scene.begin()
scene.frame(ptr: i32, len: i32)    // omitted when the picture can hold no shape
scene.end()
```

`ptr` and `len` name bytes of the module's own exported `memory`. They are
valid for the duration of the call only: the module frees the buffer when the
call returns. `scene.begin` and `scene.end` are unchanged. The glue's shape
budget (100,000 shapes plus vertices) is unchanged; see §4 for the byte bound.

### 2. The encoding, version 1

A frame declares the scene calls it makes, then makes them, so a host needs no
table of the vocabulary's calls. All integers are little-endian.

```
frame  = version:u8  ncalls:u8  call{ncalls}  record*
call   = name_len:u8  name:utf8  nparams:u8  wire:u8{nparams}
record = call_index:u8  value{nparams of the indexed call}
value  = Int: i64 | Float: f64 | Bool: u8 (0 or 1) | Str: len:u32, then len bytes
```

- A `wire` is the ASCII byte `i`, `f`, `b` or `s`: the type of one leaf of a
  shape payload (ADR 0020's `Leaf`s: `Int`, `Float`, `Bool`, `String`).
- A `call` is one of the names a shape's `SceneCalls` gives (`Call(name)`, or
  `begin`, `element` and `end` of a `Stream`), with the types of the leaves it
  takes. It is declared once per frame, in the order the glue first uses it, so
  the numbering is the glue's, not the vocabulary's.
- A `record` is one scene call: a shape that streams through `Call(name)` is
  one record; a `Stream` shape is a `begin` record over the leaves outside its
  list, one `element` record per list element, and an `end` record. The records
  appear in the order `draw`'s list holds the shapes.
- `Int` is 64 bits on every profile and `Float` is `f64`, so a host reads the
  same bytes whatever the program's `Profile`. (An interactive program is
  desktop-profile only, so this costs nothing today.)
- A string is copied into the buffer, not referred to. The frame is then
  self-contained: the interpreter, which has no linear memory, produces the same
  bytes as the wasm backend, and a host reads no pointer into the guest's heap.
  Strings that repeat across shapes (a color) are repeated.
- The header is the same bytes in every frame of a module, so a host may parse
  it once and reuse the result for any frame that starts with the same bytes.

A host replays a frame as the calls it encodes, in order. That is the whole of
decoding: the per-shape call a host already implements (`SceneSink::circle`,
`Scene::circle` in `web/scene.ts`) is what the record means. A host with a
vocabulary of its own needs only to implement the names its vocabulary uses.

### 3. Versioning

`version` is 1. A host rejects any other value. Adding a call to a vocabulary
needs no version change, because the frame declares it and a host that does not
implement the name rejects the frame before replaying any of it. Adding a wire
type, changing a width, or changing the order of the header's fields is a new
version. The version is reversible in the sense §Reversible above means: it is
data on top of the ABI, and the compiler and the hosts of one release change
together.

### 4. The frame is the program's output, so hosts bound-check every read

A host MUST treat the bytes as untrusted. Each host rejects, rather than
panics on, each of:

- a `(ptr, len)` that is not inside the module's memory (checked with
  overflow-safe arithmetic on unsigned 32-bit values);
- a frame that ends inside a header or inside a value, including a string whose
  length exceeds the bytes left;
- a version other than 1, a `wire` byte other than `i f b s`, a call name that
  is not UTF-8, a `call_index` the header did not declare, and a call name the
  host does not implement.

A string's bytes that are not valid UTF-8 are replaced, as they were when the
host read a goat string through `scene.text`. Colors and coordinates are still
checked per call after decoding (ADR 0014's allowlist, finite numbers), so a
frame cannot pass a value a per-call import would have refused.

The buffer is bounded at 16 MiB (`goat_mir::frame::LIMIT`). A write that would
pass it traps the program with "this picture is too big", on both backends. The
glue's shape budget remains, so a picture can still trap on either bound.

### 5. Where the buffer lives and who frees it

The buffer is a block of the module's heap. The first write of a frame
allocates it, a later write that does not fit doubles it, and `scene.frame`'s
return frees it, so a module holds no buffer between frames and a hot reload
(addendum above) has nothing to carry. Three MIR nodes carry it (`Expr::Frame`
with `Reset`, `Put` and `Present`); `Reset` at the start of a frame frees a
buffer that a trapped frame left behind. `goat_live_allocs` is zero between
frames.

### 6. What each host does

| Host | Receives the frame by |
|---|---|
| wasmtime (`goat/src/native`) | `link_frame` hands the host a slice of the guest's memory, no copy; `Host::frame(&[u8])` |
| MIR interpreter | the same bytes from its own buffer, through `Host::frame` |
| Rust `SceneSink` hosts (`SceneHost`, `Scene<S>`, the canvas SVG sink, the editor's highlight and format) | `Host::frame` replays through `mir/src/frame.rs`'s `replay` into the sink's per-shape methods |
| Web canvas, highlighter, formatter, theme (`web/scene.ts`) | `sceneImports(...).scene.frame` decodes with `web/frame.ts` and calls the `Scene` methods |
| Apple editor | the web build in a WKWebView, so the same decoder |
| Board hosts (WAMR) | none: an interactive program is not built for the embedded profile (ADR 0026), and no board host draws a scene |

`Host::frame` has a default that returns an error, so a host that provides no
`scene.frame` fails at link time rather than running a program that draws into
nothing.

### Consequences

- A host sees `begin`, the shapes in order, `end`, as before. One observable
  change: a `draw` that traps part-way through the walk used to leave the host
  with `begin` and the shapes drawn so far; now it leaves `begin` alone,
  because nothing reaches the host until the walk is done. The program stops
  either way, and the host already had to cope with a frame that never ends.
- The per-shape imports (`scene.circle` and the rest) are no longer imported by
  a compiled module. The web runtime keeps them so a module built before this
  change still runs; the Rust hosts never needed them for a module built after.
- A shape payload with a leaf that is not `Int`, `Float`, `Bool` or `String` was
  already rejected by `Vocab::validate`; it now also rejects a vocabulary of
  more than 255 distinct scene calls or a call with more than 255 values.
- Measured under wasmtime, `draw` of 1,000 shapes fell from 235 us to 136 us,
  and under V8 from about 270 us to about 175 us
  (`docs/design/record-arithmetic-performance.md`). Under V8 what is left is
  the decode and the host's own per-shape work, not the boundary.
