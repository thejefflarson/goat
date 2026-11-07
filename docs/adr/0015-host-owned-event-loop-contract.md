# ADR 0015 — The host owns the loop; goat exports a pure init/update/draw contract

- Status: accepted (2026-11-07)
- Context: Phase 9.5 (event loop), `docs/plan.md` ("Phase 9.5 — Event loop
  (host-owned)"), ADR 0002 (object header), ADR 0009 (strings are immortal,
  length at `ptr+8`, bytes at `ptr+12`), ADR 0010 (first-use layout pinning /
  width-independent variant families), ADR 0012 (`trap`; prelude builtins),
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
root `Let` chain. As with `trap` (ADR 0012) and the turtle names (ADR 0014), a
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
  > Note (as built, #105): in-place record reuse is not yet implemented — MIR has
  > `ReuseVariant` but no `ReuseRecord`, so a spread update allocates a fresh
  > record and frees the old one. The live-allocation balance above still holds;
  > the "allocates ~nothing" steady state is tracked by #173.
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

The browser cannot preempt wasm, and goat's only non-termination is infinite
recursion; non-tail recursion self-limits via stack exhaustion, but tail calls
(enabled) do not. So the backend emits a mutable `i32` `fuel` global and, at each
function entry, `fuel -= 1; if fuel <= 0 { unreachable }`. The host resets `fuel`
to a generous budget before each `goat_update`; a runaway update exhausts it in
bounded steps and traps, which the host catches and surfaces as *"your update got
stuck"* — stopping the program, not hanging the tab. The browser additionally
keeps a wall-clock frame-budget guard for a terminating-but-pathologically-slow
update. The CLI/wasmtime driver prefers wasmtime's native epoch interruption; the
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
  ships **Polyline + Line**. A `Polyline` expresses the accumulating arrow-draw
  path as one shape rather than N `Line`s; the `goat_draw` wrapper streams it with
  a nested list walk — `scene.polyline_begin(color)`, then `scene.vertex(x, y)`
  per point, then `scene.polyline_end()` — reusing the same `Switch`/`Payload`
  machinery one level deeper, and the per-frame cap also bounds total vertices.
  Circle/Rect/Text are a fast-follow.
- **The v1 browser event vocabulary:** `Tick(dt)`, `KeyDown(key)`, `KeyUp(key)`,
  `Pointer{Move,Down,Up}({x,y})`, where `key : Key = Up | Down | Left | Right |
  Other(String)`. The host always passes the raw `KeyboardEvent.key` string; the
  compiler-generated `goat_event_KeyDown` maps `"ArrowUp"/"ArrowDown"/…` to
  `Up/Down/Left/Right` (via `StrEq` against immortal literals) and everything else
  to `Other`, so the string→arrow mapping is authoritative in one place.
- **The fuel budget and per-frame shape cap numbers.**

The genuine one-way door is the ABI *shape*: the export set, the owned-pointer
ownership convention, exports-as-subscription, and the scene-streaming protocol.
