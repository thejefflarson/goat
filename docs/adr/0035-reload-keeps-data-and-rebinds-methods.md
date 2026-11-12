# ADR 0035 — Reload snapshots the model by name and rebinds methods by site

- Status: proposed (2026-11-11)
- Amends: ADR 0015's hot-reload addendum (§1 "a model that contains a function
  is a checker error", §3 "the model-layout fingerprint decides keep or reset").
- Context: ADR 0034 (a method is a record field whose first parameter is
  `self`), ADR 0020 (the host vocabulary feeds tag numbering), ADR 0009
  (strings are immortal), ADR 0026 (bounded stack). Canvas live reload today:
  `web/loop.ts` `reload`, `web/worker-core.ts` `reloadProgram`,
  `mir/src/fingerprint.rs`, and the "the model can't hold a function" rule in
  `checker/src/infer.rs` (the `find_func` check on the model, near line 1279).
- This is phase 1: the contract plus the measurements that gate building it.
  The recommendation is at the end.

## Problem

The program a kid writes first, a ball whose `update` and `draw` are methods,
cannot run on the canvas, because the checker rejects any function inside the
model. The rule exists because a closure holds an index into its own module's
function table; after a reload that index points into code that is gone.

Today's reload also decides keep-or-reset by a layout hash. The hash compares
slot positions and tag numbers, not names, so it keeps a model when it
should not (a renamed field with the same slot) and resets it when it need not
(an unrelated event tag that sorts before `Link` renumbers the list, ADR 0015
addendum, Consequences).

## Decision

1. **No object crosses modules.** The old module exports a generated
   `goat_snapshot(model) -> image`: a self-describing tree of records (by field
   name), variants (by tag name), lists, scalars and strings. A method slot
   holds a site key, not a function index. The image has a format version.
2. **The new module rebuilds the model** with a generated
   `goat_refresh(image, fresh) -> model | 0`, where `fresh` is the new module's
   own `init` value:
   - data comes from the image, by field name;
   - a field the image lacks comes from `fresh`;
   - a field the new type lacks is dropped;
   - a scalar or shape mismatch returns 0 with a reason code;
   - a method slot takes the new module's closure for its site key.
3. **Site key = (enclosing top-level binding, field label).** A method rebinds
   only if its key is unique in the program and its closure captures only
   top-level names. Otherwise the reload resets and the reason names the
   method. Lists rebind each element by key, not by index. A method that a
   spread inherits (`{...ball, size: 10}`) keeps the key of the literal that
   wrote it, here `(ball, moved)`.
4. **Host sequence.**
   1. New `goat_setup` gives `fresh`. If it traps, the old program keeps
      running.
   2. Old `goat_snapshot` gives the image.
   3. New `goat_refresh(image, fresh)`.
   4. Old `goat_release_model`.
   5. Old `goat_shutdown`.
   6. Free the image.

   If step 2 or 3 traps or returns 0, the host releases whichever model it
   holds and keeps the new module's `fresh` (a reset); it never leaves the old
   program half-torn-down.
5. **Status.** The `Reloaded` outcome becomes
   `{outcome: "refreshed" | "reset", reason?: ResetReason}`, and the
   fingerprint "kept" path is retired: `goat_model_fingerprint`,
   `mir::model_fingerprint`, and the fingerprint comparison in `loop.reload`
   go away. A reason carries the names the copy needs (`field_added(spin)`,
   `field_removed(vy)`, `type_changed(x, Number, String)`,
   `method_added(grow)`, `method_lost(grow)`, `method_captures(update, speed)`,
   `ambiguous_site(update)`, `too_large`, `reshaped`).
6. **A plain function in the model stays a checker error, reworded.** The rule
   at `infer.rs` ~1279 keeps rejecting a function whose field is not a method,
   and accepts one the field flag from ADR 0034 marks `METHOD`:
   > The model can hold methods but not plain functions, and `{function}` has
   > no `self`. Write `self` first to make it a method, or keep it at the top
   > level.
7. **Generate snapshot and refresh in MIR**, so the interpreter can run them
   and a differential test can compare the interpreter with wasm.

Status copy (the host shows these; the table is part of the contract):

| Situation | Message |
|---|---|
| Refreshed | Updated: the ball kept going with your new `update`. |
| A field was added | Your sketch started over because you added `spin` to what it remembers. |
| A field was removed | Your sketch started over because it no longer remembers `vy`. |
| A field's type changed | Your sketch started over because `x` changed from a `Number` to a `String`. |
| A method was added or lost | Your sketch started over because the ball got a new method, `grow`. |
| A method captures a value | Your sketch started over because `update` uses `speed` from where the ball was made, and that can't carry over. |
| Fallback | Your sketch started over because your change reshaped what it remembers. |

"A field was added" applies when `fresh` cannot supply the field: always for a
list element (`fresh` has one `init`, not one element per ball), and for a
record nested inside one.

## Measurements

All three were run on branch `ticket/411-reload-adr` at master `95e5cec`, on an
Apple M1 Pro, with a release build of `goat`.

### 1. How goat compiles top-level references inside a closure

**A reference to a top-level value is captured into the closure's
environment, by value, when the closure is built. A reference to a top-level
function is not captured: each use is a direct call or a re-materialized
closure.** The rule is in `checker/src/captures.rs` (`capture_sets`: a free
variable is a capture; "a referenced function binding contributes that
function's captures instead of itself") and `mir/src/mono.rs` ("Function
bindings are never captured: each use re-materializes them").

The probe program:

```
speed = 5
bump = program(n) do n + speed done
make = program(k) do {x: 0, step: program(self) do {...self, x: self.x + speed + k} done} done
make(1).step().x
```

lowers (`goat_mir::mono`, printed with `{:#?}`, trimmed) to:

```
f0 (root):   Let L0 = Const Int 5                     -- speed
             ... CallClosure(MakeClosure(f1, [L0]), [Const 1])   -- make(1), env = [speed]
f1 (make):   env captures: [Int]                      -- speed
             AllocRecord(layout0, [MakeClosure(f2, [Capture 0, Local 0]), Const 0])
                                                      --  step's env = [speed, k]
f2 (step):   env captures: [Int, Int]                 -- Capture 0 = speed, Capture 1 = k
             ReuseRecord(L0, layout0, [Field(L0,0), ... Capture 0 ... Capture 1 ...])
```

Consequences for the rule "captures only top-level names":

- The check is cheap and static. `Checked.captures` already maps each function
  literal to its capture list, and it is computed once and shared by the order
  check and by mono. A method rebinds exactly when every symbol in its capture
  list is bound by the root let-chain. In the probe, `step` captures `speed`
  (top level, fine) and `k` (a parameter of `make`), so the method resets and the
  reason names `step` and `k`.
- A top-level value captured by a closure is a copy of the value made at
  `goat_setup` time. A rebound closure built by the new module therefore sees
  the new module's values, which is the behavior a kid expects after editing
  `gravity = 600`.
- `bump` is unused, so mono emitted nothing for it; a top-level function that a
  method calls costs no capture, and after a reload the new method calls the new
  function directly.
- The new module can build any rebinding target at setup: every capture of a
  qualifying method is a root-chain symbol, and the root function holds all of
  them as locals. Setup would end by filling a site table (site key to a
  closure built over those locals), which `goat_refresh` reads. This is the one
  piece of codegen the contract needs that no existing stage already does.
- Site uniqueness is by source site, not by mono instance: a polymorphic
  function that mono specializes twice still has one source literal, one key.

### 2. Which methods rebind and which reset under the site-key rule

Interactive programs in `examples/` and `examples/canvas/`: none puts a method
in its model today (the checker forbids it), so every one of them would
**refresh with nothing to rebind**. The refresh rebuilds by name, so each
refreshes unless the edit changes a field or tag.

| Program | Model | Methods in the model | Result under the rule |
|---|---|---|---|
| `examples/interactive.goat` | `{ticks, x, y}` | none | refresh |
| `examples/arrow_draw.goat` | `{x, y, path: List({x, y})}` | none | refresh (the list is rebuilt by name) |
| `examples/shapes.goat` | `{x}` | none | refresh |
| `examples/canvas/bounce.goat` | `{x, y, vx, vy}` | none today | refresh; becomes the headline starter in phase 2 |
| `examples/canvas/catch.goat` | `{basket, coin_x, coin_y, score}` | none | refresh |

Programs with methods (none is interactive, so none reloads today; each
lists what its methods would do if its record were a model):

| Program | Method sites | Captures | Result |
|---|---|---|---|
| `examples/spread_update.goat` | `(counter, bump)` | none | rebind |
| `examples/closure_shapes.goat` (`r::f`, `r::g` have no `self`) | not methods | `offset` (top level) | a plain function: checker error in a model (decision 6), fine outside it |
| `checker/tests/self_methods.rs`, `cli/tests/self_methods.rs` three-method model | `(init, update)`, `(init, nudge)`, `(init, draw)` | none (they reach the record through `self`) | rebind all three |
| same files, `ball`/`big` extension | `(ball, moved)`, inherited by `big` | none | rebind; `big` keeps `ball`'s key |
| same files, `other = {...ball, twice: …}` | `(ball, moved)`, `(other, twice)` | none | rebind both |
| same files, `make(n)` in a list | `(make, get)` once, on every element | none | rebind each element by key (not by index) |
| same files, five chained `m0 … m5` | `(r, m0)` … `(r, m5)` | none | rebind |
| error-case programs (`self` outside a record, `self` not first, dot-call on a plain function, a method that drops its methods) | not valid | n/a | rejected before any reload |

So across every program on master, **no method resets** under the rule: all
capture nothing or only top-level names, and all keys are unique within their
program. The rule's reset paths (`method_captures`, `ambiguous_site`) have no
example on master; phase 2 must construct them in tests. Two hand-built cases
would exercise them (the first is the probe's own capture list; the second
follows from the key definition, and neither is run yet):

- `make = program(k) do {step: program(self) do self.x + k done, ...} done`:
  `step` captures the local `k`, so it resets with `method_captures(step, k)`.
- Two literals with the label `update` inside one top-level binding (for
  example `if c then {update: program(self) …} else {update: program(self) …}`):
  the key `(b, update)` is not unique, so it resets with
  `ambiguous_site(update)`.

### 3. Snapshot plus refresh cost for 1,000 balls

`FRAME_BUDGET_MS` is **1000 ms** (`web/loop.ts` line 25); `guarded` stops the
loop when one call into goat exceeds it. The reload runs its calls inside
`around`/`guarded` in the same way.

The prototype is a throwaway goat program, not the generated code, compiled
with `goat build` (release) and run in Node 26.13 (V8) through
`web/runtime.ts` `run`. A ball is `{x, y, vx, vy, update, draw}` with both
methods capturing the top-level `speed`, so each ball is one record plus two
heap-allocated closures. The model is a list of N balls.

- `build` constructs the list and walks it once (the baseline: module
  instantiate, start, N allocations, one pass).
- `frame` adds one `update` over every ball, so it is a normal frame.
- `snapshot` adds a data-only copy of every ball (a 4-field record, no methods).
- `snapshot_refresh` adds the rebuild with fresh method closures.

Median of 40 runs, milliseconds, each run including `WebAssembly.instantiate`:

| N | build | frame | snapshot | snapshot + refresh | refresh cost over build |
|---|---|---|---|---|---|
| 100 | 0.09 | 0.10 | 0.10 | 0.11 | 0.03 |
| 1,000 | 0.17 | 0.21 | 0.22 | 0.30 | 0.13 |
| 3,000 | 0.33 | 0.44 | 0.48 | 0.63 | 0.30 |

For 1,000 balls the snapshot-and-refresh work costs about **0.13 ms** over the
baseline, **0.30 ms** in all, against a **1000 ms** budget: 0.03% of it. It is
also about the cost of one normal frame (`frame` 0.21 ms). Allowing a 5x
penalty for the real image (names interned to ids, a version header, a tag
byte per node) still leaves it under 2 ms.

What the prototype does not measure, and why it is still enough to decide:

- It allocates the image in the goat heap rather than writing a flat buffer.
  The real snapshot writes a few stores per field into linear memory, which is
  no more work than the allocation it replaces.
- It copies no strings. See open question 3.
- **Depth, not time, is the limit.** The non-tail recursive walk over a
  10,000-element list overflowed V8's default stack (`RangeError: Maximum call
  stack size exceeded`), while 3,000 ran. A generated snapshot and refresh that
  recurse down a list inherit that limit. The prototype source is on the
  unmerged branch `spike/411-reload-measure` (`spike/411/measure.ts`).

## Apple host parity

The Apple host loads the same `web/embed.html` bundle in a `WKWebView`
(`hosts/apple/README.md`), and the reload logic lives in `web/loop.ts` and
`web/worker-core.ts`, so the new contract reaches it by re-vendoring the bundle
(`hosts/apple/scripts/stage-web.sh`). Swift has no reload code today
(`grep -i reload` over `hosts/apple` finds nothing): the follow-up is a native
trigger that posts the recompiled module to the bundle, and a place in
`EditorScreen` to show the status copy. The reason strings come from the bundle,
so the Swift side shows a string and needs no copy of the table (ADR 0018: no
goat behavior re-expressed in native code).

## What changes in phase 2 (inventory, not a plan)

- `checker/src/infer.rs`: the model-holds-a-function rule accepts a `METHOD`
  field and rewords the plain-function error.
- A MIR pass that generates `goat_snapshot`, `goat_refresh` and the site table;
  `wasm` exports them; the interpreter runs them.
- `mir/src/fingerprint.rs`, `goat_model_fingerprint` and the comparison in
  `web/loop.ts` are removed.
- `web/loop.ts` (`Reloaded`, `reload`), `web/worker-core.ts`, `web/protocol.ts`
  (`reloaded` message), `web/supervisor.ts` (`onReloaded`), `web/index.html`
  (`RELOAD_SAYS`) take the new outcome shape; `web/canvas.test.ts` and
  `web/loop.test.ts` cover it.
- ADR 0015's addendum and ADR 0020 §4 get a note that the fingerprint is gone:
  tag numbering no longer affects reload, because the image names its tags.

## Risks and open questions

1. **Renaming a top-level binding resets every method under it**, because the
   key's first half changed. A kid who renames `init` to `make_ball` sees
   "got a new method" for methods they did not touch. Options: key on label and
   arity only (collides more, so more `ambiguous_site` resets), or keep the
   rule and word the reason well. This ADR keeps the ticket's rule.
2. **A shared value becomes two.** The image is a tree. A model that holds one
   record in two places (immutable, so harmless) comes back as two copies, and
   a model that nests shared values deeply can make the image exponentially
   larger than the heap. The snapshot needs a size cap that resets with
   `too_large`. The cap's number is not decided here.
3. **Strings.** Strings are immortal and the heap is shared (ADR 0009, ADR 0015
   addendum §2), so a string pointer in the image would stay valid. Copying
   instead honors "no object crosses modules" but allocates an immortal string
   per string field per reload, a leak proportional to model size times
   reloads. Recommended: carry the pointer for strings only, and say so in the
   image format, because immortality makes it safe and copying makes a
   1,000-ball model with a `color` string leak a few kilobytes per edit.
4. **Stack depth on long lists** (measured above). The generated walk must not
   recurse once per list element, or a model of several thousand balls cannot
   reload even though it runs. This needs either a loop form in MIR or an
   accumulator form the existing tail-call support handles.
5. **Static data still accumulates.** Each reload leaves the new module's static
   block in the heap (ADR 0015 addendum, Consequences). After refresh nothing in
   the new model points into the old module's block, so it could be freed; this
   ADR does not require it. `goat_live_allocs` is zero already because that block
   hands its count back.
6. **Mono-instance sites.** One source literal can have several specializations
   with different layouts. The site table must hold the closure for the
   specialization whose layout the refreshed record uses; two specializations of
   one site are one key. Phase 2 must test a method literal inside a polymorphic
   function used at two types.
7. **A reset still re-enters the host's fresh model**, so a reset throws away
   the ball's position, as today. Nothing in this ADR makes a reset gentler.

## Recommendation

**Build phase 2, with the design unchanged.** The three gates pass:

- "captures only top-level names" is a subset test over capture sets the
  checker already computes, with no new analysis;
- no method in any program on master resets, so the rule is not hostile to the
  programs we ship; and
- snapshot plus refresh for 1,000 balls is about 0.3 ms against a 1000 ms
  budget, three orders of magnitude of headroom, so the cost of copying the
  model by name is not a reason to prefer a cheaper, riskier mechanism.

Phase 2 should settle open questions 2, 3 and 4 first, since each shapes the
image format, and should include tests for the two reset paths that no program
on master reaches (`method_captures`, `ambiguous_site`).
