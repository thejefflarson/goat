# ADR 0002 — Heap object header is `{ rc, _pad }`; drop dispatches by static layout

- Status: accepted (2026-11-01)
- Context: Phase 1.5 (MIR design), `docs/plan.md`

## Context

Every heap object (record, variant, string, closure, list cell) carries a
header. `docs/plan.md` flags the header's contents as "painful to change
later" and asks whether it must also carry a drop/type id. Reference counting
(Perceus-style, no GC) needs the `rc` field; the open question is how a `Drop`
at `rc == 0` finds the right per-object teardown.

The alternatives:

1. **No type id; drop by static layout.** The compiler knows each allocation
   site's layout, so it emits a per-layout drop function and calls it directly.
   Closures already carry their own `drop_fn` pointer; variants carry a tag that
   selects the arm. So the header rarely needs a type id.
2. **Type/drop id in the header.** Every object stores an id used to look up a
   drop routine at runtime. Simpler dynamic dispatch, but costs a header word on
   every object and bakes a runtime table in.

## Decision

- Header is **`{ rc: u32, _pad: u32 }`** (8 bytes, keeping fields 8-byte
  aligned).
- **Drop dispatches by static per-layout drop functions** the compiler emits,
  plus closures' own `drop_fn` and variants' tag. No type id in the general
  header.
- The `_pad` word is **reserved**: if a later phase proves a type/drop id is
  genuinely needed (e.g. a uniform dynamic-drop path), it goes there without
  changing object size.

## Consequences

- No per-object id word to maintain or get wrong; drop is a direct call the
  compiler already has the type information to emit.
- Padding is spent anyway for alignment, so reserving it is free.
- `rc == u32::MAX` is the immortal sentinel (literals, static closures) that
  skips inc/dec — unaffected by this decision.
- Deferred: a fully uniform runtime drop table, should one ever be needed, lands
  in the reserved word.

### Amendment 2026-11-03 (#92, Phase 7 P7d)

Iterative teardown borrows two header words of an object that is already dead.
When a drop function finds a child's count reached zero, it pushes the child on
a pending list: the child's `rc` word (now 0, and unreferenced) holds the link
to the previous head, and the high 24 bits of `_pad` hold the funcref-table
slot of the child's own drop function. `drop_loop` clears both before it calls
`free`, so `free` still sees `rc == 0` and a bare size class, and a live or
freed object never carries either. This is the "type/drop id in the reserved
word" this ADR deferred, used only transiently and only on the wasm backend;
objects still carry no type id while alive.

### Amendment 2026-11-03 (#131, Phase 6 P6b)

The wasm free-list allocator (`wasm/src/allocator.rs`) now stores each block's
size class in `_pad`. `free` runs at `rc == 0` with no size from the caller — a
closure's captured count is not static at the release site — so it recovers the
class from the block itself, as a free-list allocator conventionally does. The
class needs 55 distinct values and so occupies the low 8 bits; a future
type/drop id can still share the word in the high 24 bits, at which point `free`
masks `_pad & 0xFF`. This binds `_pad` only in the wasm backend: the interpreter
and the embedded fixed-pool strategy keep the word free, so the reservation above
is narrowed, not spent.
