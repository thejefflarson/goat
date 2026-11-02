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
