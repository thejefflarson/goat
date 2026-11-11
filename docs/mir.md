# MIR — goat's mid-level IR

MIR is the seam between the type checker and the backends. It is first-order,
explicitly typed, and backend-neutral: mono emits it, the reference interpreter
and the wasm backend consume it, and a future native backend could too. What
MIR *cannot* make cheap is what is baked into it — the memory model, mono
layouts, closure representation, number representation, and control-flow shape —
so those are settled here before code depends on them. The one-way-door choices
are recorded as ADRs ([0001](adr/0001-number-representation.md) numbers,
[0002](adr/0002-object-header.md) object header) and summarized below.

Status: design spec for Phase 1.5, implemented by the `goat_mir` crate (`mir/`)
and validated by the five hand-written hard cases in `mir/tests/hard_cases.rs`
(see Hard cases below).

## Values and types

Every MIR value has a ground `MTy` (mono has erased all type variables):

```
enum MTy {
    Int,            // target integer, width is a target parameter (i32 on wasm32)
    Float,          // target float, width is a target parameter (f64 host/web, f32 embedded)
    Bool,           // i32 0/1
    Unit,           // zero-sized; erased (see below)
    Ptr(HeapKind),  // pointer into linear memory to a heap object
}

enum HeapKind { Record(LayoutId), Variant(LayoutId), Str, Closure(SigId), List(LayoutId) }
```

- **Numbers** follow [ADR 0001](adr/0001-number-representation.md): MIR carries
  both `Int` and `Float` with per-target widths; the checker still exposes a
  single `Number` this sprint, which lowers to the target `Float`.
- **`Unit` is erased.** A `Unit`-typed *value* produces no runtime value and no
  stack slot. `Unit`-typed *calls* are not erased — see Effects.
- **Pointer size is a target parameter** (wasm32 = 4 bytes; a 64-bit native
  target = 8). Field offsets are computed per target, never hard-coded.

## Memory model

Linear memory, our own allocator, **reference counting** (Perceus-style), **no
GC**. goat is immutable, so data cannot form cycles; only functions
self-reference, and a closure refers to its own binding through its `env`,
never storing itself ([ADR 0003](adr/0003-binding-semantics.md)) — so RC is
sufficient and complete.

### Object header ([ADR 0002](adr/0002-object-header.md))

Every heap object begins with `{ rc: u32, _pad: u32 }` (8 bytes, keeps fields
8-byte aligned). Drop dispatches by **static per-layout drop functions** the
compiler emits — plus closures' own `drop_fn` and variants' tag — so the header
carries no type id. `_pad` is reserved for a type/drop id only if a later phase
proves one is needed.

`rc == u32::MAX` is the **immortal sentinel**: literals and static (top-level)
closures carry it and skip every inc/dec.

### Layouts

After mono every record/variant type is closed, so each has a fixed layout
keyed by `LayoutId`:

- **Record:** `[header][field0][field1]…`, fields sorted by label, each at its
  natural width, 8-byte aligned. `Field(rec, index)` names the field by
  **index** into the layout, not by byte offset: offsets depend on the target's
  pointer and number widths, so each backend computes them from the layout. A
  label a spread shadows (`{...p, x: …}` over a `p` that has an `x`) gets a
  single slot — the layout keeps the first occurrence of each label
  (`canon::layout_fields`) and the shadowed value is dropped, so a record holds
  exactly one slot per label ([ADR 0011](adr/0011-lacks-constraints-for-record-restriction.md)).
- **Variant:** `[header][tag: u32][payload…]`. Each tag label gets one global
  tag number (labels sorted, numbered from 0), so a layout's `Vec` of payloads
  is indexed by that number and is empty for tags the type does not have.
  `match` loads the tag and `br_table`s. Nullary tags are immortal static
  objects, one per tag. A payload is stored flat: `Tag(a, b)` has slots `a`,
  `b`, not a pointer to a record, and `Unit` has none. On wasm32 the tag is a
  `u32` at offset 8 and the payload slots start at offset 16.
- **Recursive variants:** a recursive type's layout names itself (`Link`'s
  tail slot points at the same `LayoutId`). Mono keys layouts and
  specializations on a *canonical* form of the type: the minimal automaton of
  its infinite tree, written as a `μ`-term with binders numbered by depth
  (`mir/src/canon.rs`). Types equal up to `μ`-equivalence get one layout and
  one specialization; a layout is registered before its payloads are lowered,
  so lowering a self-referential type terminates.
- **Variant families:** a value matched at two widths (`[A]` and `[A, B]`) must
  carry one `LayoutId`, so mono keys a variant layout on a *family*, not on the
  exact type. A type joins the first family it shares a tag with and agrees with
  on every shared tag's payload (nested variants compared by family); its tags
  are added to the family's table. The layout is width-independent: a cell is
  sized and dispatched by its stored tag, and members agree on shared tags
  because row unification only equates two uses of a value when they do. Types
  that give one tag different payloads (`Some(1)`, `Some(true)`) get separate
  families.
- **String:** `[header][len: u32][bytes…]`; literals live in a `data` segment
  and are immortal.
- **Closure:** `[header][drop_fn: i32][code: i32][captures…]` (see Closures).
- **List** is not special in the compiler — it is the prelude variant
  `Empty | Link(first, rest)` and uses the variant layout.

### Allocator interface

The allocator must support both size-class free lists over a bump region
(desktop/web) and **fixed-size pools inside a compile-time-declared heap
budget** (microcontrollers, which cannot afford 64 KB `memory.grow` steps). A
target declares its heap strategy; MIR does not assume `memory.grow` is cheap or
even available.

Dropping is iterative. A drop function (one per record/variant layout and per
closure body) releases the references an object holds but does not recurse:
a child whose count reaches zero is pushed on a pending list threaded through
the dead objects (the dead object's `rc` word is the link, and the high bits of
its `_pad` word hold the table slot of its own drop function). The runtime's
`drop_loop` frees the object, pops the next, and repeats, so tearing down a
million-element chain uses one call frame. A drop function never calls another.

The wasm backend implements the free-list strategy (`wasm/src/allocator.rs`).
`alloc` records the block's size class in the header's `_pad` word, so `free`
needs no size from the caller; a freed block has `rc == 0` and a poisoned
payload, which turns a second release into a trap. The live-allocation count
(`goat_live_allocs`) moves only on a real `alloc` and `free`, never for
immortal objects.

## Ownership convention

Start with **owned parameters** (Perceus): a callee consumes the pointers it is
passed. It is the simplest convention and fixes the calling convention. Room is
reserved for a later **borrowed-parameter** pass (Lean-style) that elides RC
traffic; MIR nodes are written so that pass can be added without changing the
node set.

RC operations are explicit nodes inserted by a dedicated pass (#Phase 6), not
implicit:

- `Dup(local)` before a use when the local is used again later.
- `Drop(local)` for an owned local that is otherwise unused, at scope end and at
  the start of each branch that does not consume it.
- The last use of an owned local transfers ownership (no `Dup`).

Loads and destructuring come in two forms, settled by the `map` hard case:

- **Borrowing loads** — `Field`, `Payload`, `Capture`, and `Switch`'s scrutinee
  — leave the source owned by its local. A pointer they load is a fresh owned
  reference (an implicit `Dup`), so a read never invalidates its source.
- **Consuming destructure** — `Unpack(x, tag, binds, body)` — requires `x` to
  be its sole owner (`Live(1)`). It moves the payload fields into `binds` as
  owned locals and turns `x` into a **reuse token** that exactly one of
  `ReuseVariant(x, layout, tag, fields)` or `Free(x)` must consume; any other
  use, or leaving it unconsumed, is a verifier error.

Implicit-dup loads alone cannot express `rc == 1` reuse: loading a child bumps
its count, so the child of a unique cell is never unique and the recursion in
`map` always copies. `Unpack` is Perceus's `drop-reuse`. At runtime, if the cell
has `rc == 1` the fields move out with no RC traffic and the token is the
hollow cell, which `ReuseVariant` refills in place and `Free` releases; if the
cell is shared, `Unpack` increments each field, decrements the cell, and the
token is empty, so `ReuseVariant` allocates fresh and `Free` does nothing. Both
paths are the same MIR, so the verifier checks ownership once and uniqueness is
a runtime fact. `ReuseVariant` requires the token's cell and the new layout to
have the same maximum payload size, which keeps reuse to same-sized cells.

This sizing rule predates variant-family merging (ADR 0010): a merged family's
`Layout::Variant` table is the union of all members' tags, so its `max_payload`
over-approximates any one member. When the reuse pass lands it must size the
token by the **actual stored tag's** payload, not the family table's maximum, or
it will reserve against an over-approximated size.

## Closures

`MakeClosure` and `CallClosure` are abstract so the lowering can be a heap
closure (the general fallback) or a Roc-style lambda set (defunctionalized, no
allocation) when mono knows the target set.

- General lowering: a closure is a heap object `[header][drop_fn][code][captures…]`.
  All closures of one goat function type share the wasm signature
  `(env: i32, args…) -> ret`. Calling a function value loads `code` and
  `call_indirect`s with the closure as `env`. Calling a record field
  (`r.f(x)`) is the same path.
- Top-level functions used as values get a static, immortal closure.
- **Self-reference rule** (prevents RC cycles): inside a closure body, a
  reference to its own binding compiles to the current `env`; a closure never
  stores itself.

## Control flow

Structured only — trees, no arbitrary CFG — so it maps directly to wasm
`block`/`if`/`br_table` with no relooper (and to a `FunctionBuilder` if a native
backend is ever added):

```
If(cond, then: Block, else: Block)
Switch(scrutinee, arms: [(tag, Block)], default: Block)   // Phase 7
Loop(body: Block)                                          // for the prelude's loops
TailCall(callee, args)   // explicit; wasm return_call / return_call_indirect
```

`TailCall` is a distinct node so self- and mutual recursion compile to constant
stack. A bounded stack with a clear **"stack overflow" trap** is a requirement,
not a nicety — microcontroller stacks are a few KB, and drop functions over long
lists must iterate, not recurse.

## Effects and failure

- **Effectful calls are never dropped, duplicated, or reordered**, even when
  they return `Unit`. Value erasure applies to `Unit` *values*, not to the
  *calls* that produce them. A host call is its own node, `CallForeign`, and
  `effects(expr)` lists the foreign calls and writes of a function in
  evaluation order. `insert_rc` asserts that list is the same before and after
  it runs, so a pass that dropped, duplicated or reordered a call fails loudly.
- **Foreign calls cross by borrowing.** `CallForeign(import, locals)` takes
  locals so that a pointer argument is borrowed for the call, like
  `Write(Str(x))`; the caller keeps its reference and drops it afterwards. A
  string result is a fresh owned reference: on wasm the host allocates it with
  the exported `goat_alloc`, which returns a block with `rc = 1`, then writes
  the length (`u32` at offset 8) and the bytes (from offset 12). A string passed
  to the host is read from the same two offsets.
- **`Trap(message)`** is the single runtime-error node — `first([])`, a failed
  bounds check, a stack-overflow guard. A trap aborts with the message; it is
  not catchable in v1. User-facing *static* errors still come only from the
  checker; a reachable `Trap` is a legitimate runtime failure, not a compiler
  bug.

## The node set (Phase 2b sketch)

```
struct Program { funcs: Vec<Func>, entry: FuncId, layouts: Vec<Layout>, data: Vec<Bytes> }
struct Func { params: Vec<(Local, MTy)>, env: Option<Local>, ret: MTy, body: Block }

enum Expr {
    Const(Const), Local(Local), Let(Local, Box<Expr>, Box<Expr>),
    BinInt(IntOp, a, b), BinFloat(FloatOp, a, b), Cmp(CmpOp, a, b),
    If(cond, then: Block, else: Block),
    Switch(scrutinee, arms, default),          // Phase 7
    CallDirect(FuncId, args),                  // known callee, no env
    CallClosure(closure, args),                // unknown callee: call_indirect
    TailCall(Callee, args),
    MakeClosure(FuncId, captures),
    AllocRecord(LayoutId, fields), Field(rec, index),
    AllocVariant(LayoutId, tag, payload),      // Phase 7
    Payload(variant, tag, index),              // borrowing load, like Field
    Unpack(x, tag, binds, body),               // consuming destructure -> token
    ReuseVariant(token, LayoutId, tag, payload), Free(token),
    Capture(index),                            // read a closure capture
    StrLit(DataId),
    StrEq(a, b),                               // bytes equal; borrows both strings
    StrLen(s), StrByte(s, i),                  // UTF-8 byte count; byte at 1-based Int i, traps outside
    StrChars(s), StrChar(s, i),                // code-point count; new rc=1 string of the code point at 1-based i, traps outside
    Write(Number(e) | Str(x) | Lit(data) | End), // host output line; Unit
    CallForeign(import, locals),               // host function; effectful; borrows pointers
    Dup(Local), Drop(Local),                   // Phase 6, inserted by the RC pass
    Trap(message),
}
```

`Unit`-typed sub-expressions are erased during lowering to wasm.

## Hard cases and their wasm lowering

Each is a hand-built `goat_mir::Program` in `mir/tests/hard_cases.rs`, accepted
by the verifier and run by the interpreter with zero live allocations at exit.
`rc` ops below are the inline sequences from the header; "static" means an
immortal object.

1. **Closure capturing an outer value.** `MakeClosure(f, [r])` moves `r` into
   the capture slot; the callee reads it with `Capture(0)` (an implicit dup)
   and drops `env` before returning. Lowering: `alloc(16 + 8*ncaptures)`, store
   `rc=1`, `drop_fn`, the table index of `f`, and the captures. Each closure
   signature is a wasm type `(env: i32, args…) -> ret`; `CallClosure` loads
   `code` from `env+12` and does `call_indirect`, passing the closure pointer
   as the first argument. `Capture(i)` is a load at `env + 16 + 8*i` followed by
   an `rc` increment if the capture is a pointer. `drop_fn` decrements each
   pointer capture and frees the closure.
2. **Self-recursive local closure.** The body calls itself through `env`, the
   closure it was called with, so the closure never stores itself and the
   capture list has no cycle. A tail call (`go(n-1, acc+k)`) passes `env`
   straight on (ownership moves, no `Dup`) and lowers to `return_call_indirect`
   with the same `env`; the non-tail form `Dup`s `env` before the call and
   `Drop`s after. Stack depth is constant for the tail form (tested at 1000
   iterations against an interpreter depth limit of 128).
3. **Recursive `length` over `Empty | Link`.** `Switch` on the tag becomes
   `local.get xs; i32.load (tag); br_table`. The `Link` arm is `Unpack`: load
   the head and tail from the payload slots, then `Free` the cell (when unique)
   or decrement it and increment the tail (when shared), selected by one
   `rc == 1` test. The recursion is `call`; an accumulator form would use
   `TailCall` and `return_call`. Nullary tags (`Empty`) may be static objects, in which case
   `Unpack` and `Drop` never see them.
4. **`map` with in-place reuse.** The `Link` arm is `Unpack`, then a closure
   call on the head, a recursive `map` on the tail, and `ReuseVariant`. Lowering
   emits `if (rc == 1)` once at `Unpack`: the unique path loads the fields and
   keeps the cell's address in a wasm local as the token; the shared path
   increments both fields, decrements the cell, and sets the token to 0.
   `ReuseVariant` becomes `if (token != 0) { store tag + fields into token }
   else { alloc + store }`, and `Free` becomes `if (token != 0) { free }`. A
   unique list is mapped with no allocation beyond the closure; a shared list
   leaves the original intact (both tested).
5. **Record of functions called as `r.f(x)`.** `AllocRecord` of two closures
   stores them at their field offsets; `Field(r, 0)` is a load plus `rc`
   increment, and the call is exactly case 1's `call_indirect` path with the
   loaded closure as `env`. `r` is dropped after the last call. Top-level
   functions placed in the record use their static immortal closures, so no
   allocation or `rc` traffic happens for them.

## Validation (how we know this is right)

MIR is proven out *before* mono emits it (#13): a verifier (#11) checks that
types line up, every owned pointer is consumed exactly once on every path,
there is no use after `Drop`, and control flow is well-formed — run after every
pass in debug/tests. A small reference interpreter (#11) tracks live
allocations, so leaks and double-frees fail tests immediately, and becomes the
differential-testing oracle for the wasm backend. The five hard cases (#13) —
a capturing closure, a self-recursive local closure, `length` over
`Empty | Link`, `map` with `rc == 1` reuse, a record of functions called as
`r.f(x)` — are hand-written, verified, and run in the interpreter before any
backend builds on MIR. Anything awkward changes MIR now, while it is cheap.
