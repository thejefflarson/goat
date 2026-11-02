# MIR — goat's mid-level IR

MIR is the seam between the type checker and the backends. It is first-order,
explicitly typed, and backend-neutral: mono emits it, the reference interpreter
and the wasm backend consume it, and a future native backend could too. What
MIR *cannot* make cheap is what is baked into it — the memory model, mono
layouts, closure representation, number representation, and control-flow shape —
so those are settled here before code depends on them. The one-way-door choices
are recorded as ADRs ([0001](adr/0001-number-representation.md) numbers,
[0002](adr/0002-object-header.md) object header) and summarized below.

Status: design spec for Phase 1.5. No code depends on it until #11 builds the
crate and #13 validates it with hand-written hard cases.

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
  natural width, 8-byte aligned. `Field(rec, offset)` is a load at a constant
  offset.
- **Variant:** `[header][tag: u32][payload…]`. Each tag label gets one global
  tag number; `match` loads the tag and `br_table`s. Nullary tags may be
  immortal static objects.
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
  *calls* that produce them. Mono marks foreign/effectful calls so later passes
  preserve them exactly.
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
    AllocRecord(LayoutId, fields), Field(rec, offset),
    AllocVariant(tag, payload),                // Phase 7
    StrLit(DataId),
    Dup(Local), Drop(Local),                   // Phase 6, inserted by the RC pass
    Trap(message),
}
```

`Unit`-typed sub-expressions are erased during lowering to wasm.

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
