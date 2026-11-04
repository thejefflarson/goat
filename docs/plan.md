# goat: plan

Working plan for taking goat from a Cranelift native backend to an
embeddable language with a single WebAssembly backend (browsers, iOS,
desktop, microcontrollers, any wasm host), with variants, recursive
data, a kid-friendly prelude, and turtle graphics. Phases are ordered; each
ends with something that runs and passes tests.

## What goat is

**A typed, GC-free, live-codable scripting language for creative tools,
embeddable anywhere WebAssembly runs, simple enough that kids start with a
turtle.**

- **Embeddable like Lua**, but statically typed (hosts type-check scripts
  against their API), sandboxed by construction (a script can only call what
  the host hands it), and pause-free (reference counting, no GC).
- **Creative coding first.** Hosts: the turtle app (first), a p5-style web
  canvas, game engines, visual/audio tools. Elm-style `init`/`update`/`draw`
  plus hot reload with state preserved = live coding.
- **Language levels.** Kids: turtle, structural records/variants, prelude.
  Artists: canvas/audio APIs. Host authors: WIT, FFI, named types. Same
  language; hosts choose the level.
- **Size target: Lua-scale** (tens of thousands of lines), not Roc-scale. Stay
  narrow: one IR, one backend, one host model.
- **Learn from Roc** (closest relative: structural records/tags, inference,
  RC, mono, platforms): study its lambda sets (closures without heap
  allocation via defunctionalization under mono) and its platform/host model.

## Decisions (settled — don't relitigate)

### Platform and backends
- **Targets:** browser, iOS, desktop, any host embedding a wasm runtime, and
  later microcontrollers (Phase 12). Embedded is reached only through wasm
  (WAMR / `wasm3` / `wasm2c` → vendor C toolchain); Cranelift has no 32-bit
  ARM (Cortex-M), Xtensa, or riscv32 backend.
- **One backend: WebAssembly**, emitted from MIR with `wasm-encoder`. It's
  the only path to browsers, the iOS web view, and microcontrollers, and it
  keeps the sandbox that makes goat embeddable.
  - Native code on desktop still comes from Cranelift: goat → `.wasm` →
    Wasmtime → Cranelift → machine code. (Cranelift can't emit wasm; Wasmtime
    *uses* Cranelift to compile wasm.)
  - **The direct Cranelift backend is deferred** until there's a measured
    need for it (see "Later"). The current Cranelift code is removed in
    Phase 2 and stays in git history.
  - MIR stays backend-neutral (structured, pointer size a target parameter) so
    a second backend can be added without redesign.
- **Wasm toolchain (Rust crates, Bytecode Alliance):**
  - `wasm-encoder` — build modules (sections + instructions).
  - `wasmparser` — validate every emitted module in tests/debug builds.
  - `wasmprinter` — wasm text for golden tests and debugging.
  - `wit-parser` / `wit-component` — WIT-based FFI and components (later).
  - `wasm-opt` (Binaryen) — optional post-pass; skip initially.
  - Not `walrus`: MIR already serves as the transform IR.
- **MIR is structured** (trees of `If`/`Switch`, no arbitrary CFG), so it
  maps directly to wasm `block`/`if`/`br_table` with no relooper (and to
  Cranelift's `FunctionBuilder`, if that backend is ever added).
- **Execution modes come from runtimes, not extra goat backends:**

  | Mode | How | Where |
  |---|---|---|
  | JIT | wasmtime (Cranelift) | CLI, desktop hosts, hot reload |
  | JIT | browser engine | web, iOS web view |
  | AOT | wasmtime precompiled modules (`.cwasm`) | servers, desktop, fast startup |
  | AOT to C | `wasm2c` / `w2c2` → C linked into host | consoles, embedded, native iOS apps |
  | Interpreter | wasmtime Pulley, `wasm3`, WAMR | JIT-banned hosts loading scripts at runtime |

- **The compiler is a library first:** `goat::compile(source, host_interface)
  -> wasm`, with the CLI as one client. Compiler crates must build for
  `wasm32-unknown-unknown` so browsers/iPads (and any wasm host) compile goat
  locally. Keep native-only deps (wasmtime, filesystem, `cc`) out of them.

### Memory and representation
- **No GC.** Not wasm GC, not a tracing collector. Wasm linear memory, our own
  allocator, **reference counting** (Perceus-style). Goat is immutable, so
  cycles cannot form (see the closure self-reference rule, Phase 4).
- **Whole-program monomorphization.** Every polymorphic function is specialized
  per concrete type before codegen. Consequences:
  - No uniform value representation, **no NaN-boxing, no pointer tagging**.
  - The compiler knows statically which values are pointers → RC ops only on
    those.
  - Row-polymorphic records get a fixed layout per instance → field access is a
    constant offset.
- **Numbers are decided in Phase 1.5, not later.** `f64`-everywhere is wrong
  for microcontrollers (RP2040: no FPU; ESP32: single-precision only), so
  plan for an `Int`/`Float` split with a per-target float width (`f64`
  desktop/web, `f32` embedded). Keep `Number` as the kid-facing name if the
  split stays mostly invisible (e.g. literals default to `Int` unless they
  have a decimal point).

### Language
- **Functional language.** First-class closures, capture by value, immutable.
- **No user-defined operator overloading.** Records have no names to hang
  instances on, and with structural rows overlapping instances are incoherent.
  Ad hoc polymorphism comes from a **fixed set of built-in constraints**
  (Elm-style): `eq` (`==`, any type except functions), `appendable` (`join`
  on strings and lists), and **field-wise arithmetic** on records whose fields
  are all numbers (`{x:1, y:2} + {x:3, y:4}`).
- **Interfaces are records of functions** (`vec.add(p, q)`); row polymorphism
  makes any record with the right fields fit.
- **Variants are structural and inferred** — no declarations. Capitalized names
  are always tags: `Circle(5)`, `Empty`, `Link(1, rest)`.
- **Recursive types are allowed only when the cycle passes through a variant
  tag** (OCaml's default for polymorphic variants). This makes `List` and
  `Tree` definable in goat with full inference, while `f(f)`-style mistakes
  keep their occurs-check error.
- **`List` is defined in the goat prelude**, not built into the compiler, as
  `Empty | Link(first, rest)`.
- **Kid-facing names are plain words** (Pyret/Logo/Scratch heritage), not CS
  jargon. See the prelude table in Phase 8.
- **List indexing is 1-based** (`item(xs, 1)` is the first item).
- **Named types are an advanced tier, not required.** Kids never write type
  declarations. Named types come later for teachers/library authors (see
  "Later").

## Known limitation (documented, not fixed yet)

**Lambda-bound parameters are monomorphic** (standard HM). A record bound with
`=` keeps generic fields generic; the same record passed as a parameter does
not:

```
m = {id: program(x) do x done}
a = m.id(1)  m.id(true)                       # OK

use = program(m) do a = m.id(1)  m.id(true) done
use(m)                                        # ERROR: Number vs Bool

both = program(f) do a = f(1)  f(true) done   # ERROR, no record needed
getx = program(p) do p.x done
use2 = program(g) do a = g({x: 1})  g({x: 2, y: 3}) done
use2(getx)                                    # ERROR (row mismatch)
```

Works: binding the record with `=` and referring to it directly; passing the
generic function once per type (`use(id, id)`); single-typed interfaces
(`draw(shape)`), which is the common case. Mitigation now: a targeted error
message (Phase 0). Possible fixes later: polymorphic fields on named types, or
rank-2 intersection inference (see "Later").

**Infinite record type through pure-extension spread.** An unannotated function
that recurses by spreading a field it never reads is an infinite record type and
is rejected with the occurs-check:

```
go = program(s) do go({...s, done: true}) done   # ERROR: infinite record type
```

`go` adds `done` to `s` without ever constraining `s`, so each call's argument
is `{done: Bool | row(previous)}` — a type with no finite form. Reading a field
first (`s.n`) pins `s`'s row and breaks the regress. A proper fix needs
presence/absence (lacks-style) typing carried in schemes — Phase 8 constraints
(#95). The `lacks` guard added for rest-after-shadow
([ADR 0011](adr/0011-lacks-constraints-for-record-restriction.md)) is the first,
targeted piece of that machinery.

## Target pipeline

```
source + prelude
  → parser (pest)                      [exists]
  → lower: HIR + name resolution       [exists]
  → infer: HM + scoped-label rows      [exists; Phases 1, 7, 8 extend it]
  → mono: specialize to concrete types [new: goat_mir]
  → closure conversion + lambda lift   [new: goat_mir]
  → RC insertion (dup/drop)            [new: goat_mir]
  → wasm emit                          [new: goat_wasm]
```

Goat-specific optimizations (mono, RC elision, reuse, known-closure inlining)
happen in MIR. Generic ones (register allocation, instruction selection) are
left to the engine that runs the output.

| Crate | Role |
|---|---|
| `parser`, `checker` | unchanged roles |
| `mir` (`goat_mir`) | mono, closure conversion, RC insertion; defines MIR |
| `wasm` (`goat_wasm`) | MIR → wasm bytes via `wasm-encoder` |
| `goat` (lib) | public API: `compile(source, host_interface)` |
| `cli` | `check` / `build` (emit `.wasm`) / `run` (wasmtime) |

The Cranelift `compiler` crate is removed at the end of Phase 2.
| `prelude/` | `prelude.goat`, `turtle.goat`, embedded with `include_str!` |
| `web/` (not a crate) | `runtime.js`, `index.html`, canvas turtle runtime |

---

## Phase 0 — Fix known bugs and sharp edges (small, do first)

- [ ] **Call syntax on any expression.** `s.f(x)` and `vec.add(p, q)` don't
      parse: `application` requires a bare `ident` callee. In `grammar.pest`
      make calls a postfix like field access — `term = primary ~ (access |
      call)*` — and drop the `ident` restriction. `hir::App` already takes an
      arbitrary callee. Records-of-functions are useless without this.
- [ ] `cli/src/main.rs`: `Some(0) | None => ExitCode::SUCCESS` reports a
      signal-killed child as success. `None` must be a failure.
- [ ] Type-mismatch messages are reversed: `1 + true` says
      "expected `Bool`, found `Number`" pointing at `true`. Make
      `unify(actual, expected, span)` order consistent at every call site in
      `checker/src/infer.rs`; add tests asserting message text.
- [ ] Missing-field message is backwards: `{x: 1}.y` says "record has an
      unexpected field `y`". It should say the record is missing `y`.
- [ ] **Targeted error for monomorphic parameters** (see Known limitation):
      when a parameter (or a field read off one) is used at two conflicting
      types, say so — "`m` is a parameter, so `m.id` can only be used at one
      type here; bind the record with `=` instead". Use the three failing
      examples above as tests.
- [ ] `x = x + 1  x` type-checks and only fails in codegen. Reject recursive
      bindings whose value is not a `program(...)`.
- [ ] `if c then e done` with no `else`: require the then-branch to be `Unit`
      instead of silently discarding its value.
- [ ] Grammar: `number` accepts a leading `-`, so `x = 5 -1` parses as
      `x = 5 - 1`. Drop `-` from the number token; add unary negation.
- [ ] Reject duplicate labels in a record literal (`{x: 1, x: 2}`).
- [ ] `.github/workflows/ci.yml`: stale comment about the compiler crate and
      system LLVM.

## Phase 1 — Checker outputs what mono needs

- [ ] Add `schemes: HashMap<Symbol, Scheme>` to `infer::Typed`: the
      generalized scheme of every `Let`, resolved at the end of inference.
      Today `generalize`'s result is discarded after use.
- [ ] Confirm `node_types` for `Var` use sites hold the instantiated type, and
      nodes inside a generalized body still mention the scheme's quantified
      vars, so mono can substitute them.
- [ ] Test: `id = program(x) do x done a = id(1) b = id(true) b` exposes a
      scheme with one quantified var; the two use sites have types
      `(Number) -> Number` and `(Bool) -> Bool`.

## Phase 1.5 — Design MIR before building on it

MIR is the seam that makes backends, runtimes, and host formats swappable.
What it can't make cheap is what's baked into it: the memory model, mono
(concrete types/layouts), closure representation, and structured control
flow. Settle those first.

### 1. Spec (`docs/mir.md`)
- [ ] **Values and layout:** `F64`, `I32`, `Ptr`; `Unit` erased. Layout rules
      for records, variants, strings, closures, lists. **Pointer size is a
      target parameter** (wasm32 = 4 bytes; a future native backend = 8):
      offsets are computed per target, never hard-coded.
- [ ] **Object header:** `rc` plus whatever else. Decide now whether it also
      carries a drop/type id (painful to change later).
- [ ] **Ownership convention:** owned params (Perceus; simplest) vs inferred
      borrowed params (Lean; fewer RC ops). It fixes the calling convention. Start owned; reserve room for borrowed.
- [ ] **Closures abstract:** `MakeClosure` / `CallClosure` nodes whose
      lowering can be heap closures or Roc-style lambda sets.
- [ ] **Structured control flow:** `If` / `Switch` / `Loop` trees, plus an
      explicit `TailCall` node (wasm `return_call`).
- [ ] **Effects and failure:** effectful calls are never dropped, duplicated,
      or reordered (even when they return `Unit`). `Trap(message)` for
      runtime errors like `first([])`.
- [ ] **Immortal objects:** the `rc` sentinel for literals and static
      closures.
- [ ] **Number types:** `Int` (i32 or i64? per target) and `Float` with a
      per-target width (`f64` / `f32`). Decide how the checker types literals
      and whether kids see one `Number`.
- [ ] **Memory budget:** a target can declare a fixed heap size at compile
      time (microcontrollers can't afford 64 KB `memory.grow` steps). The
      allocator interface must allow fixed-size pools per object size as well
      as free lists.
- [ ] **Stack depth:** tail calls, iterative drop functions, and a clear
      "stack overflow" trap are requirements (MCU stacks are a few KB).

### 2. Verifier (`mir/src/verify.rs`)
- [ ] Types line up; every owned pointer is consumed exactly once on every
      path; no use after `Drop`; control flow well-formed. Runs after every
      pass in debug builds and tests.

### 3. Reference interpreter (`mir/src/interp.rs`)
- [ ] Small (a few hundred lines). Proves MIR's semantics are self-contained;
      tracks allocations so leaks and double frees fail tests immediately.
- [ ] Becomes the test oracle: e2e output must match between the
      interpreter and the wasm backend.

### 4. Hand-written MIR for the hard cases (before mono exists)
- [ ] A closure capturing an outer value.
- [ ] A self-recursive local closure (self-reference via `env`).
- [ ] A recursive variant: `length` over `Empty | Link`.
- [ ] `map` over a uniquely owned list (in-place reuse when rc == 1).
- [ ] A record of functions called as `r.f(x)`.
- [ ] Each passes the verifier and runs in the interpreter, with a written
      sketch of its wasm lowering. Anything awkward → change
      MIR now.

Only after this does mono emit MIR and the backends consume it.

## Phase 2 — MIR, mono, wasm backend at parity with today

Goal: everything the Cranelift backend does today runs as wasm under
wasmtime, from MIR. Captured variables still rejected with a clear error.

### 2a. Mono (`mir/src/mono.rs`)
- Worklist keyed by `(Symbol, concrete Ty)`, starting from the root.
- At a `Var` use of a let-bound symbol with scheme `∀ā. τ`: match `τ` against
  the use-site type to get `ā ↦ concrete`, copy the binding's body
  substituting into every node type. Memoize per key; rewrite the use site to
  the copy's fresh symbol.
- Terminates: HM has no polymorphic recursion.
- Leftover unconstrained vars default to `Unit`; leftover row vars default to
  `Row::Empty` (closed).
- Output: every node has a ground type. Assert this.

### 2b. MIR (`mir/src/mir.rs`)
First-order, explicitly typed:

```rust
enum MTy { F64, I32 /* bool */, Unit, Ptr(HeapKind) }
// HeapKind: Record(layout) | Variant(layout) | Str | Closure(sig)

struct Program { funcs: Vec<Func>, entry: FuncId, layouts: Vec<Layout>, .. }
struct Func { params: Vec<(Local, MTy)>, env: Option<Local>, ret: MTy, body: Block }

enum Expr {
  Const, Local(l), Let(l, e),
  BinF64(op, a, b), Cmp(op, a, b),
  If(c, then, else),
  CallDirect(FuncId, args),        // known callee, no env
  CallClosure(closure, args),      // unknown callee: call_indirect
  MakeClosure(FuncId, captures),
  AllocRecord(layout, fields), Field(rec, offset),
  AllocVariant(tag, payload), Switch(scrutinee, arms),   // Phase 7
  StrLit(data id),
  Dup(l), Drop(l),                 // Phase 6
}
```

Unit-typed values are erased.

### 2c. Wasm emit (`wasm/src/lib.rs`)
- One exported `memory`; exported `goat_entry`; host imports under module
  `"goat"` (`print_number(f64)`, `print_bool(i32)` to start); one funcref
  `table` for closures; a `data` segment for static data; a mutable global
  heap pointer.
- `goat_entry` computes the root value and calls the matching `print_*`.
- Tail calls: `return_call` / `return_call_indirect` in tail position.

- Every emitted module is validated with `wasmparser` in tests and debug
  builds; golden tests compare `wasmprinter` text for small programs.

### 2d. CLI + tests
- [ ] `goat build FILE -o out.wasm`; `goat run FILE` runs it in `wasmtime`
      with Rust host functions. Traps print an error and exit non-zero.
- [ ] Port `compiler/tests/run.rs` to compile → wasmtime → captured stdout.
- [ ] **Differential testing:** every e2e program and fuzz case runs through
      the MIR interpreter and the wasm backend; outputs must match.
- [ ] Add a deep tail-recursion test (`f(1000000)`).
- [ ] `examples/fib.goat`, `examples/higher_order.goat` run.
- [ ] Remove the `compiler` crate and the C runtime strings (lambda lifting
      and the captured-variable check now live in `goat_mir`).
- [ ] CI: `cargo build -p goat_parser -p goat_checker -p goat_mir -p goat_wasm --target wasm32-unknown-unknown`.

## Phase 3 — Records

- After mono every record type is a closed row. Sort labels; layout
  `[header][field0][field1]...`, fields at natural width, 8-byte aligned.
- Header: `rc: u32`, `_pad: u32`.
- `Field` → load at a constant offset.
- Bump allocator (`heap_ptr` global, `memory.grow`). No frees yet.
- [ ] `examples/records.goat` runs. Row-polymorphic `getx` compiles to two
      specializations with different offsets.

## Phase 4 — Closures

(Before building this, read Roc's lambda-set design: under mono, a closure
whose possible targets are known can be compiled as tagged data with no heap
allocation or indirect call. The scheme below is the general fallback.)

- Closure conversion after mono: free variables of each `program(...)`;
  known top-level functions are called directly, not captured.
- Closure object: `[header][drop_fn: i32][code: i32][captures...]`. All
  closures of one goat function type share `(env: i32, args...) -> ret`.
- Calling a function value: load `code`, `call_indirect` with the closure as
  `env`. This is also how `s.f(x)` on a record field works.
- Top-level functions used as values get a static, immortal closure.
- **Self-reference rule (prevents RC cycles):** inside a closure's body,
  references to its own binding compile to the current `env`; a closure never
  stores itself. `Let` binds one name, so only self-recursion exists.
- [ ] Tests: `add = program(a) do program(b) do a + b done done add(1)(2)`;
      local recursive closure capturing an outer param; closure through a
      polymorphic `apply`; a record of functions called as `r.f(x)`.

## Phase 5 — Strings and printing

- String object: `[header][len: u32][bytes...]`; literals in the data segment,
  immortal.
- Host import `print_string(ptr: i32)`.

## Phase 6 — Reference counting and freeing

- Owned locals; params owned (callee consumes); `Dup` before a use if the
  local is used again later; last use transfers ownership; `Drop` unused
  owned locals at scope end and at the start of each branch.
- `Field(rec, off)`: `Dup` the field if pointer, then `Drop` the record.
- Immortal objects: `rc == u32::MAX` skips inc/dec.
- `Drop` at rc 0 calls a per-layout generated drop function (closures use
  their `drop_fn`), then frees.
- Allocator: size-class free lists on top of the bump allocator. A second
  strategy, fixed-size pools inside a declared heap budget, for embedded
  targets (less fragmentation on small RAM).
- **Leak checking:** debug runtime keeps a live-allocation count, exported as
  `goat_live_allocs()`. Every e2e test asserts 0 after `goat_entry`.
- [ ] AFL fuzzer (`fuzz/`): compile-and-run random programs, assert no leak,
      no double free (debug allocator poisons freed blocks).
- Later: Perceus reuse (in-place update when rc == 1). Matters for lists.

## Phase 7 — Variants, `match`, recursive types

### Syntax
- Capitalized identifier ⇒ tag. `Circle(5)`, `Empty`, `Link(x, rest)`.
  Lowercase identifiers stay ordinary names. (Uppercase = Unicode `Lu` start.)
- Multi-argument tags are positional; internally the payload is a record with
  positional labels (`0`, `1`, ...) so the row machinery is reused.
- `match e do Tag(a, b) then expr  Other then expr  else expr done` —
  consistent with `if`. `else` is the catch-all arm.

### Types
- Variant types are rows (Leijen's scoped labels — `papers/scopedlabels.pdf`
  covers variants as the dual of records): `Ty::Variant(Row)`.
- Constructing a tag gives an open row `[Circle: Number | ρ]`. A `match`
  without `else` closes the row; with `else` it stays open.
- **Guarded recursive types.** In `unify` (`checker/src/infer.rs`, around
  the `occurs` check at the top of `unify` and in `unify_row`): when the
  occurs check fails, allow the binding *if every occurrence of the variable
  is under a variant tag*, recording `Ty::Rec(var, body)` (μ-type).
  Otherwise keep the current error.
  - Unification of recursive types keeps an assumed-equal set of pairs so it
    terminates.
  - `resolve`, `free_vars`, `subst_vars`, `Display` need cycle handling.
  - Type printing: match inferred types against prelude shapes and print
    `List(Number)` instead of the μ-form. Kids never see μ.
- [ ] Tests: `length` over `Empty | Link` infers
      `μl. [Empty, Link: {0: a, 1: l}]`; `f = program(x) do x(x) done` still
      errors with the occurs-check message.

### Record spread and destructuring (JavaScript-style)
- [x] **Spread update:** `{...model, x: model.x + 1}`. Typed as scoped-label
      extension: result `{x: Number | row(model)}`; an existing `x` is
      shadowed. Can add fields or override them (even changing type); no new
      type rules beyond Leijen's.
  - Mono drops shadowed fields from the layout (they're unreachable), so the
    new record has a single `x`.
  - **One spread, first position only (for now).** `{...a, ...b}` needs
    "b's fields overriding a's", which plain scoped labels can't type when
    `b`'s row isn't fully known (`merge = program(a, b) do {...a, ...b} done`
    has no HM type). Reject it with a clear error.
  - **Later: multi-spread solved at generalization** (after the Phase 8
    constraint machinery exists). Multi-spread emits a row-union constraint
    (right-biased: later spreads override). At each `Let` generalization,
    the checker solves it if the rows involved are known by then; if not,
    error: "can't merge two records of unknown shape here". **Never
    generalize the constraint** (like Haskell's monomorphism restriction).
    - Order-independent: checked after the whole definition is inferred.
    - Errors stay in the checker, at the definition. No constraints appear
      in displayed types.
    - Covers the realistic uses (config records, defaults + overrides, known
      shapes). Loses only a fully generic `merge` over arbitrary records.
    - Rejected alternative: PureScript-style `Union` constraints solved
      during mono. Works without annotations, but moves errors to mono
      (template-style traces), spreads constraints into types, leaves
      unsolved constraints for uncalled code, and delays field-typo errors.
  - With Perceus reuse (Phase 6), `{...model, x: …}` on a uniquely owned
    model updates in place.
- [x] **Destructuring:** `{x, y} = point` and in parameters
      `program({x, y}) do … done`. Open-row patterns (any record with at least
      those fields), desugared to field reads.
- [x] **Rest pattern:** `{x, ...rest} = point` needs row restriction (remove
      a label; supported by scoped labels). Can follow the basic forms.
- [x] **List patterns use the same syntax:** `[first, ...rest]` →
      `Link(first, rest)`, `[]` → `Empty`, `[a, b]` → a fixed-length list.
      Lowering compiles a `match`'s list arms into nested `Empty`/`Link`
      matches; `[..] = xs` and `program([a, b])` use the same compiler.

### Warnings (whole-program)
- [ ] "Tag `Cirle` is constructed but never matched anywhere" — catches tag
      typos, the main pitfall of structural variants.

### Backend
- Every tag label gets one global tag number. Variant value:
  `[header][tag: u32][payload fields...]`; nullary tags can be immortal
  static objects.
- `match` → load tag, `br_table`.
- Mono keys must compare recursive types up to equivalence: canonicalize
  μ-types (minimize, hash-cons) before using them as keys.
- Per-layout drop functions release payloads iteratively (a pending list
  threaded through the dead objects, drained by one loop), so long lists don't
  overflow the stack. Implemented in P7d; see `docs/mir.md`.

## Phase 8 — Prelude, lists, and kid-facing features

### Prelude mechanics
- `prelude/prelude.goat` and `prelude/turtle.goat`, embedded with
  `include_str!` (good until a module loader exists).
- The user program is wrapped as the `rest` of a chain of prelude `Let`s; the
  existing `Let { rest }` shape fits.
- Mono only generates reachable code, so unused prelude functions cost
  nothing.
- Add a file id to `Span` so diagnostics distinguish prelude from user code.
  Errors raised inside prelude functions (e.g. `first([])`) report at the
  user's call site: "first of an empty list".
- Users may shadow prelude names (normal scoping), with a warning.
- Implemented (P8a): `goat_checker::PRELUDE` is lowered on its own with
  `FileId::Prelude` spans, then the user program is grafted in as the `rest` of
  its last `Let`. A `=` declaration that reuses a prelude name warns;
  parameters and pattern binders do not. `GoatError::at_call_site` re-blames a
  prelude-origin error on the user's call site. Prelude `Let`s count against
  the lowering depth limit, so keep definitions to functions.

### Lists (defined in goat)
```
# prelude.goat (sketch)
link = program(x, xs) do Link(x, xs) done
length = program(xs) do
  match xs do
    Empty then 0
    Link(first, rest) then 1 + length(rest)
  done
done
```
- Literal sugar in the grammar: `[]` → `Empty`, `[1, 2, 3]` →
  `Link(1, Link(2, Link(3, Empty)))`.

### Prelude names
| CS name | goat |
|---|---|
| `cons(x, xs)` | `link(x, xs)` |
| append to end | `add(xs, x)` |
| `concat` | `join(a, b)` (also strings; `appendable` constraint) |
| `length` | `length(xs)` |
| `nth` (1-based) | `item(xs, 1)` |
| `head` / `tail` | `first(xs)` / `rest(xs)` |
| `map` | name TBD (`change_each`?) |
| `iter` (for effects) | `each(xs, f)` |
| `filter` | `keep(xs, test)` |
| `fold` | mostly unneeded: `sum`, `count`, `biggest`, `smallest` |
| `elem` | `has(xs, x)` (needs `eq`) |
| `reverse`, `sort` | same |

Turtle (`turtle.goat`, Logo names): `forward`, `back`, `left`, `right`,
`pen_up`, `pen_down`, `color`.

### Built-in constraints (checker)
- [ ] Constrained type-variable kinds checked during unification, Elm-style:
      `eq` (any type without functions inside), `appendable` (String, List),
      `numeric` (Number, or a record whose fields are all `numeric`).
- [ ] `==`, `!=` use `eq`; mono emits a per-type equality function
      (structural on records, variants, lists).
- [ ] `+ - * /` use `numeric`; on records, mono emits field-wise code.
- [ ] Error messages name the constraint plainly ("can't compare functions
      with `==`").

### Other language features
- [ ] `and`, `or`, `not`.
- [ ] **`print` as a builtin** usable mid-program, `(a) -> Unit`, per-type
      printer generated by mono.
- [ ] **Sequencing:** allow `expr  rest` at statement position (treated as
      `_ = expr  rest`), or `a; b`. Pick one, update the grammar.
- [ ] **Loops:** `repeat n times do ... done`, `for i from 1 to 10 do ... done`,
      `for x in xs do ... done`. Lower to wasm `loop`s.

## Phase 8.5 — FFI (host imports)

FFI = wasm imports. The "foreign" side is the host: JS in the browser and the iOS web
view, Rust in the wasmtime CLI. Turtle graphics is the first user.

**Direction: WIT and the Component Model.** A host describes its API in WIT,
whose types (records, variants, lists, options, results) map almost 1:1 onto
goat's. The compiler reads the host's WIT and turns it into goat types, so
**the WIT file is the annotation** and no type syntax appears in goat code.
The canonical ABI handles strings, lists, and records across the boundary.
Browsers don't run components natively (they need `jco`), so the browser host
keeps core modules; other hosts get components. The v1 design below is the
stepping stone: keep it compatible with WIT's types.

- **Who writes it:** prelude/library authors only (same tier as named types).
  Kids call `forward(100)`; they never declare foreign functions. The app
  ships a fixed set of host functions, so user code can't reach arbitrary
  native APIs — good for sandboxing and App Store review.
- **Syntax:** the one place types are written, since a foreign function's
  type can't be inferred. Sketch:
  `forward = foreign "turtle" "forward" (Number) -> Unit`
  Lowered to a `Let` whose value is a known function with a fixed scheme.
- **Boundary types (v1):** `Number` → `f64`, `Bool` → `i32`, `Unit` → nothing,
  `String` → `i32` pointer (host reads `[len][bytes]` from exported memory).
  No records, lists, or closures across the boundary yet.
- **Opaque host objects** (images, sounds): an `i32` handle into a host-side
  table, typed as an opaque foreign type (`image = foreign type`). Needs a
  nominal type — first real use of the named-types machinery.
- **Ownership across the boundary:** pointers passed to the host are borrowed
  for the call. Strings returned by the host are allocated through exported
  `goat_alloc(size) -> ptr` and arrive with rc = 1 (goat owns them).
- **Effects:** MIR erases `Unit` *values*, never calls. A foreign call must
  never be dropped, duplicated, or reordered. Mark foreign calls as effectful
  in MIR.
- **Callbacks:** none in v1. The host calls fixed exports only (`goat_entry`;
  later the Elm-style `init`/`update`/`draw`).
- **Every host implements the same imports.** The CLI's turtle is headless: it
  records commands and writes an SVG, which gives golden-file tests for
  drawings (`goat run spiral.goat -o spiral.svg`).
- **Native C libraries:** not reachable from wasm directly. On desktop they'd
  be wrapped as Rust host functions in the CLI; they don't exist in the
  browser or on iOS, so keep the import set identical across hosts.
- [ ] Tests: foreign `Number`/`Bool`/`String` round-trips under wasmtime;
      a turtle program produces the expected SVG.

## Phase 9 — Browser runtime and turtle graphics

- [ ] `web/runtime.js`: instantiate the module, provide `goat.*` imports,
      read strings from memory.
- [ ] Turtle imports behind `turtle.goat`: commands go into a queue; the
      canvas animates the queue so kids see the turtle move. The goat program
      never blocks.
- [ ] Compiler crates built to wasm (plain C-ABI export: source bytes in,
      module bytes or rendered diagnostics out).
- [ ] `web/index.html`: editor + Run + canvas + error panel.

## Phase 9.5 — Event loop (host-owned)

Goat programs never write a loop or block. The host owns the loop and calls
pure goat exports. Same model on every host (browser, desktop, CLI,
microcontroller).

### Goat side (Elm architecture)
```
init = {x: 0, y: 0}

update = program(model, event) do
  match event do
    Tick(dt) then {...model, x: model.x + dt}
    KeyDown(Left) then {...model, x: model.x - 10}
    else model
  done
done

draw = program(model) do
  [Circle({x: model.x, y: model.y, r: 10})]
done
```
- `init`: starting model. `update(model, event) -> model`. `draw(model) ->`
  picture as data (a list of shape variants), not drawing calls.
- **Levels:** a program without these exports runs once, top to bottom
  (`forward(100)`, kid level). Defining `init`/`update`/`draw` opts into the
  loop; the host checks which exports exist.

### Host side (contract)
```
model = goat.init()
loop:
  wait for events            # interrupt queue / DOM events / frame timer
  for e in queue: model = goat.update(model, e)
  if frame due: render(goat.draw(model))
```
- Browser: `requestAnimationFrame` + DOM events. Microcontroller: superloop
  sleeping (WFI) until the interrupt queue is non-empty. CLI: wasmtime with a
  timer (or no loop).
- **Events are goat variants** (`Tick(dt)`, `KeyDown(k)`, `ButtonPressed(t)`,
  `Reading(...)`), defined by the host's WIT.
- **Outputs:** v1 — everything the host emits is part of `draw`'s result
  (LEDs are part of the picture). Later, if needed: `update` returns
  `{model, commands: [PlaySound(...)]}` (Elm-style commands).
- **Subscriptions inferred from types:** `update`'s `match` closes the event
  variant row to exactly the events handled. The host reads that from the
  compiled interface and enables only those listeners/interrupts — no
  declaration needed; saves power on microcontrollers.
- **Bounded update time:** fuel/epoch limits plus a watchdog catch a slow or
  looping `update`.
- **Memory:** the old model is dropped after `update`; Perceus reuse makes
  spread updates in place.

### Interrupts (microcontrollers; see Phase 12)
- Goat never runs in interrupt context: RC/allocator aren't interrupt-safe,
  wasm instances aren't reentrant, and goat has no shared mutable state.
- A tiny host ISR (C) pushes `{kind, timestamp, value}` into a lock-free ring
  buffer and returns; the loop drains it into `update`.
- Latency is bounded by `update`'s duration.
- **Overflow policy:** drop oldest and deliver `Missed(n)` so programs know
  they fell behind.
- Debounce/coalesce in the host or prelude; optional priority queues.
- **Hard real-time** (µs timing) is done by hardware configured from goat:
  PWM, DMA, RP2040 PIO, ESP32 RMT (NeoPixels). Not in software.
- Later, only if a host needs it: a checker-enforced restricted function kind
  (no allocation, no RC, no closures, numbers only, bounded loops) compiled
  AOT to run in interrupt context.

## Phase 10 — iOS and desktop shells

- [ ] iOS: Swift app hosting `WKWebView` with the `web/` bundle. App Store
      guideline 2.5.2 allows educational apps to run user code if the source
      is fully viewable and editable — editor always reachable, no "export an
      app" features.
- [ ] Desktop: Tauri (or similar) wrapping `web/`.
- [ ] Both shells implement the Phase 9.5 host-loop contract.

## Phase 11 — Embedding and live coding

- [ ] **Embedding API** (`goat` lib crate): compile source against a host
      interface (WIT), instantiate, call exports. Document it as the primary
      product; the CLI and the turtle app are clients.
- [ ] **Second demo host** (e.g. a small game-scripting or p5-style canvas
      host in Rust) to keep the embedding API honest.
- [ ] **Hot reload with state preserved:** recompile, instantiate the new
      module, keep the `model`, swap `update`/`draw`.
  - The host owns linear memory and passes it in (imported memory), so old
    and new instances share it; the allocator's state lives there too.
  - If the model's type is unchanged, mono lays it out identically and the
    model pointer stays valid; if it changed, reset to `init`.
  - Closures stored in the model reference the old module's table: either
    forbid functions in the model type or deep-copy across reloads.
- [ ] **Compile latency budget:** whole-program mono means every reload
      recompiles the whole script; measure and keep it interactive.
- [ ] **Real-time caveat (audio hosts):** RC is deterministic but dropping a
      large structure frees it all at once. For audio callbacks add deferred
      freeing (drop queue drained off the hot path) or a per-callback arena.

## Phase 12 — Microcontrollers

Typed, GC-free scripting for LEDs, sensors, and installations: the
creative-coding crowd overlaps with Arduino users. Competition: MicroPython /
CircuitPython (dominant), Toit (closest "serious" option), Lua variants,
Espruino. None are statically typed and GC-free.

- [ ] **Compile off-device:** in the browser (compiler-as-wasm) or the CLI;
      flash over WebSerial / WebUSB.
- [ ] **On-device runtime:** start with an interpreter (WAMR fast-interp or
      `wasm3`, tens of KB flash); add AOT (WAMR AOT, or `wasm2c` → vendor
      toolchain) for speed.
- [ ] **First boards:** an ESP32 variant and an RP2040/RP2350.
- [ ] **Host API (WIT):** GPIO, timers, LEDs (NeoPixel strips), basic
      sensors, serial print.
- [ ] **Event model:** the Phase 9.5 loop and interrupt queue — button/timer/
      sensor events in, model updated, outputs driven. No callbacks.
- [ ] **Constraints honored:** `f32` floats, declared heap budget with pooled
      allocation, bounded stack with clear overflow traps.
- [ ] **Live coding over serial:** upload new code, keep the model (same
      rules as Phase 11 hot reload).
- [ ] Check runtime support for wasm custom page sizes before relying on it.

---

## Later (not scheduled)

- **Direct Cranelift backend (MIR → Cranelift IR)**, added only when a
  measured need shows up. Triggers: wasm's limits on stacks/threads block
  coroutines or parallelism; a host needs native embedding with no wasm
  runtime or direct C interop; profiling shows the wasm layer (bounds
  checks, host-call adapters, lost goat facts) costing real time. Start from
  the old Cranelift code in git history; it would also become a second
  differential-testing oracle. Desktop-only: Cranelift doesn't target
  microcontrollers.

- **Module loader** replacing `include_str!` for the prelude and user files.
- **Named types (advanced tier).** For teachers and library authors; kids
  consume them, never write them. Enables polymorphic fields
  (`forall` in a field type, OCaml-style — fixes the known limitation without
  annotations in function code), nominal protection against tag typos, and
  later user-defined operators keyed on names. Possible kid-readable syntax:
  `shape = kinds do circle(r)  square(side) done`.
- **Rank-2 intersection inference (experiment, behind a flag).** Fixes the
  known limitation with no annotations: a parameter whose uses conflict gets
  an intersection type; mono compiles an intersection-typed parameter as one
  specialized argument per conjunct. Restrict to function-typed params.
  Open problems: grouping uses is order-dependent with conflict-driven
  splitting; error messages; recursion. Rank-2 intersections + scoped-label
  rows appears unexplored. References: Jim, POPL 1996; Kfoury & Wells, POPL
  1999; Damiani (rank-2 intersections for local definitions); related
  call-site splitting: Agesen's CPA (ECOOP 1995), Wright & Jagannathan
  (TOPLAS 1998), Crystal.
- **Perceus reuse / FBIP** for in-place list updates.
- **Built-in `Array`** (contiguous, unboxed via mono, in-place when unique) for
  indexing-heavy code, alongside the prelude `List`.
- **Prior art for embedding:** Luau (typed Lua, Roblox), Gluon (typed
  functional embeddable in Rust; find out why it stalled), Mun (static types +
  hot reload), Extism and Zed extensions (wasm plugin hosts).
- **Live-coding prior art:** Sonic Pi, TidalCycles.

## Notes for whoever implements this

- Each phase is a PR with tests; don't start Phase N+1 with Phase N red.
- `goat check` must stay fast. Mono/MIR failures are internal compiler bugs;
  every user-facing error comes from the checker.
- Every feature gets a checker test and an e2e run test; examples go in
  `examples/`.
