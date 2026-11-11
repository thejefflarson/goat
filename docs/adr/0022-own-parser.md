# ADR 0022 — goat's own grammar-driven, error-recovering parser (replacing pest)

- Status: accepted (2026-11-08)
- Context: the parser-future spike (PR #268, `docs/spikes/parser-future.md`), which
  measured rowan, chumsky and tree-sitter against pest and recommended a
  hand-written recursive-descent parser over rowan. This ADR **supersedes that
  recommendation** on one point — it keeps a *formal grammar* that drives the
  parser rather than hand-coding the parser — and otherwise builds on the spike's
  measurements. Refs the current PEG (`parser/src/grammar.pest`), the pest→HIR
  lowering (`checker/src/lower.rs`), the pest-based editor lexer
  (`parser/src/lexer.rs`), ADR 0013 (flat operator runs, `a; b` sequencing),
  ADR 0016 (tags declared, not capitalized — tag-vs-name resolved in lowering),
  ADR 0008 (Coq/Ott type-system proof), ADR 0018 (one Rust conformance suite),
  and the CLAUDE.md invariants: user-facing errors come only from the checker,
  and the compiler crates build for `wasm32-unknown-unknown` with no C.
- Not urgent. Highlighting and live type-checking already ship on pest, and a
  pragmatic autocomplete can ship on pest now (§6, P0). This build becomes
  worth-it only when *semantic, robust-in-broken-code* completion is the goal.

## Context

### What pest cannot do, and why it now matters

pest compiles the grammar to a parsing-expression grammar (**PEG** — a grammar of
ordered, backtracking alternatives) and reports the single farthest failure. On a
half-typed buffer it returns `Err` with **no tree**. The spike measured the cost:
of the 173 prefixes of a sample program — which is exactly what an editor holds
while someone types — pest yields a tree for 61 (35%). For the other 65%,
everything that needs a tree goes dark mid-edit.

The thing that needs a tree mid-edit is **completion**, and completion is the
near-term reason to do this work. goat is for kids learning to code; they
discover the commands and their own names by typing a prefix and seeing what is
offered. The cursor is therefore *always* sitting in incomplete code — `turtle.`
with nothing after it, `col` mid-identifier, an unterminated `match … do`. A
parser that produces nothing on such input cannot answer "what can go here," which
is the one question completion asks.

### The three hard requirements

The owner has chosen to build goat's own parser over keeping pest, adopting
tree-sitter, or hand-writing a recursive-descent parser over rowan, because only a
grammar-driven recovering parser satisfies all three of these at once:

1. **A formal grammar** — a legible, declarative specification of the syntax, kept
   as a first-class artifact (the owner values this, and it sits beside goat's
   Ott/Coq semantics, ADR 0008). The grammar must *drive* the parser, not be a
   document that drifts from a hand-written one.
2. **Error recovery** — produce a usable tree plus multiple spanned diagnostics on
   broken or incomplete input, so editor tooling (completion first) works while
   the file is mid-edit.
3. **Pure Rust that builds for `wasm32-unknown-unknown`** — the in-browser
   playground runs the whole compiler as wasm, with no C toolchain (this is the
   decisive strike against tree-sitter, whose Rust crate *does* now build for
   wasm32 but drags `cc` and a wasm-capable clang into the compiler crates).

The spike's recommendation (hand-RD over rowan) meets requirements 2 and 3 but
demotes the grammar to documentation — the hand-written parser becomes the real
spec. That is what the owner rejected. This ADR keeps the grammar authoritative.

### Terms used below

- **CST** (concrete syntax tree): a tree that keeps *every* token and *trivia*
  (whitespace and comments), so the source reconstructs from it byte for byte.
  Contrast an AST, which keeps only semantically relevant nodes.
- **Lossless / infallible parse**: the parser never returns "no tree"; it returns
  a CST plus a separate list of diagnostics. Unparseable input is wrapped in
  `ERROR` nodes; a required-but-absent token is marked by a zero-width `MISSING`
  node (rust-analyzer's design).
- **Ordered choice**: a PEG's `A | B` tries `A`, and only if `A` fails tries `B`.
  goat's grammar already depends on this (`done` is listed before `do`,
  `destructure` before `record`); it is load-bearing, not incidental.
- **Panic-mode recovery**: on an error, skip input until a **sync token** (a
  stable landmark such as `done`, `;`, or a block boundary), then resume.
- **Pratt parsing** (precedence climbing): building an expression tree from a flat
  run of operands and operators by operator binding strength.

## Decision

Build a **grammar interpreter**: a single, small, resilient PEG engine that walks
the grammar *as data* against a token stream, producing a lossless CST and a list
of diagnostics, and never failing. The grammar is one legible EBNF file; the
engine is a few hundred lines of pure Rust. Precedence stays in lowering's
existing Pratt code. Build it alongside pest, reach parity on the corpus, then
switch lowering onto the CST and retire pest. The whole thing is deferred until
semantic completion is the active goal.

### 1. Grammar formalism — a PEG-in-EBNF file, evolved from today's `.pest`

The grammar stays a **PEG** and stays close to the current `grammar.pest`. Two
reasons, both about cost and risk:

- The existing grammar's disambiguations *are* PEG ordered-choice facts
  (`done` before `do`; `destructure` before `record`/`list`; `local` — a
  `name = …` binding — before a bare `name`). Moving to an LL or LR context-free
  grammar would force re-deriving all of them, for no benefit. Keep ordered
  choice.
- The grammar already exists, is ~227 lines, is already legible, and is already
  the single source of truth for the editor lexer. Rewriting it from scratch is
  waste.

The artifact is a `grammar/goat.peg` file: the current rules in a cleaned EBNF
(sequence, ordered choice `/`, repetition `*`/`+`, option `?`, negative lookahead
`!` for the keyword-boundary rules, a string/char-class terminal set), **plus a
small, closed set of recovery annotations** that stock pest cannot carry:

| Annotation | Means | Example |
|---|---|---|
| `@sync(tok…)` on a rule | tokens that end panic-mode recovery *into* this rule's follow | `expr` syncs to `;`, `done`, EOF |
| `@expect(tok)` on a required terminal | if absent, insert a `MISSING` node + diagnostic, keep going | the `done` closing `match` |
| `@anchor(tok)` (don't-cross) | recovery of an inner error must not consume this token | the outer `done`, a top-level `;` |

This small vocabulary is the engineering distillation of the *labeled-failures /
recovery-expressions* line of PEG research (Maidl–Mascarenhas–Medeiros): a label
marks a real error and carries enough to resynchronize. We deliberately do **not**
adopt the full labeled-PEG calculus (a recovery expression per label) — three
annotation kinds cover goat's grammar and stay legible, which is the priority. We
also do not adopt lelwel-style *automatically computed* recovery sets (follow sets
of grammar dominators): elegant, but "too clever to reason about" for a first
version, and explicit `@sync`/`@anchor` are what a reader can check by eye. Both
remain available as later enhancements if the explicit sets prove tedious.

During migration the recovery annotations live in the new `goat.peg`; pest keeps
its own unchanged `grammar.pest` until it is retired (§6). The corpus keeps the
two honest.

### 2. Parser engine — a grammar interpreter, not a code generator or hand-RD

Three ways to turn the grammar into a parser:

| | (a) Code generator (pest, LALRPOP, lelwel) | (b) **Grammar interpreter** | (c) Hand-written RD checked against the grammar |
|---|---|---|---|
| Grammar drives parser (req 1) | yes (regenerate) | **yes (interpret)** | no — the parser is the spec; grammar is a doc |
| Simplest to build | no — a code emitter + its generated-code surface to debug | **yes — one engine + the grammar data** | medium |
| Simplest to evolve | regen step each change | **edit the grammar data** | hand-edit per construct |
| Recovery threading | in the generator | **in one interpreter loop + annotations** | hand-tuned per construct (best quality) |
| Pure-Rust / wasm32 | build-time codegen (pest's derive; a `build.rs`) | **trivial — data + a loop, no build step** | trivial |
| Speed | fast | slower (irrelevant — goat files are tiny) | fast |

We recommend **(b), the grammar interpreter.** The grammar is read once, at parser
init, from the embedded `goat.peg` text into an in-memory tree of PEG combinators
(`Seq`, `Choice`, `Repeat`, `Opt`, `Token`, `RuleRef`, `NotAhead`, plus the three
annotations). One engine then walks that tree against the token stream, builds the
CST, and recovers. It is the simplest thing that satisfies all three requirements
*and* keeps the grammar authoritative:

- **Simplest to build and evolve.** One interpreter (a few hundred lines) versus a
  code generator plus the generated code you then debug. Changing the language is
  an edit to `goat.peg`, with no regeneration.
- **Recovery lives in one place.** The recovery algorithm (§3) is a property of
  the interpreter loop plus the per-rule annotations, not scattered across
  generated branches or hand-written functions.
- **Trivially pure-Rust/wasm32.** No proc-macro, no `build.rs`, no C. The grammar
  is `include_str!`'d as a `&'static str`; a tiny bootstrap reader (it parses only
  *well-formed* grammar, so it needs no recovery of its own) builds the combinator
  tree at startup. The only runtime dependency is `unicode-ident` (already used)
  for `XID_START`/`XID_CONTINUE`.
- **Speed is a non-issue.** goat source files are small (a kid's program), and the
  interpreter is linear in tokens. The spike's slowest measured case was recovery
  cost, not throughput; §3's termination invariant bounds that.

The honest cost of (b) over (c): a *generic* interpreter recovers only as well as
its annotations, whereas hand-RD can special-case a construct's recovery. The
spike saw this bite tree-sitter (generated recovery) in 3 of 5 cases. Mitigation:
the annotation set in §1 is chosen to express goat's recovery needs, the prefix
corpus (§3) measures recovery quality against the rowan bar, and if one construct
still recovers poorly we add an annotation — or, as a last resort, a single
hand-written override hook for that one rule while the interpreter handles the
rest. We do not pre-build that hook.

**Expression precedence (Pratt).** ADR 0013 makes operator runs *flat*: the
grammar produces `operand (infix operand)*`, and lowering's existing `prec` code
resolves precedence by climbing. The interpreter keeps that exact shape — an
operator run is an ordinary repetition, emitted as one flat `OpRun` node — and
**precedence resolution stays in `lower.rs`, unchanged.** No Pratt engine is added
to the parser. (A Pratt sub-mode could move into the engine later if lowering ever
wants a pre-shaped tree; it is not needed now.)

### 3. Error recovery — infallible parse, insert-to-continue, panic-mode-to-sync

The engine never returns "no tree." It returns `(cst, diagnostics)`. Recovery is
four mechanisms, layered:

1. **Infallible / lossless.** Every token of the source lands in the CST,
   including trivia. Input the grammar cannot place goes into an `ERROR` node, not
   on the floor. (Parser diagnostics are a *separate* list, not tree nodes —
   rust-analyzer's split — so the tree stays a clean picture of the syntax.)
2. **Required-token insert (`@expect`).** When a rule requires a specific terminal
   and it is absent, the engine emits a diagnostic ("expected `done` to close
   `match`") at that point, inserts a **zero-width `MISSING` node**, and continues
   as if the token were there. The `MISSING` node is what tells completion "a
   `done` belongs here."
3. **Panic-mode to a sync token (`@sync`).** When the engine hits input it cannot
   match inside a rule, it opens an `ERROR` node and skips tokens into it until it
   reaches a token in that rule's sync set (its `@sync` tokens plus its follow
   set), then resumes. This is what keeps the `b = 2` after a broken `a = ;`: the `;` is the sync token.
4. **Don't-cross anchors (`@anchor`).** Recovery for an inner error must not
   consume an anchor token belonging to an enclosing construct (the outer `done`,
   a top-level `;`). This is the fix for the spike's worst observed failure, where
   tree-sitter swallowed a whole `match` *and* the following binding into one
   `ERROR` node: goat's anchors make `done` and top-level `;` hard walls.

**Termination invariant (stated explicitly, because the spike hit the bug).** The
spike's rowan prototype was first *exponential*: after hitting a depth cap it
re-entered the same nesting from every level. The engine therefore maintains the
invariant that **every recovery step either advances the token cursor by at least
one or closes an open node; it never re-enters a rule at a position it has already
tried.** With a global depth cap (`MAX_DEPTH = 256`, the bound lowering already
uses) this makes the parse terminate on any input. We fuzz for it directly:
`fuzz/` already exists, and the property is "never panics, always lossless, always
terminates."

**Acceptance bar.** The spike's rowan prototype produced a lossless tree for
**100% of the 173 prefixes** of a valid program (pest: 35%). That is the bar: a
lossless CST for every prefix of every corpus program, plus the expected
diagnostics on the broken-snippet suite.

#### Worked broken snippets (with the completion query each unlocks)

`•` marks the cursor.

**(a) `match x do •`** — unterminated, no arms, at EOF.

```
MatchExpr[ 'match'  OpRun[name 'x']  'do'
           arms: (none)
           MISSING('done')@expect ]
diag: "expected `done` to close `match`"  at the cursor
```
Completion at `•`: the enclosing path is `MatchExpr → arm-position`, so offer an
**arm pattern head** — the tags of `x`'s type (checker-backed) or any declared tag
(CST-only fallback).

**(b) `a = •;` then `b = 2; b`** — a binding with no value yet. goat is
whitespace-insensitive, so the `;` after the cursor is what ends the broken
binding; without it `b` would parse as `a`'s value.

```
Expr[ Decl[ name 'a'  '='  MISSING(value)@expect ]      # a kept
      Decl[ name 'b'  '='  OpRun[number '2'] ]  ';'  OpRun[name 'b'] ]  # b intact
diag: "expected value"  where the value should be
```
Completion at `•`: the enclosing path is `Decl → value-position`, so offer the
**in-scope names + builtins/prelude** — exactly the kids'-discoverability case,
and `b`'s later binding is untouched because the newline/`;` is a sync point.

**(c) `turtle.•`** — member access with nothing after the dot (the discoverability
case the owner cares about most).

```
Access[ OpRun[name 'turtle']  '.'  MISSING(name)@expect ]
diag: "expected a field name after `.`"
```
Completion at `•`: the enclosing path is `Access`, base `turtle`. The CST alone
says "a member of `turtle` goes here"; the **checker** supplies *which* members —
the fields/methods of `turtle`'s type. This is the query that makes `turtle.`
offer `forward`, `right`, `pen_up`, … while the line is unfinished.

A fourth, `col•` mid-identifier, needs no special recovery: the token is a `name`
in expression position, so the enclosing path says "a name goes here," and the UI
prefix-filters the in-scope set to those starting `col`. The parser's only job is
to put the cursor in a name position even though the program is incomplete.

### 4. CST representation — a flat arena, own it, don't adopt rowan

A **lossless** CST (requirement 2; the substrate completion queries run on). Own a
simple structure rather than adopt rowan — the owner finds rowan niche and
rust-analyzer-tied, and owning the tree is cheap because goat needs none of
rowan's incremental-reuse machinery (files are small).

- **Storage: a flat arena.** Two element kinds, addressed by index (not pointer),
  so it is trivially `Clone`, `Send`, and wasm32-clean:
  - `Token { kind, span }` — a lexeme or a piece of trivia, with its byte range.
  - `Node { kind, span, children: Range }` — children are a contiguous slice in a
    shared `Vec<ElementId>`. The node's span covers its children (trivia
    included), so the source reconstructs byte-for-byte.
  This is a "green tree" in spirit (lossless, offset-addressable) without rowan's
  interning, `countme`, and `text-size` deps. Lighter, fewer dependencies.
- **Queries (a thin cursor computed on demand).** A `Cursor { arena, id }` walks up
  and down by index. Two completion primitives are **first-class**, because
  completion is the whole point:
  - `enclosing_path(offset) -> Vec<NodeKind>` — the chain of constructs the cursor
    is inside (the spike's `enclosing_kinds`, generalized to the full path).
    Answers "am I in a match arm / a binding value / a field access / an argument
    list," *on broken input*.
  - `token_context(offset) -> TokenContext` — the token under or just before the
    cursor and its syntactic role (name-expecting position? field-access base?
    arm-pattern head? after a `.`?). This is what the completion provider filters
    on.
  Both are CST-only — no types — so they are fast and work on any recovered tree.
- **Typed views (what `lower.rs` consumes).** A thin typed layer over nodes (the
  spike's `ast.rs`), where **every accessor returns `Option`**, because a recovered
  tree can be missing any child. Lowering reads `decl.name()`, `decl.value()`,
  `match_expr.arms()`, each an `Option`/iterator, and skips what is absent (the
  parser already reported it). This replaces today's pest walk —
  `.into_inner()`, `.as_rule()`, `.as_str()`, the peekable `Pairs` — that
  `lower.rs` uses in ~57 `Pair`/`Pairs` and ~80 `Rule::` sites. The flat operator
  run survives as an `OpRun` typed view feeding the unchanged `prec` code.

**The CST/checker split for completion (what answers what).** Stated plainly so the
staged plan can schedule it:

| Completion feature | Needs |
|---|---|
| keyword expected here; `done`/bracket insertion hint | CST only (`@expect`/`MISSING`) |
| arm-pattern head is a tag; field name after `.`; argument position | CST only (`enclosing_path`/`token_context`) |
| in-scope variable names at the cursor | the **checker** (scope at offset) |
| builtins / prelude names | the checker's prelude scope (or a static list for the pragmatic tier) |
| the tags of a scrutinee's type; the fields/methods of a value's type | the **checker** (type at offset) |

### 5. Pure-Rust / `wasm32-unknown-unknown` — confirmed, with nothing to special-case

The whole parser is pure Rust: an embedded grammar string, a bootstrap reader, the
interpreter, the arena CST, the typed views. No C (unlike tree-sitter), no
build-time code generation (unlike pest's derive — our grammar is *data read at
runtime*, not generated code), no `cc`, no filesystem at runtime, no
target-specific code. The one dependency is `unicode-ident` (already in the tree).
This keeps the CLAUDE.md portability rule — the compiler crates (`parser`,
`checker`, future `mir`/`wasm`) build for `wasm32-unknown-unknown` with no native
toolchain. The grammar compiles into the binary via `include_str!` and the reader
runs once at init.

Size is a consequence to **measure, not promise**. pest's full generated parser is
302 KB as standalone wasm; the spike's rowan-slice (a third of the grammar) was
82.6 KB including std. An interpreter carries no generated-parser bloat, so the
footprint should be comparable-or-smaller; P6 measures it.

### 6. Migration — build alongside pest, reach parity, then switch and retire

Build the new parser beside pest and keep **pest authoritative until parity**.
Parity is proven against three corpora at once: ADR 0018's one Rust conformance
suite, the existing ~973 lines of parser tests, and `examples/*.goat`. The bar is
not just "both parse" but "both **lower to the same HIR**" — run every valid
program through both and diff the lowered output (the spike's recommended method).
Only then switch `lower.rs` onto the CST, and only after that delete pest.

One migration detail worth stating: **the editor lexer is pest-based today**
(`parser/src/lexer.rs` drives off `Rule::lex`) and already does its context work in
Rust (contextual `from`/`to`/`in`/`foreign` keywords, tag detection). The new
engine needs a lexer too, so the clean first move is a single hand-written lexer
shared by the highlighter and the parser — a small, self-contained step that also
takes pest out of the highlight path. It is sequenced first (P1) because it is
independent and de-risks everything after it.

**Framing the value — why this is worth building at all.** A *pragmatic*
autocomplete ships on pest **now**, independent of this build (P0): lexer tokens +
builtins-from-the-prelude + a visible-scope name scan, no recovery needed. That
gives kids prefix-completion of commands and their own names today. The new parser
**upgrades** that to *semantic* (type-aware: `turtle.` offers turtle's methods;
`match` offers the scrutinee's tags) and *robust-in-broken-code* (it works while
the line is unfinished, which is always). The completion UI and plumbing
(CodeMirror 6 provider, the completion API) are built **once** against a stable
interface in P0; the new parser swaps the *data source* behind that API, not the
UI. So: pragmatic completion now → semantic completion is the reason we build the
real parser.

This migration is **deferred**. Nothing forces it until completion/LSP is the
active goal; highlighting and live type-checking already work on pest.

### 7. Relation to the Coq proofs — a first-class artifact, nothing overclaimed

> **Superseded by [ADR 0030](0030-verified-parser-core-fragment.md):** the parser is verified for the core fragment, over a trusted token stream.

goat's proofs (ADR 0008) are about the **type system** — progress and preservation
over an *abstract-syntax* declarative core, authored in **Ott**, which generates
the typeset spec and the Coq definitions from one source. Ott models typing and
reduction over abstract terms; it says nothing about concrete surface syntax. So a
formal *grammar* does **not** feed the existing proofs, which begin after parsing,
at abstract syntax.

The honest connection is one of kind, not of mechanism:

- A declarative grammar makes the surface-syntax → abstract-syntax mapping (what
  `lower.rs` does) an **inspectable, first-class artifact**, the same way
  `docs/semantics.md` (Ott) makes the typing rules first-class. Two legible
  declarative specs at two layers of the pipeline.
- If goat ever wanted to *prove* a property about parsing — unambiguity, or that
  lowering preserves a grammar invariant — the formal grammar is the object a
  proof would reference. Today none does.

We **do not** propose a verified parser or a mechanized grammar. That is a tar pit
that buys the three requirements nothing. The grammar is a first-class artifact a
future proof *could* reference — no more. (ADR 0008 keeps the same discipline of
recording what a proof does not cover, to prevent over-claiming.)

### 8. Risks and the simplest-viable cut

**What could make this a tar pit:**

- **Building a general parser framework.** The interpreter must handle exactly the
  PEG constructs goat's grammar uses and the three recovery annotations — nothing
  configurable, no grammar-DSL ecosystem, no features no rule exercises. This is
  the main gold-plating risk and the easiest to rationalize; resist it.
- **Recovery quality below hand-RD.** A generic interpreter can recover worse than
  a hand-tuned parser on a given construct (the spike saw tree-sitter do so).
  Measured by the prefix/corpus bar (§3); closed by adding an annotation, or at
  worst a single hand-override hook for one rule.
- **Non-terminating / exponential recovery** — the real bug the spike hit. Closed
  by the termination invariant (§3) and fuzzing for it.
- **Two grammars drifting during migration.** Bounded: the grammar is ~227 lines,
  the migration is time-boxed, and the corpus diff keeps them honest.
- **Over-investing before completion needs it.** The build is deferred; do not
  start it until semantic completion is the active goal.

**The simplest version that delivers all three requirements:**

- One `grammar/goat.peg` = today's grammar in cleaned EBNF + `@sync`/`@expect`/
  `@anchor` annotations. *(formal grammar)*
- A few-hundred-line PEG interpreter: `Seq`/`Choice`/`Repeat`/`Opt`/`Token`/
  `RuleRef`/`NotAhead` + infallible parse + panic-mode-to-sync + required-token
  insert + `ERROR`/`MISSING` nodes + the termination invariant. *(recovery)*
- A flat-arena CST + `Option`-returning typed views + `enclosing_path` /
  `token_context`. *(serves completion)*
- Pure Rust, `include_str!` grammar, `unicode-ident` only, builds wasm32. *(pure
  Rust / wasm32)*
- Precedence stays in `lower.rs`'s existing `prec` (no new Pratt engine).

**Explicitly out of the cut:** packrat memoization (not needed — files are small,
and memoization fights recovery); incremental reparse (not needed); lelwel-style
auto-computed recovery sets (a later option); a rowan red-green interned tree
(rejected); a tree-sitter editor grammar (separate and deferred, see below).

## Staged ticket plan

Dependency-ordered. Each line: scope — acceptance.

- **P0 — Pragmatic completion on pest (ships now, independent of this build).**
  CodeMirror 6 completion UI + a stable completion API; data source = lexer tokens
  + prelude/builtin names + a visible-scope name scan, no recovery. — Typing a
  prefix offers in-scope names + builtins; the UI and API are the ones the new
  parser will reuse. *(No dependency; unblocks the kids'-discoverability win
  immediately.)*
- **P1 — Shared hand-written lexer.** Move tokenization off pest's `Rule::lex` into
  one lexer feeding both the highlighter and the new parser; keep the contextual-
  keyword and tag post-processing. — `tokenize`/`highlight` byte-identical to today
  on the corpus; parser crate builds wasm32; no pest in the lexer path. *(Depends:
  none. De-risks everything after.)*
- **P2 — Grammar formalism + interpreter parsing VALID input to the CST, at pest
  parity.** `goat.peg` (grammar + annotations), the bootstrap reader, the PEG
  interpreter (valid input only, no recovery yet), the flat-arena CST + typed
  views. — Every valid corpus program + the ~973 parser tests + `examples/*.goat`
  parses to a CST that lowers (via a throwaway adapter) to the **same HIR** as
  pest. *(Depends: P1. Requirement 1 + the CST, proven before recovery.)*
- **P3 — Error recovery (the hard part).** Infallible parse, panic-mode-to-sync,
  required-token insert, `ERROR`/`MISSING` nodes, the termination invariant, the
  fuzz target. — Lossless CST for 100% of valid-program prefixes (the rowan bar);
  the broken-snippet suite (§3) yields the expected spanned diagnostics; fuzz clean
  for never-panics/always-lossless/always-terminates. *(Depends: P2. Requirement
  2.)*
- **P4 — `lower.rs` consumes the CST (parity; pest kept as the oracle).** Replace
  the `Pairs` walk with the typed `Option` views; keep `prec` unchanged; dual-run
  against pest. — Full suite green through the CST path with pest still present;
  lowered HIR diffs clean against pest on the whole corpus. *(Depends: P3. Unblocks
  the checker-on-CST, hence semantic completion.)*
- **P5 — Semantic completion (the payoff).** A checker query over the recovered
  CST — `scope_at(offset)` (in-scope names + their types) and `type_of(node)` — and
  a completion provider that joins it with `enclosing_path`/`token_context`. —
  `turtle.`␣ offers turtle's members by type; a binding value offers in-scope names
  + builtins + tags; a `match` arm offers the scrutinee's tags; **all on
  broken/incomplete buffers.** CST-only features (keyword/arm/field structure) need
  no checker; the name/field/tag features need the `scope_at`/`type_of` queries.
  *(Depends: P4. The near-term reason for the whole build.)*
- **P6 — Retire pest.** Delete the pest dependency, the `#[derive(Parser)]`, and
  `grammar.pest`; `goat.peg` becomes the single source of truth; measure and report
  wasm size vs pest's 302 KB. — Suite green on the new parser only; pest gone from
  `Cargo.toml`; size recorded. *(Depends: P4/P5 proven in the field. Trailing
  cleanup; does not block completion.)*
- **P7 (optional, later) — tree-sitter editor grammar.** Only if someone needs
  external editors (Neovim/Zed/Helix/GitHub). A separate editor-only grammar kept
  honest by the shared corpus (`examples/*.goat` must parse error-free under both).
  — Deferred per the spike; not part of the compiler path.

## Consequences

- goat gains a parser whose spec *is* its grammar, that recovers on any input, and
  that stays pure-Rust/wasm32 — the three requirements, with the grammar kept
  authoritative (the point on which this ADR departs from the spike).
- The invariants hold. User-facing errors still come only from the checker: the
  parser emits *syntactic* diagnostics (which the checker already surfaces), and
  mono/MIR/codegen are untouched. The compiler crates stay C-free and
  wasm32-portable.
- Completion moves in two steps the owner can take independently: a pragmatic tier
  on pest now (P0), and a semantic, robust tier once this parser lands (P5), behind
  one unchanged UI.

### Reversible (not one-way doors)

- The engine choice (interpreter vs generator vs hand-RD). All three consume the
  same `goat.peg`; swapping engines later does not touch the grammar or the CST
  consumers.
- The recovery-set strategy (explicit `@sync`/`@anchor` vs lelwel-style auto-
  computed sets). An annotation detail, swappable.
- Pragmatic completion (P0) is throwaway plumbing behind a stable API; the new
  parser replaces its data source without a UI rewrite.

### One-way-ish door

- Retiring pest (P6). Reversible only by keeping pest's `grammar.pest` around;
  cheap to defer, costly to undo once deleted — hence P6 trails parity and the
  dual-run, and is not rushed.

## References (external, as of 2026-11)

- A. Kladov (matklad), *Resilient LL Parsing Tutorial* (2023) — hand-written
  resilient recursive-descent + Pratt, `ERROR` nodes, follow-set recovery; the
  design rust-analyzer uses. https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html
- rust-analyzer, *Challenging LR Parsing* (2020) and the syntax guide — lossless,
  infallible, resilient trees; parser errors kept out of the tree.
  https://rust-analyzer.github.io/blog/2020/09/16/challeging-LR-parsing.html
- *lelwel* — a Rust recursive-descent generator implementing matklad-style
  resilience with recovery sets computed from grammar dominators (prior art for the
  generator option and for auto-recovery-sets). https://docs.rs/crate/lelwel
- Maidl, Mascarenhas, Medeiros et al., *Error Reporting in PEGs* (2014),
  *Syntax Error Recovery in PEGs* / recovery expressions (2018), and
  *Towards Automatic Error Recovery in PEGs* (arXiv 2507.03629, 2025) — labeled
  failures and recovery expressions, the formal basis for the `@sync`/`@expect`
  annotations and the honest note on automatic annotation.
- Pratt / precedence climbing — the standard expression-parsing method; here it
  stays in `lower.rs` (ADR 0013's flat operator runs).
