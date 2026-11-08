# Spike: parser future (pest vs tree-sitter vs a pure-Rust resilient parser)

Status: spike findings, not a decision. Prototype code is throwaway and lives in
`spike/parser-future/` (its own Cargo workspace, not a member of the root
workspace, so CI and `cargo test` at the root never build it). The real pest
parser is untouched.

## The question

pest bails at the first failure, which blocks editor and LSP features (completion
above all). Incrementality is not the need (goat files are small). The needs are
error recovery, staying `wasm32-unknown-unknown`-pure, and one source of truth.

## What was built

Every candidate parses the same slice: the binding chain (`name = value ;?`), flat
binary-operator runs, `-`/`not`, calls, field access, parens, and
`match expr do arm* (else expr)? done` with `arm = pattern then expr`. Not covered:
operand-position bindings (`1 + x = 2 x`), tag declarations, foreign declarations,
records, lists, loops, functions, destructuring, spreads.

| Candidate | Where | Size |
|---|---|---|
| B1: hand-written lexer and recursive descent over a `rowan` green tree | `spike/parser-future/rowan-slice` | 734 lines (lexer 97, parser 449, typed AST view 76, rowan glue 112), 13 tests |
| B2: `chumsky` 0.13 combinators with `recover_with` | `spike/parser-future/chumsky-slice` | 214 lines, 10 tests |
| A: tree-sitter grammar, Rust binding, web-tree-sitter glue | `spike/parser-future/tree-sitter-goat-slice`, `ts-rust`, `web-glue` | grammar.js 72 lines (generates a 133 KB `parser.c`) |

Reproduce (from `spike/parser-future`):

- Rust candidates: `cargo test`; `cargo run -p rowan-slice --example demo` (tree dumps
  next to pest's error); `cargo run --release -p chumsky-slice --example nesting`.
- wasm32: `cargo build --lib --target wasm32-unknown-unknown --release -p rowan-slice`
  (likewise `-p chumsky-slice`); sizes via `--examples` builds of `size_*`.
- tree-sitter: in `tree-sitter-goat-slice`, `npm install`, `npx tree-sitter generate`,
  `npx tree-sitter parse inputs/*.goat`, `npx tree-sitter build --wasm -o goat_slice.wasm`.
  Rust binding on wasm32: `AR_wasm32_unknown_unknown=<llvm-ar> cargo build --lib
  --target wasm32-unknown-unknown --release -p ts-rust`, then `node ts-rust/run.mjs
  target/wasm32-unknown-unknown/release/ts_rust.wasm`. Browser glue: `npm install` in
  `web-glue`, serve `spike/parser-future` statically, open `web-glue/index.html`
  (`node web-glue/glue.mjs` runs the same code in Node).

## Measured results

### Error recovery

Inputs, each broken at one point, with a good binding after it:

| Input | pest (full goat grammar) | rowan | chumsky | tree-sitter |
|---|---|---|---|---|
| `a = ;` then `b = 2; b` | 1 error, no tree | 1 spanned error; tree keeps `a` (value missing) and `b` | same | `a` stranded as a name, `=` in an ERROR node, `b = 2` intact |
| `match x do` (EOF) | 1 error ("expected arm"), no tree | 1 error "expected `done` to close `match`, found end of file" at 10..10; `MatchExpr` node present | match kept, 1 error | `(MISSING "done")` inserted, match kept |
| `m = match x do A then 1` then `y = 2; y` | 1 error at `y`, no tree | 1 error at `y`; `m` and `y` both bound, `y` outside the match | same | `m = match ...` and `y` swallowed into one ERROR node |
| `match s do Circle(r) then done` (arm body missing) | no tree | 1 error; arm kept, `done` still closes the match | arm kept with `Error` body | `done` parsed as the arm body, MISSING `done` at EOF |
| `match s do Circle(r) r * r Square(s) then s done` (`then` missing) | no tree | 1 error "expected `then`"; both arms kept | both arms kept (after adding a `then` recovery point) | ERROR node swallows the first arm |
| three independent errors in one file | 1 error | 3+ errors, all 4 bindings kept | 2 errors and no output at all (see below) | tree with ERROR nodes, no messages |

Findings that matter for the decision:

- **rowan** gives a tree for every input, including every prefix of a valid program
  (test `every_prefix_of_a_valid_program_parses_losslessly`: all 173 prefixes of the
  sample produce a lossless tree; pest produces a tree for 61 of them, 35%) and the
  tree reproduces the source byte for byte. Diagnostics carry hand-written messages
  and byte spans. `enclosing_kinds(root, offset)` answers "what construct is the cursor
  in" on the broken `match x do`, which is the primitive completion needs.
- **chumsky** recovery is opt-in per combinator. Where I placed a recovery point it
  worked; where I did not, the parse returned *no output*, the same all-or-nothing
  outcome as pest (`an_unrecovered_error_loses_the_whole_tree`; also `x = 1 + ;`
  lost everything until I added a recovery point on the right operand). It also
  yields an AST rather than a lossless tree: no trivia, so formatting and
  comment-preserving edits need a second structure. Its guide's recovery chapter is
  still marked TODO in the 0.13.0 sources.
- **chumsky cost**: with `nested_delimiters` recovery, unclosed `(` nesting costs
  12.9 ms at depth 100, 457 ms at 400, 6.7 s at 1000, 52.6 s at 2000 (release build,
  `examples/nesting.rs`): roughly cubic. rowan stays linear with a depth cap of 256
  (100,000 `(` parse in well under a second; a first version without the
  give-up-at-depth rule was exponential, which is the kind of bug hand-written
  recovery invites, caught by `hostile_input_does_not_overflow_the_stack`).
- **tree-sitter** always yields a tree and `MISSING` nodes are excellent for
  completion ("a `done` belongs here"), but it produces no messages (diagnostics
  are synthesized from ERROR/MISSING nodes: "unexpected input" at `2..27` for the
  unterminated-match case) and its recovery chose worse trees than rowan in 3 of 5
  cases above. Its recovery is generated, so improving a bad case means grammar
  surgery, not adding a branch.

### Does it build for `wasm32-unknown-unknown`?

| | Result |
|---|---|
| rowan-slice | `cargo build --lib --target wasm32-unknown-unknown --release`: clean, no C. Deps: rowan, unicode-ident (rowan pulls countme, hashbrown, memoffset, rustc-hash, text-size). 82.6 KB standalone `.wasm` (includes std). |
| chumsky-slice | Builds clean. Default features pull `stacker` and `psm`, which compile on wasm32 but are dead weight there. 314 KB standalone `.wasm`. |
| pest, for scale | The real full grammar: 302 KB standalone `.wasm`. The two slices are not full grammars, so compare only the order of magnitude. |
| **tree-sitter Rust crate (0.27.2)** | **Builds and runs on wasm32-unknown-unknown**, which contradicts the premise that it cannot. 0.27 vendors a minimal libc for the target and forwards `malloc`/`free` to the Rust allocator. I linked the generated slice parser, loaded the 162 KB `.wasm` in Node with an empty import object, and `has_error` returned the right answer for four inputs. |

The tree-sitter result has strings attached, all found by hitting them:

1. The grammar's `parser.c` must be compiled by `cc` in a `build.rs`, so the parser
   crate acquires a C-compiler requirement on every target. `CLAUDE.md` keeps `cc`
   out of the compiler crates exactly so those crates build with no C toolchain.
2. The grammar's build must add `tree-sitter-language`'s wasm headers
   (`DEP_TREE_SITTER_LANGUAGE_WASM_HEADERS`); without them `#include <stdlib.h>`
   fails on this target.
3. Needs a clang with the wasm32 backend (Apple clang 21 has it) and a GNU-format
   archiver. With Apple's BSD `ar` the build succeeds but linking fails with
   `undefined symbol: tree_sitter_goat_slice`, because rust-lld cannot read BSD
   archives. Setting `AR_wasm32_unknown_unknown` to rustup's `llvm-ar` fixed it.
   Not verified on Linux CI.
4. Runtime and grammar ABI must move in lockstep: tree-sitter-language 0.1.8 and
   later reject tree-sitter 0.26 at compile time, and many third-party grammar
   crates lag.

### Tree-sitter in the browser (the split architecture)

Stood up and verified: `tree-sitter build --wasm` produced a 29 KB grammar `.wasm`
(it downloaded a 171 MB wasi-sdk on first use); `web-tree-sitter` 0.27.2 parsed the
slice in Node (`web-glue/glue.mjs`) and **in Chrome from a static page**
(`web-glue/index.html`, served with `python3 -m http.server`), printing the same
trees, including `(MISSING "done")`. Page weight: runtime `.wasm` 211 KB (83 KB
gzipped), JS loader 155 KB, grammar 29 KB (8.5 KB gzipped), on top of `goat_web`.

Not built: the checker side. Handing the tree to the Rust checker means JS walks the
tree into a wire format (the glue serializes it to JSON, 0.6 to 2.1 KB for the test
inputs) and `lower.rs` consumes a deserialized tree instead of pest pairs. That is
the same rewrite of `lower.rs` as the pure-Rust option, plus a JS marshalling layer,
plus two build pipelines (the compiler wasm and the grammar wasm) that must agree.
The native CLI/Apple hosts would still use the Rust binding, so the browser would
run a different parser build than every other host, which breaks the single-source
property for tests (ADR 0018's one Rust conformance suite would not cover the
browser path).

## Migration shape (estimate)

pest is used only in `goat_parser` and `checker/src/lower.rs`
(`checker/Cargo.toml` depends on `pest` and `goat_parser`). `lower.rs` references
`Rule::` 80 times and `Pair`/`Pairs` 57 times in 2,612 lines. Any non-pest option
replaces the pair-walking in `lower.rs` with a typed CST/AST view: the slice's
`ast.rs` shows the shape (every accessor returns `Option`, because a recovered tree
can be missing any child; lowering skips what is absent since the parser already
reported it). The flat operator run is kept as in pest, so the existing
precedence code in `lower.rs` (`prec`) survives unchanged.

For the hand-written parser, the slice covers roughly a third of `grammar.pest`'s
shape in 734 lines, so a full parser is on the order of 1,500 to 2,500 lines plus the
`lower.rs` rewrite. That is a guess from one slice, not a measurement. The 110 rules
and 973 lines of existing parser tests give a ready conformance corpus: run every
valid program through both parsers during the migration and compare lowered output.

## Keep-pest baseline

pest compiles to a PEG with ordered choice and reports the single furthest failure,
so the parse of a half-typed buffer is `Err` with no tree: no scope at the cursor, no
"inside a `match`" fact, no later bindings, no second error. The measured cost is the
prefix test above: for 65% of the prefixes of a valid program (the editor's actual
input while typing) pest yields nothing, so completion, hover, and go-to-definition go dark
the moment a file is mid-edit. pest is fine for the compile path and stays correct;
it cannot be taught recovery without wrapping or replacing it.

## What tree-sitter uniquely buys

An external-editor ecosystem: one `grammar.js` gives highlighting, folding, and
text-objects in Neovim, Helix, Zed, and GitHub rendering, and a `highlights.scm` is
a few lines. goat's hosts are native (SwiftUI) with their own editor widgets, so
this benefit applies to people editing `.goat` files in third-party editors, which
nobody does yet.

## Recommendation

**Migrate to a pure-Rust resilient parser built on rowan (hand-written lexer and
recursive descent), and defer a tree-sitter grammar until someone needs external
editors.** If one is wanted later, write it as a separate editor-only grammar and
keep it honest with a shared corpus (`examples/*.goat` must parse error-free under
both).

Reasons, each tied to a measurement above:

1. It is the only candidate that satisfies all three needs without a caveat: recovery
   (a usable tree for every input and prefix, spanned messages), wasm32 purity (no C,
   82.6 KB for the slice), and one source of truth (the parser is the grammar; the
   same crate runs in the CLI, Apple hosts, and `goat_web`).
2. The original argument for tree-sitter, that its Rust crate cannot build for wasm32,
   no longer holds (0.27.2 builds and runs). The remaining case against it is
   different and still strong: it reintroduces `cc` and a wasm-capable clang into the
   compiler crates, has no diagnostics text, recovered worse trees in 3 of 5 cases,
   and locks the runtime and grammar ABI together. Browser-split via web-tree-sitter
   works (verified in Chrome) but means the browser runs a different parser than
   every other host.
3. chumsky is the weaker B: all-or-nothing outside hand-placed recovery points, an
   AST with no trivia, cubic recovery cost on unclosed delimiters, and a 314 KB slice.
4. The cost is real: goat's context-sensitive pieces (a binding as an operand, tag
   groups, the keyword-boundary rules) must be hand-ported, and a hand-written
   recovery parser invites exactly the kind of bug the depth test caught. Mitigate
   with the dual-parser comparison during migration and by fuzzing (`fuzz/` already
   exists) for "never panics, always lossless, always terminates".

## What I could not do in the time box

- Only a slice is covered; the full grammar, `local` operands, and `lower.rs` were not
  ported, so the size estimate is extrapolated.
- No speed benchmark of rowan against pest on real programs. Only the nesting
  stress test was timed.
- No LSP: `enclosing_kinds` is a stub that shows the CST supports the query;
  completion candidates (expected tokens at a position) are not implemented.
- chumsky got about one hour of tuning; a chumsky expert might avoid the
  all-or-nothing cases and the cubic cost.
- tree-sitter on Linux CI (clang and `llvm-ar` availability) was not tried, and the
  tree-sitter grammar was not tuned beyond resolving its conflicts, so its recovery
  quality could improve with `prec.dynamic` and `extras` work.
- The checker end of the browser glue (deserializing the tree in Rust) does not exist.
