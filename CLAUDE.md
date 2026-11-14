# goat

A typed, GC-free, embeddable scripting language for creative coding — kids start
with a turtle. See `docs/plan.md` for the roadmap and `docs/adr/` for the
decisions that are expensive to reverse.

## Comments: keep them to a minimum

**The source should read as clearly as the language it implements.** Reach for a
clearer name, a smaller function, an extracted constant, or a type that makes the
wrong state unrepresentable *before* you reach for a comment.

- Do **not** write a comment that restates what the code already says.
- A comment earns its place only for what code cannot express: a non-obvious
  *why*, a deliberate tradeoff and its cost, a platform fact, a dated citation.
- Prefer one short line at the load-bearing spot over a paragraph, and over
  decorative `///`/`//!` banners on every item.
- If you can't name what a reader would get wrong without the comment, delete it.

## Working norms

- **Branches.** Mainline is `master`. Work on short-lived feature branches off
  `master`, open a PR to `master`, and merge on green. (The earlier `revival`
  integration branch has been folded into `master` and retired.)
- **Tracker.** GitHub issues (`thejefflarson/goat`). Decisions that outlive a
  ticket go in `docs/adr/`.
- **Gates (CI-enforced).** `cargo fmt --all -- --check`,
  `cargo clippy --all-targets -- -D warnings`, and `cargo test` must all be
  green before a PR merges.
- **Proof gate (ADR 0037).** A PR that changes `grammar/goat.peg`,
  `checker/src/{infer,lower,ty}.rs` or `prelude/prelude.goat` must also change
  `proofs/`. The `proof-gate` check waives this only for a PR with the
  `no-semantics-change` label and a body line starting `No semantics change:`
  followed by the reason. The `coq` check runs on every PR and skips its build
  when nothing it depends on changed.
- **Errors come only from the checker**, with one deliberate exception: mono may
  raise a spanned *resource-limit* diagnostic ("program too complex") when a
  well-typed program would explode monomorphization — a resource bound, not a
  type or logic error. Otherwise a user never sees an error from mono/MIR/codegen
  — those failing is an internal compiler bug. Every user-facing diagnostic
  carries a source span.
- **Tests.** Every feature gets a checker test and, where it runs, an
  end-to-end run test. Examples go in `examples/`.
- **Portability.** The compiler crates (`parser`, `checker`, and the future
  `mir`/`wasm`) must build for `wasm32-unknown-unknown` — keep native-only deps
  (wasmtime, filesystem, `cc`) out of them.
- **Worktrees.** All work MUST live inside this repo. Create every git worktree
  under `.claude/worktrees/` (gitignored, so it never shows in `git status`) —
  never as a sibling directory like `../goat-worktrees/`. A worktree is only a
  checked-out directory; the branch and its commits live in this repo's `.git`
  regardless, so an in-repo worktree loses nothing and keeps the tree self-
  contained.
- **Local Rocq toolchain.** The opam root for building the `proofs/` development
  lives at `/coq-toolchain/` (gitignored — it is ~1 GB and must never be
  committed). An opam root records absolute paths and breaks when moved, so a
  fresh root is **rebuilt in place** at that path, never relocated from
  elsewhere. The switch is `rocq-9`: OCaml 4.14.2, `opam install coq.9.1.1
  ott.0.34` (Rocq 9.1.1; `coq` is the compatibility metapackage that pulls in
  `rocq-core`, and metalib depends on it), then `opam pin add -n coq-metalib
  <plclub/metalib>#144ddcd0fff6717229140314cf559d85fad6eae0` and `opam install
  coq-metalib`. Build with `opam exec --switch=rocq-9 -- make -C proofs ci`. Rocq
  9.2 and 9.3 do not work yet: metalib's `CoqListFacts.v` fails to compile on
  them. CI runs the same switch on the self-hosted runner image
  (`.github/workflows/coq.yml`), so nothing in the repo depends on this local
  toolchain; it is a convenience for running `make -C proofs ci` locally.
