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
- **Errors come only from the checker.** A user never sees an error from
  mono/MIR/codegen — those failing is an internal compiler bug. Every
  user-facing diagnostic carries a source span.
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
- **Local Coq toolchain.** The opam root for building the `proofs/` development
  lives at `/coq-toolchain/` (gitignored — it is ~1 GB and must never be
  committed). An opam root records absolute paths and breaks when moved, so a
  fresh root is **rebuilt in place** at that path (Coq 8.20.1, Ott 0.34, metalib
  pinned — the recipe in `.github/workflows/coq.yml`), never relocated from
  elsewhere. CI builds the proofs in a Coq Docker image, so nothing in the repo
  depends on this local toolchain; it is a convenience for running
  `make -C proofs ci` without the Docker round-trip.
