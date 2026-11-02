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

- **Branches.** Mainline is `master`. Current integration branch for the
  compiler revival is `revival`; sprint PRs target `revival`, which merges to
  `master` when green.
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
