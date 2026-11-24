# goat_apple

The engine the Apple apps embed (ADR 0043): goat compiled and run in-process on
wasmtime's Pulley interpreter, behind the C header `include/goat_engine.h`.
Native only. It is not in the wasm32 build, and the compiler crates never
depend on it.

- One worker thread owns the wasmtime store. A caller never waits on it, and a
  delivery thread hands messages to the host, so a slow host costs frames, not
  the program's time. A frame still waiting is replaced by a newer one.
- Every call into goat has a budget: 1 second for a frame, 10 seconds for setup,
  a reload or a run-once program, and a 128 MiB heap. A call that overruns, a
  trap or a heap overrun stops the program with a `failed` state and discards
  the store, so the next run starts clean.
- Running a source while an interactive program is live reloads it in place
  (ADR 0035) and says `reloaded` with `kept`, or `reset` and why. A source with
  errors leaves the live program running and sends only diagnostics.
- A run-once turtle program runs to its end, then its drawing is sent as frames,
  four segments at a time (more for a drawing longer than 3,600 segments, so
  that it never takes more than about 15 seconds), each frame fitted to the
  400 by 300 canvas.
- The vocabulary (turtle or canvas) is read from the names the program uses, by
  `goat_detect`, as `goat run` does.

In a workspace build, cargo unifies wasmtime's features across every crate, so
the trimmed set (`runtime`, `cranelift`, `pulley`, `std`) shows only when
`goat_apple` is built on its own: `cargo build -p goat_apple`.

Tests are in `tests/`: `engine.rs` drives the Rust API with a recording sink,
and `c_api.rs` drives the C functions.
