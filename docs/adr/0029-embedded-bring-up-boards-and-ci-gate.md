# ADR 0029 — Embedded bring-up: boards, memory presets, and what CI proves without a board

- Status: accepted (2026-11-11)
- Decision:
  1. **Two boards, two jobs.** The ESP32-C6 is the first *engineering* bring-up board:
     it has first-party WAMR support through ESP-IDF, and its 512 KB of SRAM holds the
     256 KiB arena of ADR 0026. The first public *demo* is filmed on an RP2040 (a Raspberry
     Pi Pico), the classroom flagship, where "a typed language with no garbage collector
     runs in 64 KiB" beats the MicroPython story.
  2. **Foreign-first for v1.** A board program talks to its hardware through
     `foreign` declarations (ADR 0020, ADR 0024). v1 adds no WIT and no host `Vocab` for
     boards, and an interactive program on a board stays out (ADR 0017).
  3. **Per-board memory presets are data.** `goat_wasm` exposes `EmbeddedLimits::C6`,
     `C3` and `RP2040`, and `goat build --target embedded --board c6|c3|rp2040` selects
     one. Each preset is a whole number of 64 KiB pages, because memory is declared
     `minimum == maximum` and custom page sizes are refused (ADR 0026): 4 pages
     (256 KiB) for the C6 and C3, 1 page (64 KiB) for the RP2040, whose 264 KB of SRAM
     cannot hold 256 KiB. Each preset's `heap_bytes` is its pages minus an 8 KiB reserve for
     static data and the allocator's table, so a program with under 8 KiB of statics fills
     exactly those pages. The values are placeholders until they are tuned on hardware.
  4. **What CI proves without a board.** The gate is (a) the vendored WAMR cross-compiles
     for `riscv32imc` and `thumbv6m` with tail calls and bulk memory on, the link
     succeeds, and a build with either flag off is rejected; and (b) every example built
     for each board validates host-side with memory pages within that board's budget.
     Loading a module on a target is deferred, and CI has no QEMU-riscv32 job.
  5. **Board builds live in `firmware/`.** `wamr/build.rs` keeps panicking on any
     architecture but x86_64 and aarch64 hosts. It builds the conformance driver and must
     not grow a cross-compile path.
- Context: Phase 12 (`docs/plan.md` "Microcontrollers"), ADR 0019 (WAMR on device, with
  a feature floor of tail calls and bulk memory), ADR 0025 (the host driver's two
  interpreters) and ADR 0026 (the fixed arena). Before any board runs goat, the build
  half of "WAMR on a board" and the sizing half of "a heap that fits" are checkable in
  CI; this ADR records what is checked and what waits for hardware.
- Consequences:
  - `firmware/build.sh` compiles the interpreter with a minimal single-threaded
    platform layer (`firmware/platform/`) and links a program that initializes the
    runtime and loads a module, against newlib on `thumbv6m` and picolibc on `riscv32imc`.
    It reuses `wamr/csrc/floor.c`, so a flag that is off fails the compile exactly as it
    does for the host driver. Its source list mirrors `wamr/build.rs`; a change to one
    changes the other.
  - Linking proves the runtime resolves against a board's C library. It does not prove the
    runtime runs, nor that a module loads, under that architecture's real memory map. The
    first on-target load, and the tuning of the presets and the call depth, happen on
    hardware. Adding a QEMU job later is reversible and changes no code here.
  - A program whose static data exceeds a preset's 8 KiB reserve declares one more page than
    the board's budget; `goat build` does not yet warn about it.
  - The ESP-IDF build of the C6 uses Espressif's WAMR component, not `firmware/`. The
    CI cross-build covers the architecture, not that port.
