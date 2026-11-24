# Goat apps on Apple: one in-process engine, one renderer, exported apps

Owner, 2026-11-23: "I like the real .app idea, and I'd love a macos and ios
app." Decisions: export makes **both** kinds of app, a player by default and
native when the Command Line Tools are present; the in-process engine replaces
the web view, **gated** on spike S1; distribution is decided **later**. The
decisions are in [ADR 0043](../adr/0043-apple-apps-run-goat-in-process-and-export-apps.md).

## What exists

- `hosts/apple`: one SwiftUI codebase with macOS and iOS targets. The editor is
  native. Programs run in a `WKWebView` (`web/embed.html` plus
  `goat_web.wasm`). Run never reloads, and the watchdog kill path is untested.
- `goat build --native`: a windowed AppKit executable, built with clang and
  swiftc, with no app bundle.
- `goat::native::Interactive` (reload over a shared memory) and
  `Guest::with_timeout` (epoch preemption) on wasmtime, both conformance-tested.

## Assumptions the brief checked

- **"A real .app means native code."** Not for kids. Native needs Apple's Command
  Line Tools. Apple's SDK stubs can't be redistributed, and `xcrun` refuses to
  run inside the App Sandbox. What the kid needs is their own double-clickable
  app, and a player template gives that.
- **"WAMR in-process."** No, for now. The vendored WAMR 2.4.5 cannot stop a
  spinning loop (`THREAD_MGR=0`). It also cannot give two instances one
  host-created memory, which reload needs. WAMR stays the board hot-swap path.
- **"wasmtime's JIT in the macOS app."** No. wasmtime doesn't use `MAP_JIT` yet
  (wasmtime #11989), and iOS forbids a JIT. Pulley, wasmtime's interpreter,
  runs on both platforms and in CI.
- **"Ad hoc signing is enough to share."** Partly. An app made on the same Mac
  runs. A copied one needs Privacy & Security → Open Anyway once. A broken
  signature reads as "damaged", with no override, so export must re-sign.
  `/usr/bin/codesign` ships with every Mac.

## Approaches compared

- **macOS export:**
  - native through the Command Line Tools: costs the sandbox, and kids lack the
    tools;
  - **a player template**, the LÖVE and Godot model: small and sandbox-safe;
  - a bundled toolchain: 100 MB or more, and hard to ship.
- **The editor engine:**
  - keep the web view: two renderers, and exported apps would ship a web view;
  - **in-process wasmtime on Pulley**;
  - in-process WAMR: blocked on reload and preemption.
- **iOS:**
  - **in-editor Play mode**;
  - exporting an Xcode project from the Mac: next sprint;
  - building on the device: impossible for third parties.

## Sequence (after #263, #289, #684)

1. **A1, the CLI `.app`.**
   - `goat build --native examples/canvas/bounce.goat -o Bounce.app` writes the
     bundle layout.
   - `codesign --verify --strict` passes.
   - The binary runs headless.
   - A run-once program refuses `.app` with a clear message.
2. **A2, a shared GoatCanvas.** One source for `Frame`, `Painter` and `Color`.
   The headless native tests and `swift test` pass unchanged.
3. **S1, the Pulley spike** (gates A4–A7).
   - The conformance suite runs under a `GOAT_RUNTIME=pulley` lane, which stays
     in CI.
   - An epoch timeout stops a tail-call loop.
   - The engine builds for iOS and the iOS simulator.
   - Frame time on an iPhone is under 8 ms p95.
   - The size delta is measured.
   - The result is a go or no-go.
4. **S2, a sandboxed signing spike.** Can the sandboxed editor run `codesign` and
   write a bundle to a folder the user picked? If not, use the pure-Rust
   `apple-codesign` crate.
5. **A4, the `goat_apple` engine crate**, built to `goat_engine.h`. Rust tests
   cover:
   - run;
   - reload that keeps the model, and reload that resets with a reason;
   - a stuck call stopped within its budget;
   - a trap;
   - print output;
   - run-once turtle programs as frames.
6. **A5, the xcframework.** Builds for aarch64 and x86_64 macOS, iOS and the iOS
   simulator, and CI builds it.
7. **A6, swapping the engine.**
   - A native canvas view replaces the web view, `AssetSchemeHandler`,
     `Watchdog.swift`, the web staging and the two entitlements.
   - Swift glue tests check the pixels, recovery from a stuck program, and a
     reload that keeps the model.
   - The iOS UI smoke test still passes.
8. **A7, GoatPlayer and Export App…** (both kinds).
   - The player is the default.
   - Native is offered when the Command Line Tools are present.
   - The exported app opens by double-click with Goat removed.
   - `codesign --verify --deep --strict` passes.
   - The menu item is disabled while the program has diagnostics.
9. **A8, iOS Play mode**: a full-screen canvas.
10. **A9, docs**: the README, and the App Store 2.5.2 text.

Each item merges to `main` shippable on its own.

## Deferred

- iOS Xcode-project export.
- Notarization.
- Cranelift on macOS, until wasmtime supports `MAP_JIT`.
- Icons from a program's first frame.
- `.app` for run-once programs in the CLI.
