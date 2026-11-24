# ADR 0043 — The Apple apps run goat in-process and export programs as apps

- Status: accepted (2026-11-23); the engine half is gated on spike S1
- Builds on: [ADR 0042](0042-a-second-backend-emits-llvm-ir-for-native-binaries.md)
  (the native backend), [ADR 0015](0015-host-owned-event-loop-contract.md),
  [ADR 0018](0018-native-first-test-drivers.md),
  [ADR 0021](0021-host-owned-preemption.md),
  [ADR 0035](0035-reload-keeps-data-and-rebinds-methods.md)
- Brief: [docs/ideas/apple-apps.md](../ideas/apple-apps.md)

## Context

`hosts/apple` is one SwiftUI app with macOS and iOS targets. Its editor, files
and problem list are native, but programs run in a `WKWebView` that loads
`goat_web.wasm`. That web view needs the JIT and network entitlements and an npm
staging step. Its watchdog kill path is untested, and Run never reloads.
`goat build --native` already makes an AppKit executable, but it writes a bare
Mach-O binary, and it needs clang and swiftc, which come from Apple's Command
Line Tools. Kids' Macs don't have those.

The owner wants a kid to turn a program into a real, double-clickable app, and
wants full macOS and iOS apps.

## Decision

1. **The engine.** The Apple apps run goat in-process on wasmtime's Pulley
   interpreter, on both macOS and iOS, and `WKWebView` leaves the Apple hosts.
   Pulley needs no executable memory, which iOS forbids and wasmtime's macOS
   JIT cannot yet allocate. The engine wraps `goat::native::Interactive`, so
   reload (ADR 0035) and epoch preemption (ADR 0021) are the code the
   conformance suite already covers. This is ADR 0042's "dev = wasm" path,
   hosted natively. The LLVM backend stays the release path. This decision is
   gated: spike S1 must show that goat's conformance suite passes under Pulley
   (tail calls and epoch interruption included), that it builds for iOS and the
   iOS simulator, and that frame time on an iPhone is under 8 ms p95. If S1
   fails, iOS keeps the web view and macOS still moves in-process.
2. **The seam** between Rust and Swift is a C header, `goat_engine.h`. Control
   messages are the existing `EngineMessage` JSON, plus
   `reloaded {kept | reset, reason}`. Frames are raw `scene.frame` bytes through
   their own callback. Only the engine's worker thread touches the wasmtime
   store, and Swift never blocks on it. Frames pass through a latest-wins slot.
   After a trap, the store is discarded.
3. **One renderer.** `Frame.swift`, `Painter.swift` and `Color.swift` become one
   `GoatCanvas` SwiftPM target. The editor, exported apps and
   `goat build --native` apps all draw with it.
4. **Export App… makes both kinds.**
   - **Player (default):** the editor copies a prebuilt, signed `GoatPlayer.app`,
     writes `Contents/Resources/program.goat`, sets the name, and signs the copy
     ad hoc. This works on any Mac with no toolchain, inside the sandbox, and
     the exported app runs exactly as the program did in the editor.
   - **Native, when the Command Line Tools are present:** the export compiles
     through ADR 0042's LLVM path into the same bundle layout.
   - Export is refused while the program has diagnostics. Bundle IDs are
     `local.goat.<slug>`.
5. **The CLI `.app`.** `goat build --native -o Name.app` writes a bundle
   (`Contents/MacOS/<name>`, `Info.plist`, `AppIcon.icns`) and signs it ad hoc.
6. **iOS** runs programs in the editor and in a full-screen Play mode. No
   third-party app can build another app on the device. Exporting an Xcode
   project from the Mac is deferred to a later sprint.
7. **Distribution** (App Store or Developer ID) is undecided. The apps stay
   sandboxed so that both channels remain open.

## Consequences

- One engine and one renderer replace two runtimes. The JIT and network
  entitlements, the npm staging step and `Watchdog.swift` go away.
- Programs in the editor run interpreted, which is slower than JavaScriptCore's
  JIT. S1 measures whether that matters for kids' programs.
- wasmtime adds an estimated 10–20 MB to the app and to each exported player.
- An exported player is frozen at the goat version that made it. That is
  intended: it never breaks when Goat updates.
- An app made and run on the same Mac runs without a prompt. A copied app is
  quarantined: since macOS Sequoia, the user allows it once under Privacy &
  Security → Open Anyway. Notarization would remove that step, but it needs a
  paid Developer ID, which is deferred with distribution.
