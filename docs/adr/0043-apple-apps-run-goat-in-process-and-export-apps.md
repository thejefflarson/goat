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

## Amendment (2026-11-24): spike S2 — the sandboxed editor can write and sign an export

Decision 4's player export needs two things inside the App Sandbox: writing a
bundle into a folder the user picked, and signing the copy ad hoc. Spike S2
tested both with `exportBundle(template:to:)` in `GoatKit` (`ExportBundle.swift`),
which copies the `.app` tree with `FileManager` and runs
`/usr/bin/codesign --force --deep --sign - <bundle>` through `Process`.
`ExportBundleTests` runs it inside `GoatTestHost-macOS`, which carries
`Goat-macOS`'s entitlements, and checks `codesign --verify --deep --strict`.
It passes on the `apple.yml` CI runner (`xcodebuild test -scheme
GoatKitTests-macOS`, ad hoc signed so the sandbox applies); a test asserts the
host's `APP_SANDBOX_CONTAINER_ID` is set, so the pass is a sandboxed pass.

What this shows:

- **`Process` and `codesign` work in the sandbox.** A sandboxed app may spawn
  `/usr/bin/codesign`; the child inherits the sandbox and needs no extra
  entitlement. Writing the bundle needs only
  `com.apple.security.files.user-selected.read-write`, which `Goat-macOS`
  already has. No temporary-exception entitlement is required.
- **The signature covers the whole tree, so sign last.** Adding
  `Contents/Resources/program.goat` to a signed bundle makes `--verify` fail;
  the export must write `program.goat` and `Info.plist` changes first, then
  sign. `exportBundle` signs once, so the player export should write its files
  into the copy before that call (the function will take a prepare closure
  when the real export lands).
- **What the test cannot cover.** A test cannot show `NSSavePanel`, so it
  writes under the container's temporary directory, which the sandbox always
  allows. With a real panel, the app receives a URL inside a folder the user
  chose, with its security scope open; the copy and the child `codesign` write
  there. We expect the child to write under the parent's scope, but a
  scope-open write by a spawned child is not proved by CI. The first real
  Export App… implementation must run this once by hand (save panel, then
  `codesign --verify`) before the ticket closes. Keep the scope open
  (`startAccessingSecurityScopedResource`) until `codesign` exits.
- **Quarantine is unchanged.** Files the app writes are not quarantined, so an
  export made and run on the same Mac opens without a prompt.

Fallback decision: the `apple-codesign` crate (in-process signing) is not
needed and is not adopted. It would add a macOS-only dependency and a Rust-to-
Swift seam for a task `/usr/bin/codesign` already does. It remains the fallback
if a future macOS release blocks a sandboxed `Process` launch of `codesign`.
