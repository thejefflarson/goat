# goat for macOS and iOS

A SwiftUI app with two targets (`Goat-macOS`, `Goat-iOS`) sharing one codebase.
The editor, Run control, file open/save, problem list and canvas are native. Programs run in
this process on the goat engine (`engine/`, ADR 0043): it compiles to the Pulley interpreter,
so the app needs no JIT entitlement, and its frames are drawn with Core Graphics by the same
`GoatCanvas` renderer `goat build --native` embeds.

```
hosts/apple/
  App/GoatApp.swift      @main; a DocumentGroup of .goat files on macOS, the document browser on iOS
  App/DocumentBrowser.swift   iOS only: UIDocumentBrowserViewController that creates into local Documents
  GoatKit/               shared code; a SwiftPM package (for `swift test`) and, via project.yml,
                         a framework per platform
    (Sources/GoatCanvas: Frame, Painter and Color, the one renderer; `goat build --native`
     embeds the same files via goat_native::appkit)
    Engine.swift           owns the C engine; run/stop/key/pointer in, EngineMessages and frames out
    EngineMessage.swift    the engine -> app control messages (JSON), including `reloaded`
    FrameSlot.swift        the latest picture, handed from the engine's thread to the canvas view
    CanvasHostView.swift   NSView / UIView that draws the frames and forwards keys and pointer
    CodeEditor.swift       NSTextView / UITextView with smart quotes off, error highlights
    EditorScreen.swift     editor + canvas + problems panel + toolbar
  Player/PlayerApp.swift  GoatPlayer-macOS: the engine and canvas without the editor, for exported apps
                         (also carries AppIcon.icns from native/appkit, the goat head)
  project.yml            XcodeGen spec; the .xcodeproj is generated, not committed
  scripts/stage-engine.sh builds engine/ (goat_apple) into Frameworks/GoatEngine.xcframework
  engine/                the native goat engine behind include/goat_engine.h (ADR 0043)
```

## Build

```sh
hosts/apple/scripts/stage-engine.sh       # cargo, 4 Apple targets; builds Frameworks/GoatEngine.xcframework
cd hosts/apple && xcodegen generate       # brew install xcodegen
xcodebuild -project Goat.xcodeproj -scheme Goat-macOS -destination 'platform=macOS' build
xcodebuild -project Goat.xcodeproj -scheme Goat-iOS -destination 'generic/platform=iOS' CODE_SIGNING_ALLOWED=NO build
# ^ CODE_SIGNING_ALLOWED=NO is valid for simulator and CI only; it must not be used for real-device or distribution builds.
swift test --package-path GoatKit
# the same tests plus the engine tests inside the sandbox; ad-hoc signing makes the entitlements apply
xcodebuild test -project Goat.xcodeproj -scheme GoatKitTests-macOS -destination 'platform=macOS' \
  CODE_SIGN_IDENTITY=- CODE_SIGNING_ALLOWED=YES ENABLE_USER_SCRIPT_SANDBOXING=NO
```

`stage-engine.sh` builds `goat_apple` in release for `aarch64`/`x86_64-apple-darwin` (joined with
`lipo` into one macOS slice), `aarch64-apple-ios` and `aarch64-apple-ios-sim`, with
`MACOSX_DEPLOYMENT_TARGET=13.0` and `IPHONEOS_DEPLOYMENT_TARGET=17.0`. Install the targets first
(`rustup target add` each). The iOS simulator slice is arm64 only. The xcframework's headers carry a
module map, so Swift writes `import GoatEngine`. `check-staged.sh` fails the app builds when the
xcframework is missing or older than `engine/src`, `engine/include` or `engine/Cargo.toml` (a change
in the compiler crates it depends on is not detected; rerun the script). SwiftPM has no
`GoatEngine` module, so `swift test` builds and tests only what does not need the engine
(`Engine.swift` and `EditorScreen.swift` are compiled out); everything that runs the engine is
tested under `xcodebuild test`.

`NativeEngineTests` drives the real `Engine`: the starter program's pixels land on the
canvas view, a stuck program shows its message and Run works again, and a second Run
keeps the model (`reloaded kept`). `EngineLinkTests` checks the raw C seam. Under
`xcodebuild test` they run inside `GoatTestHost-macOS`, a windowless app with `Goat-macOS`'s
sandbox entitlements. An unsigned build is unsandboxed, so it cannot catch a missing one.

`UITests/EditorSmokeTests` (scheme `Goat-iOS`, `xcodebuild test` against an iOS simulator)
launches the Debug app with `-goat-ui-smoke`, which opens the editor on the starter program
without the document browser, taps Run, and waits for the canvas (identifier `canvas`) to
report the value `finished`.

`PlayModeTests` (same file) taps Play on iOS, expects the canvas to fill the window with the editor
gone, and leaves by the Close button and by swiping down. Play runs the program and shows only its
canvas on black; leaving keeps the program running, so the editor shows the same picture. macOS has
no Play button (its canvas already sits beside the editor).

`scripts/check-doc-types.sh` (run in CI after `xcodegen generate`) fails if the
document type, the exported UTI and `UTType.goatSource` stop naming the same identifier.

## Signing

Builds are unsigned unless you opt in. `project.yml` includes `Local.xcconfig` in every
configuration, and `xcodegen generate` copies `Local.xcconfig.example` (empty team) to
`Local.xcconfig` when it is missing, so a fresh checkout and CI stay unsigned.

To sign with your own Apple Development team, set `DEVELOPMENT_TEAM` in `Local.xcconfig`
(gitignored, so the Team ID never reaches this public repo) and regenerate the project.
The Team ID is the **OU** of your Apple Development certificate, *not* the value shown in
parentheses in the certificate's name — read it with
`security find-certificate -c "Apple Development" -p | openssl x509 -noout -subject -nameopt multiline | grep organizationalUnit`.
Automatic signing then needs your Apple ID in Xcode (Settings > Accounts), and for a device
build a registered device; headless `xcodebuild` also needs `-allowProvisioningUpdates` the
first time. Pass `CODE_SIGNING_ALLOWED=NO` to build unsigned while a team is set.

## Creating documents on iOS

`DocumentGroup` cannot choose where a new document goes, and the browser it wraps
moves the new file through the Files import step. That step failed with
`com.apple.DocumentManager` error 1 (the Files service could not resolve a bookmark
for the item it had just moved), and with iCloud Drive as the default location it
stalled on unsynced items and left the browser ignoring **+**.

On iOS the app therefore hosts its own `UIDocumentBrowserViewController`
(`App/DocumentBrowser.swift`). **Create Document** writes `Untitled.goat` (or
`Untitled 2.goat`, and so on) into the app's local Documents folder, "On My iPhone",
through `LocalDocuments.create`, and hands the URL back with import mode `.none`, so
the browser opens the file where it is. Nothing touches ubiquity, so creating does
not wait on iCloud. A `UIDocument` subclass loads and autosaves the text, and the
editor is presented over the browser with a Done button. macOS keeps `DocumentGroup`.

The browser still opens documents in place (`LSSupportsOpeningDocumentsInPlace`,
guarded by `check-doc-types.sh`), so files picked from iCloud Drive or other
providers are edited where they live.

`UITests/EditorSmokeTests` has a create test (`CreateDocumentTests`) that taps
**Create Document** in the real browser, without `-goat-ui-smoke`, and waits for the
editor.

## The engine seam

`Engine` owns a `goat_engine` (`engine/include/goat_engine.h`) and speaks to it:

- App to engine: `run(source:)`, `stop()`, `key(_:down:)` and `pointer(_:x:y:)`, none of which
  waits for the program. A second `run` while a program is running is a reload (ADR 0035).
- Engine to app: control messages as JSON (`EngineMessage`: `ready`, `diagnostics`, `output`,
  `state`, `reloaded`) and frames, on a thread the engine owns. Control messages queue in order
  and are handled on the main actor. A frame is decoded where it arrives and left in a
  `FrameSlot`, so a frame the canvas never got to draw is replaced by a newer one.
- `reloaded` shows under the problems panel: "Reloaded: your program's data was kept." or
  "...started over because ...", with the engine's reason.
- Budgets (1 s a frame, 10 s for setup, a reload or a run-once program) are the engine's, not
  the app's: a program over budget comes back as a `failed` state, shown in the problems panel,
  and the next Run starts clean (ADR 0021).
- Releasing the `Engine` frees the C engine, which waits for a callback in flight; callbacks
  never wait on the main actor, so that cannot deadlock.

The canvas draws the 400 by 300 picture centered at its own proportions; the keyboard goes to it
after a click or tap, with key names as `KeyboardEvent.key` has them. The canvas reports the
engine's phase as its accessibility value (`finished` once a run-once program drew).

## Running on a device

1. `rustup target add aarch64-apple-ios aarch64-apple-ios-sim aarch64-apple-darwin x86_64-apple-darwin`
   and `brew install xcodegen`.
2. `hosts/apple/scripts/stage-engine.sh` (a few minutes; it builds four slices).
3. `cp hosts/apple/Local.xcconfig.example hosts/apple/Local.xcconfig` and set
   `DEVELOPMENT_TEAM` in it (see Signing). The file is gitignored.
4. `cd hosts/apple && xcodegen generate && open Goat.xcodeproj`.
5. Pick the `Goat-iOS` scheme and your phone, then Run (Debug builds are fine for a frame-time
   number, but profile with Release for a fair one: Product > Scheme > Edit Scheme > Run >
   Build Configuration). The first launch needs the developer certificate trusted on the phone
   (Settings > General > VPN & Device Management) and Developer Mode on.

## Export App…

On macOS, File > Export App… saves the program as `Name.app`. It is enabled once the program
has run without problems and is unchanged since. `GoatPlayer.app` is built beside Goat and
embedded in Goat's `Contents/Resources`; the export copies it, writes `program.goat` to its
Resources, sets `CFBundleName`, `CFBundleDisplayName` and `CFBundleIdentifier`
(`local.goat.<slug>`; `CFBundleExecutable` stays `GoatPlayer`), and signs the copy ad hoc,
last, because the signature seals every file. The player reads `program.goat` at launch and
titles its window with the app's name; a program error shows as one line under the canvas.
Like `goat build --native`, an export replaces an app already at that path only if its bundle
identifier starts with `local.goat.`, and refuses anything else. The save panel's security
scope stays open until `codesign` exits.

The exported app carries the same default icon as `goat build --native` bundles
(`native/appkit/AppIcon.icns`, named by `CFBundleIconFile` in `GoatPlayer`'s Info.plist).

File > Export Native App… appears when the Command Line Tools are installed
(`/Library/Developer/CommandLineTools/usr/bin/clang`). It does not build anything: the sandbox
forbids the app from running `xcrun`, `clang` or a `goat` binary, and ADR 0043 keeps the sandbox,
so the item explains this and shows the command to run in Terminal:
`goat build --native Name.goat -o Name.app`. A one-click native export would need a compiler
helper outside the sandbox (possible only with Developer ID distribution) or dropping the
sandbox; both wait on the distribution decision (ADR 0043).

## Play mode on iOS

The toolbar's Play button runs the program and replaces the editor with the canvas alone, edge to
edge on black, with the status bar and home indicator hidden. Touches reach the program. A Close
button appears on any touch and fades after three seconds; swiping down also leaves. Leaving does
not stop the program, so the editor shows the same picture and Stop is one tap away. macOS has no
Play button: its canvas already sits beside the editor.

## App Store 2.5.2

Guideline 2.5.2 forbids an app from downloading or executing code that changes the app's
features. Goat runs only the program the user typed: source is always visible and editable in the
native editor, including while a program runs, and the engine never fetches anything (the apps
have no network entitlement). Programs are interpreted in this process (Pulley), so the apps need
no JIT entitlement. iOS has no export. On macOS, Export App… copies a player that runs the same
program the user wrote, to a file the user chose.

Game-style programs read keys from the canvas, so click the picture before using
the arrow keys.

## Open decisions

Bundle id `com.thejefflarson.goat`, minimum macOS 13 / iOS 17, unsigned by default.
Distribution signing is not set up. The macOS sandbox carries only app-sandbox and
user-selected read-write files: the engine interprets (Pulley), so no JIT entitlement, and it
never touches the network, so no network entitlement. Hardened Runtime is on for notarization.
