# goat for macOS and iOS

A SwiftUI app with two targets (`Goat-macOS`, `Goat-iOS`) sharing one codebase.
The editor, Run control, file open/save and problem list are native. A
`WKWebView` is only the compile-and-draw engine: it loads `web/embed.html`
(a canvas and `goat_web.wasm`, no editor UI) from the app bundle, offline.

```
hosts/apple/
  App/GoatApp.swift      @main; a DocumentGroup of .goat files (native open/save, Files on iOS)
  GoatKit/               shared code; a SwiftPM package (for `swift test`) and, via project.yml,
                         a framework per platform
    Engine.swift           owns the web view; run/stop in, EngineMessages out
    EngineMessage.swift    the web view -> native protocol (JSON strings)
    AssetSchemeHandler.swift, AssetPath.swift   serves Resources/web over goat-app://
    CodeEditor.swift       NSTextView / UITextView with smart quotes off, error highlights
    EditorScreen.swift     editor + canvas + problems panel + toolbar
  project.yml            XcodeGen spec; the .xcodeproj is generated, not committed
  scripts/stage-web.sh   builds goat_web.wasm + the embed page into Resources/web
```

## Build

```sh
hosts/apple/scripts/stage-web.sh          # cargo + npm; fills hosts/apple/Resources/web
cd hosts/apple && xcodegen generate       # brew install xcodegen
xcodebuild -project Goat.xcodeproj -scheme Goat-macOS -destination 'platform=macOS' build
xcodebuild -project Goat.xcodeproj -scheme Goat-iOS -destination 'generic/platform=iOS' CODE_SIGNING_ALLOWED=NO build
swift test --package-path GoatKit
```

`scripts/check-doc-types.sh` (run in CI after `xcodegen generate`) fails if the
document type, the exported UTI and `UTType.goatSource` stop naming the same identifier.

## Create Document on the iOS simulator

Tapping **Create Document** in the iOS 26.5 simulator intermittently shows "Unable to
Import Document (com.apple.DocumentManager error 1)". The type declarations are not the
cause: the UTI resolves and conforms to `public.plain-text`, existing `.goat` files open
with their contents, and an app whose document type is stock `public.plain-text` fails the
same way. On a failure the file is still written; the Files service then cannot resolve a
bookmark for the item it just moved (`NSFileProviderErrorDomain` -1005, "NonExistentItemIdentifier").
Open the file from the browser instead. Not reproduced on a device.

## The bridge

- Native to web: `Engine.run(source:)` calls `window.goat.run(source)` through
  `callAsyncJavaScript` with the source as an argument, never spliced into script
  text. `stop()` calls `window.goat.stop()`.
- Web to native: `web/embed-main.ts` posts `JSON.stringify(EngineMessage)` to the
  `goat` script message handler: `ready`, `diagnostics` (line, column, length,
  message), `output` (printed lines), `state` (`running`, `finished`, `failed`).
  `EngineMessage.decode` drops anything oversized or unrecognized, and the handler
  only accepts messages from the bundled page's main frame.
- The page loads through a private `goat-app://app/` URL scheme (file URLs would
  block module scripts and the wasm fetch). The web view cancels every other
  navigation and the page's CSP is `default-src 'none'`.

## Stopping a runaway program (ADR 0021)

goat runs on the web view's main thread, which nothing on the page can interrupt,
so the native app owns preemption (`Watchdog.swift`, `Engine.swift`):

1. `web/beat.ts` posts a `beat` before and after every call into goat. The count
   is odd while goat runs and even while the page is idle; `call` says which
   budget applies (`frame` for `setup`/`update`/`draw`, `once` for a run-once program).
2. `WatchdogTimer` polls only while a call is open. A call open past its budget
   (1 s per frame, 10 s run-once, the same numbers as the browser supervisor)
   makes `Engine` drop the web view, build a new one on a non-persistent data
   store, and show "your program got stuck" / "your program was stopped". Idle
   programs are never stopped. The program does not restart on its own; Run does.
3. Nothing else bounds a program: goat modules carry no fuel. The page only runs
   goat on its own thread when the `goat` message handler exists, which is how it
   knows this watchdog is listening; a page with neither that nor cross-origin
   isolation refuses to run.

Untested without a Mac at runtime: that releasing a web view kills a content
process stuck in wasm, and that a `beat` posted just before the page blocks still
reaches the app. If the second fails the watchdog never fires and a runaway
program hangs the web view.

`crossOriginIsolated` (COOP/COEP on `AssetSchemeHandler`, so the browser's worker
supervisor could run here) is not used. Whether WebKit isolates a custom-scheme
page, and serves a module worker and wasm from one, is unverified; try it on a Mac
before relying on it. The page picks the worker path by itself when isolated.

## App Store 2.5.2

The app never downloads or generates code outside what the user types: source is
always visible and editable in the native editor, including while a program runs,
and nothing exports a program as a separate app.

Game-style programs read keys from the canvas, so click the picture before using
the arrow keys.

## Open decisions

Bundle id `com.thejefflarson.goat`, minimum macOS 13 / iOS 16, unsigned builds.
Team, signing and entitlements beyond the macOS sandbox (user-selected files,
no network) are not set.
