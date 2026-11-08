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
