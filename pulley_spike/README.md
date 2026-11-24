# Pulley spike

Times every `examples/canvas` program, per frame (one `update` plus one `draw`),
on wasmtime's Pulley interpreter or on its default Cranelift backend. The
results and the go or no-go are in the
[ADR 0043 amendment](../docs/adr/0043-apple-apps-run-goat-in-process-and-export-apps.md).

This crate is outside the main workspace, so the workspace gates and the editor
image build context ignore it.

## On the desktop

```sh
cargo run --release --example bench pulley 600      # 600 frames per program
cargo run --release --example bench cranelift 600
```

Columns are milliseconds: `load_ms` compiles and instantiates the program; the
other three are the p50, p95 and max of one update plus one draw. The first 30
frames are warm-up and dropped. The program's `.events` script plays first and
`Frame 16` events pad it to the frame count.

## Build the static library for iOS

```sh
rustup target add aarch64-apple-ios aarch64-apple-ios-sim
export IPHONEOS_DEPLOYMENT_TARGET=17.0        # match the Xcode app's target
cargo build --release --target aarch64-apple-ios       # a real iPhone
cargo build --release --target aarch64-apple-ios-sim   # the simulator
```

The archives are `target/<triple>/release/libgoat_pulley_spike.a`.

## The device step (the owner runs this)

The number the go or no-go waits for is the iPhone's p95 per program: **go if
every program's p95 is under 8 ms.**

1. In Xcode, make a new iOS App (SwiftUI, Swift), named `PulleyBench`. Set its
   minimum deployment target to 17.0 (the same as `IPHONEOS_DEPLOYMENT_TARGET`).
2. Replace the generated `PulleyBenchApp.swift` (and delete `ContentView.swift`)
   with `ios/PulleyBenchApp.swift` from this folder.
3. Add `ios/goat_pulley_bench.h` to the project. When Xcode offers to create a
   bridging header, accept; otherwise set Build Settings, Objective-C Bridging
   Header, to a header that has `#include "goat_pulley_bench.h"`.
4. Add `target/aarch64-apple-ios/release/libgoat_pulley_spike.a` under Build
   Phases, Link Binary With Libraries. Add `-lc++` to Other Linker Flags if the
   link asks for it. Under Build Settings, Library Search Paths is not needed
   when the archive is added by file.
5. Set the scheme's build configuration to **Release** (Product, Scheme, Edit
   Scheme, Run, Build Configuration) and run without the debugger attached
   (stop in Xcode, then launch the app from the home screen), because a
   debugger slows the interpreter.
6. Pick the iPhone, run, tap **Run the Pulley bench**, and copy the table. Run it
   twice and report the second run (the first one warms the caches). Note the
   phone model and iOS version, and whether Low Power Mode was on (turn it off).

The table has the same columns as the desktop run. The send-and-draw cost
includes copying the frame's scene commands, but not the Swift painter.
