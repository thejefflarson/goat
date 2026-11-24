//! The AppKit host's Swift (ADR 0042): its frame decoder, colors and painter
//! compile and pass their own checks (`native/appkit/tests/main.swift`). macOS
//! only; the window itself is covered by `goat build --native`'s tests, which
//! run the linked binary headless.

#![cfg(target_os = "macos")]

use std::path::Path;
use std::process::Command;

const PURE: [&str; 3] = ["Color.swift", "Frame.swift", "Painter.swift"];

#[test]
fn the_frame_decoder_colors_and_painter_pass_their_swift_tests() {
    let swiftc = std::env::var("GOAT_SWIFTC").unwrap_or_else(|_| "swiftc".to_string());
    if !Command::new(&swiftc)
        .arg("--version")
        .output()
        .is_ok_and(|out| out.status.success())
    {
        eprintln!("skipped: swiftc is not installed");
        return;
    }
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let appkit = manifest.join("appkit");
    let canvas = manifest.join("../hosts/apple/GoatKit/Sources/GoatCanvas");
    let dir = tempfile::tempdir().unwrap();
    let exe = dir.path().join("frame-tests");
    let built = Command::new(&swiftc)
        .args([
            "-swift-version",
            "5",
            "-warnings-as-errors",
            "-module-name",
            "Tests",
        ])
        .args(PURE.map(|file| canvas.join(file)))
        .arg(appkit.join("tests/main.swift"))
        .arg("-o")
        .arg(&exe)
        .output()
        .unwrap();
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let ran = Command::new(&exe).output().unwrap();
    assert!(
        ran.status.success(),
        "{}",
        String::from_utf8_lossy(&ran.stderr)
    );
}
