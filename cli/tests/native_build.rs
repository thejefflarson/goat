//! `goat build --native`: a program becomes a standalone executable whose output
//! matches `goat run`'s. Skips when clang is not installed.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const GOAT: &str = env!("CARGO_BIN_EXE_goat");
const SPIRAL: &str = "../examples/spiral.goat";

fn goat(args: &[&str]) -> Output {
    Command::new(GOAT).args(args).output().expect("run goat")
}

fn clang_present() -> bool {
    let named = std::env::var("GOAT_CLANG").unwrap_or_else(|_| "clang".to_string());
    Command::new(named)
        .arg("--version")
        .output()
        .is_ok_and(|out| out.status.success())
}

/// The profile directory the `goat` binary sits in, where `libgoat_native.a`
/// belongs. Cargo builds the staticlib only for its own package, so a test run
/// of this crate builds it first.
fn static_lib() -> PathBuf {
    let profile_dir = Path::new(GOAT).parent().expect("target profile directory");
    let lib = profile_dir.join("libgoat_native.a");
    if !lib.exists() {
        let mut build = Command::new(std::env::var("CARGO").unwrap_or_else(|_| "cargo".into()));
        build
            .args(["build", "-p", "goat_native", "--target-dir"])
            .arg(profile_dir.parent().expect("target directory"));
        if profile_dir.ends_with("release") {
            build.arg("--release");
        }
        assert!(build.status().expect("run cargo").success());
    }
    lib
}

fn build_native(dir: &Path, name: &str, source: &str) -> Result<PathBuf, String> {
    let program = dir.join(format!("{name}.goat"));
    std::fs::write(&program, source).unwrap();
    let exe = dir.join(name);
    let out = Command::new(GOAT)
        .args(["build", "--native"])
        .arg(&program)
        .arg("-o")
        .arg(&exe)
        .env("GOAT_NATIVE_LIB", static_lib())
        .output()
        .expect("run goat");
    if out.status.success() {
        Ok(exe)
    } else {
        Err(String::from_utf8_lossy(&out.stderr).into_owned())
    }
}

macro_rules! needs_clang {
    () => {
        if !clang_present() {
            eprintln!("skipped: clang is not installed");
            return;
        }
    };
}

#[test]
fn the_spiral_binary_writes_the_svg_goat_run_writes() {
    needs_clang!();
    let dir = tempfile::tempdir().unwrap();
    let source = std::fs::read_to_string(SPIRAL).unwrap();
    let exe = build_native(dir.path(), "spiral", &source).unwrap_or_else(|e| panic!("{e}"));
    let (native_svg, wasm_svg) = (dir.path().join("native.svg"), dir.path().join("wasm.svg"));
    let ran = Command::new(&exe)
        .arg("-o")
        .arg(&native_svg)
        .output()
        .unwrap();
    assert!(
        ran.status.success(),
        "{}",
        String::from_utf8_lossy(&ran.stderr)
    );
    let reference = goat(&["run", SPIRAL, "-o", wasm_svg.to_str().unwrap()]);
    assert!(reference.status.success());
    let (native, wasm) = (
        std::fs::read(&native_svg).unwrap(),
        std::fs::read(&wasm_svg).unwrap(),
    );
    assert!(!native.is_empty());
    assert_eq!(native, wasm);
}

#[test]
fn a_binary_prints_to_stdout() {
    needs_clang!();
    let dir = tempfile::tempdir().unwrap();
    let source = "print(\"hello\");\nprint(2.5);\nprint(true)";
    let exe = build_native(dir.path(), "hello", source).unwrap_or_else(|e| panic!("{e}"));
    let ran = Command::new(exe).output().unwrap();
    assert!(ran.status.success());
    assert_eq!(String::from_utf8_lossy(&ran.stdout), "hello\n2.5\ntrue\n");
}

#[test]
fn a_trap_prints_goat_runs_message_and_exits_non_zero() {
    needs_clang!();
    let dir = tempfile::tempdir().unwrap();
    let source = "print(1);\nprint(5 // 0)";
    let exe = build_native(dir.path(), "trap", source).unwrap_or_else(|e| panic!("{e}"));
    let native = Command::new(exe).output().unwrap();
    let reference = goat(&["run", dir.path().join("trap.goat").to_str().unwrap()]);
    assert!(!native.status.success());
    assert_eq!(native.stdout, reference.stdout);
    assert_eq!(native.stderr, reference.stderr);
    assert!(String::from_utf8_lossy(&native.stderr).contains("trap: 2:7: division by zero"));
}

#[test]
fn an_interactive_program_is_refused() {
    needs_clang!();
    let dir = tempfile::tempdir().unwrap();
    let source = std::fs::read_to_string("../examples/interactive.goat").unwrap();
    let error = build_native(dir.path(), "interactive", &source).unwrap_err();
    assert!(
        error.contains("does not support interactive programs"),
        "{error}"
    );
}

#[test]
fn a_clang_that_does_not_run_is_named() {
    let dir = tempfile::tempdir().unwrap();
    let program = dir.path().join("p.goat");
    std::fs::write(&program, "print(1)").unwrap();
    let out = Command::new(GOAT)
        .args(["build", "--native"])
        .arg(&program)
        .env("GOAT_CLANG", "no-such-clang")
        .env("GOAT_NATIVE_LIB", static_lib())
        .output()
        .unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("GOAT_CLANG is no-such-clang"));
}

#[test]
fn a_missing_clang_says_how_to_install_it() {
    let dir = tempfile::tempdir().unwrap();
    let program = dir.path().join("p.goat");
    std::fs::write(&program, "print(1)").unwrap();
    let out = Command::new(GOAT)
        .args(["build", "--native"])
        .arg(&program)
        .env("PATH", "")
        .env_remove("GOAT_CLANG")
        .output()
        .unwrap();
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    let fix = if cfg!(target_os = "macos") {
        "xcode-select --install"
    } else {
        "install clang"
    };
    assert!(
        stderr.contains("needs clang") && stderr.contains(fix),
        "{stderr}"
    );
}
