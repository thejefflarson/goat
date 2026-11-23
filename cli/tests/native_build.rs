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
    build_native_with(dir, name, source, &[])
}

fn build_native_with(
    dir: &Path,
    name: &str,
    source: &str,
    flags: &[&str],
) -> Result<PathBuf, String> {
    let program = dir.join(format!("{name}.goat"));
    std::fs::write(&program, source).unwrap();
    let exe = dir.join(name);
    let out = Command::new(GOAT)
        .args(["build", "--native"])
        .args(flags)
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

#[cfg(not(target_os = "macos"))]
#[test]
fn an_interactive_program_is_refused_where_there_is_no_window_host() {
    needs_clang!();
    let dir = tempfile::tempdir().unwrap();
    let source = std::fs::read_to_string("../examples/interactive.goat").unwrap();
    let error = build_native(dir.path(), "interactive", &source).unwrap_err();
    assert!(
        error.contains("does not support interactive programs") && error.contains("macOS"),
        "{error}"
    );
}

#[test]
fn build_native_reads_the_vocabulary_from_the_program_and_obeys_the_flags() {
    let dir = tempfile::tempdir().unwrap();
    let both =
        "forward(10)\nupdate = program(m, e) do match e do Frame(d) then m else m done done\n";
    let ambiguous = build_native(dir.path(), "both", both).unwrap_err();
    assert!(
        ambiguous.contains("`forward`") && ambiguous.contains("`Frame`"),
        "{ambiguous}"
    );
    assert!(ambiguous.contains("--turtle or --canvas"), "{ambiguous}");

    let canvas = std::fs::read_to_string("../examples/canvas/sky.goat").unwrap();
    let forced = build_native_with(dir.path(), "sky", &canvas, &["--turtle"]).unwrap_err();
    assert!(forced.contains("error(s)"), "{forced}");
}

/// The AppKit window host (macOS only). Every test runs the binary with
/// `--headless`, which needs no display: the program runs and its pictures are
/// decoded as the window would draw them.
#[cfg(target_os = "macos")]
mod window_host {
    use super::*;

    const BOUNCE: &str = include_str!("../../examples/canvas/bounce.goat");
    const CATCH: &str = include_str!("../../examples/canvas/catch.goat");

    fn canvas(dir: &Path, name: &str, source: &str) -> PathBuf {
        build_native(dir, name, source).unwrap_or_else(|e| panic!("{e}"))
    }

    /// The numbers of the first line of `picture` that starts with `shape`.
    fn numbers(picture: &str, shape: &str) -> Vec<f64> {
        let line = picture
            .lines()
            .find(|line| line.starts_with(shape))
            .unwrap_or_else(|| panic!("no {shape} in\n{picture}"));
        line.split_whitespace()
            .skip(1)
            .filter_map(|word| word.parse().ok())
            .collect()
    }

    fn headless(exe: &Path, args: &[&str]) -> Output {
        Command::new(exe)
            .arg("--headless")
            .args(args)
            .output()
            .unwrap()
    }

    #[test]
    fn a_canvas_program_links_and_animates() {
        needs_clang!();
        let dir = tempfile::tempdir().unwrap();
        let exe = canvas(dir.path(), "bounce", BOUNCE);
        let ran = headless(&exe, &["20"]);
        assert!(
            ran.status.success(),
            "{}",
            String::from_utf8_lossy(&ran.stderr)
        );
        let picture = String::from_utf8_lossy(&ran.stdout);
        let ball = numbers(&picture, "circle");
        assert!(
            ball[0] > 40.0 && ball[0] < 380.0,
            "the ball moved from x = 40: {ball:?}"
        );
        assert_eq!(numbers(&picture, "rect"), [0.0, 290.0, 400.0, 10.0]);
    }

    #[test]
    fn keys_reach_the_program() {
        needs_clang!();
        let dir = tempfile::tempdir().unwrap();
        let exe = canvas(dir.path(), "catch", CATCH);
        let still = headless(&exe, &["2"]);
        let moved = headless(&exe, &["2", "--key", "ArrowLeft", "--key", "ArrowLeft"]);
        assert_eq!(
            numbers(&String::from_utf8_lossy(&still.stdout), "rect")[0],
            160.0
        );
        assert_eq!(
            numbers(&String::from_utf8_lossy(&moved.stdout), "rect")[0],
            120.0
        );
    }

    #[test]
    fn a_trap_shows_goats_message() {
        needs_clang!();
        let dir = tempfile::tempdir().unwrap();
        let source = "init = {n: 0}\n\
                      update = program(model, event) do\n  match event do\n    Frame(dt) then {n: 5 // 0}\n    else model\n  done\ndone\n\
                      draw = program(model) do [Dot({x: 10, y: 10, r: 5, fill: \"red\"})] done\n";
        let exe = canvas(dir.path(), "traps", source);
        let ran = headless(&exe, &["50"]);
        assert_eq!(ran.status.code(), Some(1));
        let stderr = String::from_utf8_lossy(&ran.stderr);
        assert!(
            stderr.contains("trap: 4:") && stderr.contains("division by zero"),
            "{stderr}"
        );
    }

    #[test]
    fn a_runaway_update_is_stopped_by_the_watchdog() {
        needs_clang!();
        let dir = tempfile::tempdir().unwrap();
        let source = "init = {n: 0}\n\
                      spin = program(n, model) do if n < 0 then model else spin(n + 1, model) done done\n\
                      update = program(model, event) do\n  match event do\n    Frame(dt) then spin(0, model)\n    else model\n  done\ndone\n\
                      draw = program(model) do [Dot({x: 10, y: 10, r: 5, fill: \"red\"})] done\n";
        let exe = canvas(dir.path(), "spins", source);
        let ran = Command::new(&exe)
            .args(["--headless", "50"])
            .env("GOAT_STUCK_MS", "300")
            .output()
            .unwrap();
        assert_eq!(ran.status.code(), Some(1));
        let stderr = String::from_utf8_lossy(&ran.stderr);
        assert!(stderr.contains("your program got stuck"), "{stderr}");
    }

    #[test]
    fn a_turtle_interactive_program_links_too() {
        needs_clang!();
        let dir = tempfile::tempdir().unwrap();
        let source = std::fs::read_to_string("../examples/interactive.goat").unwrap();
        let exe =
            build_native(dir.path(), "interactive", &source).unwrap_or_else(|e| panic!("{e}"));
        let ran = headless(&exe, &["3", "--key", "ArrowRight"]);
        assert!(
            ran.status.success(),
            "{}",
            String::from_utf8_lossy(&ran.stderr)
        );
        assert_eq!(
            numbers(&String::from_utf8_lossy(&ran.stdout), "line"),
            [0.0, 0.0, 10.0, 0.0]
        );
    }
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
