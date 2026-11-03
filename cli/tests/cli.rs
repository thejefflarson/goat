//! End-to-end tests of the `goat` binary: source to wasm to wasmtime.

use std::fs;
use std::process::{Command, Output};

fn goat(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_goat"))
        .args(args)
        .output()
        .expect("run goat")
}

fn run_source(name: &str, source: &str) -> Output {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = dir.path().join(name);
    fs::write(&path, source).unwrap();
    goat(&["run", path.to_str().unwrap()])
}

fn stdout_of(source: &str) -> String {
    let out = run_source("p.goat", source);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

#[test]
fn runs_the_examples() {
    let fib = goat(&[
        "run",
        concat!(env!("CARGO_MANIFEST_DIR"), "/../examples/fib.goat"),
    ]);
    assert_eq!(String::from_utf8(fib.stdout).unwrap(), "55\n");
    let higher = goat(&[
        "run",
        concat!(env!("CARGO_MANIFEST_DIR"), "/../examples/higher_order.goat"),
    ]);
    assert_eq!(String::from_utf8(higher.stdout).unwrap(), "42\n");
    let records = goat(&[
        "run",
        concat!(env!("CARGO_MANIFEST_DIR"), "/../examples/records.goat"),
    ]);
    assert_eq!(String::from_utf8(records.stdout).unwrap(), "7\n");
}

#[test]
fn number_formatting_matches_the_old_runtime() {
    assert_eq!(stdout_of("1 + 2 * 3"), "7");
    assert_eq!(stdout_of("1000000"), "1000000");
    assert_eq!(stdout_of("10 / 4"), "2.5");
    assert_eq!(stdout_of("0.1 + 0.2"), "0.3");
    assert_eq!(stdout_of("1 < 2"), "true");
}

#[test]
fn a_trap_exits_non_zero() {
    let out = run_source("trap.goat", "f = program(n) do f(n) + 1 done\n\nf(1)");
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("trap"));
}

#[test]
fn type_errors_exit_non_zero() {
    let out = run_source("bad.goat", "1 + true");
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("error"));
}

#[test]
fn build_writes_a_wasm_module() {
    let dir = tempfile::tempdir().expect("temp dir");
    let src = dir.path().join("f.goat");
    let out = dir.path().join("f.wasm");
    fs::write(&src, "1 + 2").unwrap();
    let result = goat(&["build", src.to_str().unwrap(), "-o", out.to_str().unwrap()]);
    assert!(result.status.success());
    assert_eq!(&fs::read(&out).unwrap()[..4], b"\0asm");
}
