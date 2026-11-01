//! End-to-end backend tests: type-check, compile to an object, link against the
//! C runtime with `cc`, run the executable, and check what it prints. Requires
//! a C compiler on PATH (set `CC` to override), which CI and dev machines have.

use std::process::Command;
use std::sync::atomic::{AtomicU32, Ordering};
use std::{env, fs};

const RUNTIME_C: &str = r#"
#include <stdio.h>
extern void goat_entry(void);
void goat_print_number(double x) { printf("%g\n", x); }
void goat_print_bool(long b) { printf("%s\n", b ? "true" : "false"); }
int main(void) { goat_entry(); return 0; }
"#;

/// Compile and run `src`, returning its stdout with the trailing newline
/// trimmed.
fn run(src: &str) -> String {
    let checked = goat_compiler::check(src).expect("program type-checks");
    let object = goat_compiler::compile(&checked).expect("program compiles");

    static COUNTER: AtomicU32 = AtomicU32::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = env::temp_dir().join(format!("goat-e2e-{}-{n}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let obj = dir.join("p.o");
    let rt = dir.join("rt.c");
    let exe = dir.join("p");
    fs::write(&obj, &object).unwrap();
    fs::write(&rt, RUNTIME_C).unwrap();

    let cc = env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let status = Command::new(&cc)
        .arg(&obj)
        .arg(&rt)
        .arg("-o")
        .arg(&exe)
        .status()
        .expect("invoke cc");
    assert!(status.success(), "linking failed");

    let output = Command::new(&exe).output().expect("run program");
    let _ = fs::remove_dir_all(&dir);
    String::from_utf8(output.stdout).unwrap().trim().to_string()
}

#[test]
fn arithmetic() {
    assert_eq!(run("1 + 2 * 3"), "7");
    assert_eq!(run("(1 + 2) * 3"), "9");
    assert_eq!(run("10 / 4"), "2.5");
}

#[test]
fn booleans() {
    assert_eq!(run("1 < 2"), "true");
    assert_eq!(run("3 < 2"), "false");
    assert_eq!(run("x = 5  x < 10"), "true");
}

#[test]
fn let_bindings() {
    assert_eq!(run("a = 2  b = 3  a + b"), "5");
}

#[test]
fn functions_and_recursion() {
    assert_eq!(run("add = program(a, b) do a + b done  add(20, 22)"), "42");
    let fib = "fib = program(n) do if n < 2 then n else fib(n - 1) + fib(n - 2) done done fib(10)";
    assert_eq!(run(fib), "55");
}

#[test]
fn higher_order_functions() {
    let src = "apply = program(f, x) do f(x) done \
               double = program(n) do n * 2 done \
               apply(double, 21)";
    assert_eq!(run(src), "42");
}

#[test]
fn identifier_may_start_with_a_keyword() {
    // `double` begins with the keyword `do`; this must still be a valid name.
    assert_eq!(run("double = program(n) do n * 2 done  double(21)"), "42");
}
