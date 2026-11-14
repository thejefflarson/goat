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

/// A finite loop that takes far longer than a few milliseconds.
const LONG_LOOP: &str =
    "count = program(n) do if n >= 300000000 then n else count(n + 1) done done\nprint(count(0))";
const SPIN: &str = "spin = program(n) do if n < 0 then n else spin(n + 1) done done\nspin(0)";

fn run_with_args(source: &str, args: &[&str]) -> Output {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = dir.path().join("p.goat");
    fs::write(&path, source).unwrap();
    goat(&[&["run", path.to_str().unwrap()], args].concat())
}

#[test]
fn a_runaway_program_is_stopped_by_timeout() {
    let out = run_with_args(SPIN, &["--timeout", "200"]);
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("trap") && stderr.contains("looks stuck"),
        "{stderr}"
    );
}

#[test]
fn without_timeout_a_long_program_runs_to_the_end() {
    let bounded = run_with_args(LONG_LOOP, &["--timeout", "1"]);
    assert!(!bounded.status.success(), "the loop outlasts 1 ms");
    let unbounded = run_with_args(LONG_LOOP, &[]);
    assert!(
        unbounded.status.success(),
        "{}",
        String::from_utf8_lossy(&unbounded.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&unbounded.stdout).trim(),
        "300000000"
    );
}

#[test]
fn timeout_must_be_a_positive_number_of_milliseconds() {
    for bad in ["0", "soon", "-5"] {
        let out = run_with_args("1", &["--timeout", bad]);
        assert!(!out.status.success(), "{bad}");
        assert!(String::from_utf8_lossy(&out.stderr).contains("--timeout"));
    }
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
    let lists = goat(&[
        "run",
        concat!(env!("CARGO_MANIFEST_DIR"), "/../examples/lists.goat"),
    ]);
    assert_eq!(String::from_utf8(lists.stdout).unwrap(), "15\n");
}

#[test]
fn runs_the_whole_numbers_example() {
    let out = goat(&[
        "run",
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../examples/whole_numbers.goat"
        ),
    ]);
    assert!(out.status.success());
    assert_eq!(
        String::from_utf8(out.stdout).unwrap(),
        "3\n2\n-4\n3\n3\n-3\n-2\n-2\n0.5\n4\n50\n"
    );
}

#[test]
fn run_prints_an_int_past_2_to_the_53_exactly() {
    assert_eq!(
        stdout_of("print(9007199254740993);\nprint(9007199254740992 + 1);\nprint(0.5)"),
        "9007199254740993\n9007199254740993\n0.5"
    );
}

#[test]
fn a_division_by_zero_is_blamed_on_the_slash_slash() {
    let out = run_source("p.goat", "print(5 // 0)");
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("trap: 1:7: division by zero"), "{stderr}");
}

#[test]
fn runs_the_tags_example() {
    let out = goat(&[
        "run",
        concat!(env!("CARGO_MANIFEST_DIR"), "/../examples/tags.goat"),
    ]);
    assert!(out.status.success());
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "12\n9\n1\n");
}

#[test]
fn runs_the_groups_example() {
    let out = goat(&[
        "run",
        concat!(env!("CARGO_MANIFEST_DIR"), "/../examples/groups.goat"),
    ]);
    assert!(out.status.success());
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "25\n2\n");
}

#[test]
fn runs_the_literals_example() {
    let out = goat(&[
        "run",
        concat!(env!("CARGO_MANIFEST_DIR"), "/../examples/literals.goat"),
    ]);
    assert!(out.status.success());
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "2\n10\nno\n");
}

#[test]
fn a_missing_arm_in_a_grouped_match_is_a_spanned_error_on_stderr() {
    let out = run_source(
        "p.goat",
        "tag Light = Red | Green match Red do Red then 1 done",
    );
    assert!(!out.status.success());
    let stderr = String::from_utf8(out.stderr).unwrap();
    assert!(stderr.contains("doesn't handle `Green`"), "{stderr}");
    assert!(stderr.contains("^^^"), "span caret missing: {stderr}");
}

#[test]
fn a_helpers_failed_requirement_is_a_second_location_on_stderr() {
    let (_, stderr) = failure_of(
        "step = program(p) do q = p.moved(); q.x done\n\
         ball = {x: 1, moved: program(self) do self.x done}\n\
         step(ball)",
    );
    assert!(stderr.contains("3:1: type mismatch"), "{stderr}");
    assert!(stderr.contains("1:37: note: "), "{stderr}");
    assert!(
        stderr.contains("  step = program(p) do q = p.moved(); q.x done"),
        "{stderr}"
    );
}

#[test]
fn a_function_used_two_ways_is_two_notes_and_a_suggestion_on_stderr() {
    let (_, stderr) =
        failure_of("(program(f) do {a: f(1), b: f(true)} done)(program(x) do x done)");
    assert!(
        stderr.contains("1:29: `f` gets a Number here and a Bool there"),
        "{stderr}"
    );
    assert!(stderr.contains("f = program(x) do x done"), "{stderr}");
    assert!(
        stderr.contains("1:20: note: `f` gets a Number here"),
        "{stderr}"
    );
    assert!(
        stderr.contains("1:29: note: `f` gets a Bool here"),
        "{stderr}"
    );
}

#[test]
fn an_undeclared_tag_is_a_spanned_error_on_stderr() {
    let out = run_source("p.goat", "match Empty do Dwon then 1 else 0 done");
    assert!(!out.status.success());
    let stderr = String::from_utf8(out.stderr).unwrap();
    assert!(stderr.contains("unknown tag `Dwon`"), "{stderr}");
    assert!(stderr.contains("^^^^"), "span caret missing: {stderr}");
}

#[test]
fn runs_the_constraints_example() {
    let out = goat(&[
        "run",
        concat!(env!("CARGO_MANIFEST_DIR"), "/../examples/constraints.goat"),
    ]);
    assert!(out.status.success());
    assert_eq!(
        String::from_utf8(out.stdout).unwrap(),
        "{x: 21, y: 42}\n[true, true, false]\ntrue\n"
    );
}

#[test]
fn print_writes_a_line_per_call_before_the_result() {
    let src = "a = print(1)  b = print(\"two\")  c = print({n: [3]})  4";
    assert_eq!(stdout_of(src), "1\ntwo\n{n: [3]}\n4");
}

#[test]
fn comparing_functions_exits_non_zero_and_says_why() {
    let out = run_source("bad.goat", "f = program(x) do x done  f == f");
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("can't compare functions with `==`"),
        "{stderr}"
    );
}

#[test]
fn arithmetic_on_a_non_numeric_record_exits_non_zero_and_says_why() {
    let out = run_source("bad.goat", "{x: 1, y: true} + {x: 1, y: true}");
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("needs numbers or records of numbers"),
        "{stderr}"
    );
}

#[test]
fn record_arithmetic_and_equality_run_end_to_end() {
    assert_eq!(
        stdout_of("{x: 1, y: 2} + {x: 3, y: 4} == {x: 4, y: 6}"),
        "true"
    );
    assert_eq!(stdout_of("\"a\" == \"b\""), "false");
    assert_eq!(stdout_of("[1, 2] == [1, 2]"), "true");
}

#[test]
fn runs_the_hello_example() {
    let hello = goat(&[
        "run",
        concat!(env!("CARGO_MANIFEST_DIR"), "/../examples/hello.goat"),
    ]);
    assert!(hello.status.success());
    assert_eq!(String::from_utf8(hello.stdout).unwrap(), "hello, world\n");
    assert_eq!(stdout_of("\"hi\""), "hi");
}

#[test]
fn the_target_flag_picks_the_number_widths() {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = dir.path().join("p.goat");
    fs::write(&path, "print(2147483647 + 1)").unwrap();
    let file = path.to_str().unwrap();
    let run = |target: &[&str]| goat(&[&["run", file], target].concat());

    let desktop = run(&["--target", "desktop"]);
    assert_eq!(desktop.stdout, b"2147483648\n");
    assert_eq!(run(&[]).stdout, desktop.stdout);
    let embedded = run(&["--target", "embedded"]);
    assert!(!embedded.status.success());
    assert!(String::from_utf8_lossy(&embedded.stderr).contains("this number got too big"));
    let unknown = run(&["--target", "arm"]);
    assert!(String::from_utf8_lossy(&unknown.stderr).contains("desktop or embedded"));

    let out = dir.path().join("p.wasm");
    let build = goat(&[
        "build",
        file,
        "--target",
        "embedded",
        "-o",
        out.to_str().unwrap(),
    ]);
    assert!(build.status.success());
    assert!(goat_cli::run(&fs::read(out).unwrap()).is_err());
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
fn function_is_a_synonym_for_program() {
    let with_program =
        "apply = program(f, x) do f(x) done\ndbl = program(n) do n * 2 done\napply(dbl, 21)";
    let with_function =
        "apply = function(f, x) do f(x) done\ndbl = function(n) do n * 2 done\napply(dbl, 21)";
    assert_eq!(stdout_of(with_program), "42");
    assert_eq!(stdout_of(with_function), "42");
}

#[test]
fn a_trap_exits_non_zero() {
    let out = run_source("trap.goat", "f = program(n) do f(n) + 1 done\n\nf(1)");
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("trap"));
}

fn failure_of(source: &str) -> (String, String) {
    let out = run_source("t.goat", source);
    assert!(!out.status.success());
    (
        String::from_utf8(out.stdout).unwrap(),
        String::from_utf8(out.stderr).unwrap(),
    )
}

#[test]
fn a_trap_names_its_message_and_the_users_call() {
    let (_, stderr) = failure_of("x = 1\nfirst([]) + x");
    assert!(
        stderr.contains("trap: 2:1: first of an empty list"),
        "{stderr}"
    );
    assert!(stderr.contains("first([])"), "{stderr}");
    assert!(!stderr.contains("in the prelude"), "{stderr}");
}

#[test]
fn a_nested_call_is_blamed_on_the_call_that_trapped() {
    let (_, stderr) = failure_of("x = 1\nfirst(rest([1]))");
    assert!(
        stderr.contains("trap: 2:1: first of an empty list"),
        "{stderr}"
    );
    let (_, stderr) = failure_of("x = 1\nitem([1, 2], 3)");
    assert!(stderr.contains("trap: 2:1: "), "{stderr}");
}

#[test]
fn a_users_own_trap_is_blamed_where_it_is_written() {
    let (_, stderr) = failure_of("x = 1\ntrap(\"stop here\")");
    assert!(stderr.contains("trap: 2:1: stop here"), "{stderr}");
}

#[test]
fn a_number_that_gets_too_big_is_blamed_on_the_operation() {
    let (_, stderr) = failure_of("x = 9223372036854775807\nprint(x + 1)");
    assert!(
        stderr.contains("trap: 2:7: this number got too big"),
        "{stderr}"
    );
    assert!(stderr.contains("x + 1"), "{stderr}");
    let (_, stderr) = failure_of("f = program(n) do n * n done\nx = 1\nf(4611686018427387904)");
    assert!(
        stderr.contains("trap: 1:19: this number got too big"),
        "{stderr}"
    );
}

#[test]
fn lines_printed_before_a_trap_survive() {
    let (stdout, stderr) = failure_of("a = print(1)\nb = print(\"two\")\nfirst([]) + 1");
    assert_eq!(stdout, "1\ntwo\n");
    assert!(stderr.contains("first of an empty list"), "{stderr}");
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

#[test]
fn runs_the_loops_example() {
    let out = goat(&[
        "run",
        concat!(env!("CARGO_MANIFEST_DIR"), "/../examples/loops.goat"),
    ]);
    assert!(out.status.success());
    assert_eq!(
        String::from_utf8(out.stdout).unwrap(),
        "hello\nhello\n1\n4\n9\n16\n25\nfalse\nfalse\ntrue\n2\n4\n6\n5\n10\n15\n"
    );
}

#[test]
fn sequencing_and_loops_run_from_the_command_line() {
    assert_eq!(stdout_of("print(1); print(2); 3"), "1\n2\n3");
    assert_eq!(
        stdout_of("for i from 1 to 3 do print(i) done; false or not false"),
        "1\n2\n3\ntrue"
    );
}

#[test]
fn run_writes_the_turtle_drawing_to_the_o_path() {
    let dir = tempfile::tempdir().expect("temp dir");
    let svg = dir.path().join("spiral.svg");
    let out = goat(&[
        "run",
        concat!(env!("CARGO_MANIFEST_DIR"), "/../examples/spiral.goat"),
        "-o",
        svg.to_str().unwrap(),
    ]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let golden = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/golden/spiral.svg");
    assert_eq!(fs::read(&svg).unwrap(), fs::read(golden).unwrap());
}

#[test]
fn a_turtle_program_without_o_runs_and_writes_nothing() {
    let out = run_source("t.goat", "print(1); forward(10); print(2)");
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "1\n2\n");
    assert!(String::from_utf8_lossy(&out.stderr).contains("-o"));
}

#[test]
fn o_on_a_program_that_never_draws_is_an_error_and_writes_nothing() {
    let dir = tempfile::tempdir().expect("temp dir");
    let src = dir.path().join("n.goat");
    let svg = dir.path().join("n.svg");
    fs::write(&src, "1 + 2").unwrap();
    let out = goat(&["run", src.to_str().unwrap(), "-o", svg.to_str().unwrap()]);
    assert!(!out.status.success());
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "3\n");
    assert!(!svg.exists());
}

const TYPO_TAG: &str = "match Cirle(5) do Circle(r) then r else 0 done";
const TYPO_TAG_DECLS: &str = "tag Cirle tag Circle ";

#[test]
fn run_warns_on_stderr_and_still_succeeds() {
    let out = run_source(
        "p.goat",
        &format!("{TYPO_TAG_DECLS}p = print(1)\n{TYPO_TAG}"),
    );
    assert!(out.status.success());
    let stderr = String::from_utf8(out.stderr).unwrap();
    assert!(stderr.contains("warning in "), "{stderr}");
    assert!(stderr.contains("tag `Cirle` is constructed but never matched"));
    assert!(stderr.contains("^^^^^^^^"), "span caret missing: {stderr}");
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "1\n0\n");
}

#[test]
fn check_and_build_warn_on_stderr_and_succeed() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("p.goat");
    fs::write(&path, format!("{TYPO_TAG_DECLS}{TYPO_TAG}")).unwrap();
    let path = path.to_str().unwrap();
    for command in ["check", "build"] {
        let out = goat(&[command, path]);
        assert!(out.status.success(), "{command}");
        let stderr = String::from_utf8(out.stderr).unwrap();
        assert!(stderr.contains("warning in "), "{command}: {stderr}");
        assert!(!String::from_utf8_lossy(&out.stdout).contains("warning"));
    }
}

#[test]
fn clean_program_prints_no_warnings() {
    let out = run_source("p.goat", "print(1)");
    assert!(out.status.success());
    assert!(!String::from_utf8(out.stderr).unwrap().contains("warning"));
}

#[test]
fn error_program_still_fails() {
    let out = run_source("p.goat", "1 + true");
    assert!(!out.status.success());
    assert!(
        String::from_utf8(out.stderr)
            .unwrap()
            .contains("error(s) in")
    );
}
