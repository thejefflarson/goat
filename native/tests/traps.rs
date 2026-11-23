//! Traps on the native backend end the run with the message and the blamed
//! source range the wasm backend reports, and a program that recurses past its
//! thread's stack ends in goat's stack-overflow trap instead of a crash
//! (ADR 0042).

use goat::{HostInterface, NoHost, Profile, STACK_OVERFLOW};
use goat_native::{Library, Stopped, build, clang_available};

macro_rules! need_clang {
    () => {
        if !clang_available() {
            eprintln!("skipping: clang is not available");
            return;
        }
    };
}

fn host() -> HostInterface {
    HostInterface::turtle()
}

fn native_stop(source: &str) -> Stopped {
    let library = build(Profile::Desktop, source, &host()).expect("program builds");
    library
        .run(NoHost)
        .expect("it runs")
        .result
        .expect_err("the program traps")
}

fn wasm_stop(source: &str) -> goat::native::Stopped {
    let wasm = goat::compile(source, &host()).expect("compiles");
    goat::native::run_to_end(&wasm, NoHost)
        .expect("it runs")
        .result
        .expect_err("the program traps")
}

fn rendered(source: &str, stop: &Stopped) -> String {
    stop.render(source)
}

#[test]
fn a_trap_renders_exactly_as_wasm_renders_it() {
    need_clang!();
    for source in [
        "x = 1\nfirst([]) + x",
        "x = 1\nfirst(rest([1]))",
        "x = 1\nitem([1, 2], 3)",
        "x = 1\ntrap(\"stop here\")",
        "x = 9223372036854775807\nprint(x + 1)",
        "f = program(n) do n * n done\nx = 1\nf(4611686018427387904)",
        "x = 0\n1 // x",
        "nest = program(n, acc) do if n < 1 then acc else nest(n - 1, [acc]) done done\n\
         a = nest(300000, [])\nb = nest(300000, [])\nprint(a == b)",
    ] {
        let native = native_stop(source);
        let wasm = wasm_stop(source);
        let wasm = goat::render_trap(source, &wasm.message, wasm.site);
        assert_eq!(rendered(source, &native), wasm, "{source}");
        assert!(native.site.is_some(), "{source}");
    }
}

#[test]
fn a_trap_names_its_line_and_column() {
    need_clang!();
    let source = "x = 1\ntrap(\"stop here\")";
    assert!(
        rendered(source, &native_stop(source)).starts_with("trap: 2:1: stop here"),
        "{}",
        rendered(source, &native_stop(source))
    );
}

const FOREVER: &str = "f = program(n) do f(n) + 1 done\n\nf(1)";

#[test]
fn deep_non_tail_recursion_ends_in_the_stack_overflow_trap() {
    need_clang!();
    let stop = native_stop(FOREVER);
    assert_eq!(stop.message, STACK_OVERFLOW);
    let wasm = wasm_stop(FOREVER);
    assert_eq!(rendered(FOREVER, &stop), {
        goat::render_trap(FOREVER, &wasm.message, wasm.site)
    });
}

#[test]
fn an_overflow_inside_the_prelude_is_blamed_on_the_users_call() {
    need_clang!();
    let source = "nest = program(n, acc) do if n < 1 then acc else nest(n - 1, [acc]) done done\n\
                  a = nest(300000, [])\nb = nest(300000, [])\nprint(a == b)";
    let stop = native_stop(source);
    assert_eq!(stop.message, STACK_OVERFLOW);
    let (start, end) = stop.site.expect("blamed on the comparison");
    assert_eq!(&source[start..end], "a == b");
}

#[test]
fn a_small_stack_overflows_cleanly_and_a_large_one_goes_deep() {
    need_clang!();
    let depth = |bytes: usize, n: u64| {
        let source = format!(
            "sum = program(n) do if n == 0 then 0 else n + sum(n - 1) done done\nprint(sum({n}))"
        );
        let library = build(Profile::Desktop, &source, &host()).unwrap();
        std::thread::Builder::new()
            .stack_size(bytes)
            .spawn(move || library.run(NoHost).unwrap())
            .unwrap()
            .join()
            .unwrap()
    };
    let small = depth(1 << 20, 10_000_000);
    assert_eq!(small.result.unwrap_err().message, STACK_OVERFLOW);
    let large = depth(1 << 30, 5_000_000);
    assert_eq!(large.printed, ["12500002500000"]);
}

#[test]
fn a_trap_in_one_run_leaves_the_next_run_of_the_library_working() {
    need_clang!();
    let library: Library = build(Profile::Desktop, FOREVER, &host()).unwrap();
    for _ in 0..2 {
        let run = library.run(NoHost).unwrap();
        assert_eq!(run.result.unwrap_err().message, STACK_OVERFLOW);
    }
}
