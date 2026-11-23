//! Closures, captures and the call-depth counter on the native backend,
//! checked against the reference interpreter's allocation counts and against
//! wasm.

#[path = "../../mir/tests/common/mod.rs"]
mod common;
mod support;

use common::*;
use goat::{EmbeddedLimits, HostInterface, NoHost, Profile, STACK_OVERFLOW};
use goat_llvm::{EmitOptions, emit, emit_with_options};
use goat_mir::*;
use goat_native::{Library, Run, build, clang_available};
use support::interpreted;

macro_rules! need_clang {
    () => {
        if !clang_available() {
            eprintln!("skipping: clang is not available");
            return;
        }
    };
}

/// Source programs whose functions never end in a call, since the native
/// backend has no tail calls yet: each result is added to 0 or used further.
const CORPUS: &[&str] = &[
    "add = program(a) do program(b) do a + b done done\n\
     add_ten = add(10)\nanswer = add_ten(5)\nanswer + 0",
    "repeat_add = program(n) do\n\
       go = program(k) do if k < 1 then 0 else n + go(k - 1) done done\n\
       r = go(3)\nr + 1\n\
     done\nanswer = repeat_add(10)\nanswer + 0",
    "tag Pile = Nil | Cons(_, Pile)\n\
     keep = program(p) do program(x) do match p do Nil then x Cons(a, r) then a + x done done done\n\
     f = keep(Cons(5, Nil))\ng = f\na = f(1)\nb = g(2)\na + b",
    "label = program(s) do program(n) do s done done\n\
     f = label(\"hello\")\nprint(f(1));\nprint(f(2));\nlast = f(3)\nlast",
    "twice = program(f) do program(x) do a = f(x)\nf(a) + 1 done done\n\
     outer = program(k) do\n\
       add_two = twice(program(n) do n + k done)\n\
       r = add_two(40)\nr + 1\n\
     done\nanswer = outer(1)\nanswer + 0",
    "pair = program(a, b) do {first: program(z) do a + z done, second: program(z) do b * z done} done\n\
     p = pair(3, 4)\nx = p::first(10)\ny = p::second(10)\nx + y",
];

/// The interpreter, wasm and native agree on what each program prints, and none
/// leaves anything allocated.
#[test]
fn the_interpreter_wasm_and_native_agree_on_closures() {
    need_clang!();
    for profile in [Profile::Desktop, Profile::Embedded] {
        for source in CORPUS {
            let host = HostInterface::new(goat_checker::PRELUDE);
            let (expected, live) = interpreted(profile, source);
            assert_eq!(live, 0, "the interpreter leaked: {source}");
            let (wasm, _) = goat::compile_for(profile, source, &host).expect("compiles");
            let wasm = goat::native::run(&wasm).expect("wasm runs");
            let run = build(profile, source, &host)
                .unwrap_or_else(|e| panic!("{source}: {e}"))
                .run(NoHost)
                .unwrap();
            assert_eq!(run.result, Ok(()), "{source}");
            assert_eq!(wasm.printed, expected, "wasm on {profile:?}: {source}");
            assert_eq!(run.printed, expected, "native on {profile:?}: {source}");
            assert_eq!(run.live_allocs, 0, "native leaked on {profile:?}: {source}");
        }
    }
}

#[test]
fn closures_are_built_called_and_freed() {
    need_clang!();
    let source = "add = program(a) do program(b) do a + b done done\n\
                  f = add(10)\nr = f(5)\nr + 0";
    let host = HostInterface::new(goat_checker::PRELUDE);
    let run = build(Profile::Desktop, source, &host)
        .unwrap()
        .run(NoHost)
        .unwrap();
    assert_eq!(run.printed, ["15"]);
    assert_eq!((run.live_allocs, run.allocations), (0, 1));
}

fn native(p: &Program) -> Run<NoHost> {
    let ll = emit(p).expect("the program emits");
    Library::build(&ll)
        .expect("clang builds it")
        .run(NoHost)
        .expect("it runs")
}

#[test]
fn a_closure_that_captures_nothing_is_static_and_allocates_nothing() {
    need_clang!();
    let double = closure_fn(
        vec![(0, MTy::Int)],
        1,
        vec![],
        MTy::Int,
        let_(2, drop_(1), mul(local(0), int(2))),
    );
    let apply = func_with(
        vec![(0, closure_ty(0)), (1, MTy::Int)],
        MTy::Int,
        call_closure(local(0), vec![local(1)]),
    );
    let main = func(
        MTy::Int,
        let_(
            0,
            Expr::MakeClosure(FuncId(1), vec![]),
            call(2, vec![local(0), int(21)]),
        ),
    );
    let p = with_closures(program(vec![main, double, apply]), vec![MTy::Int]);
    assert_eq!(verify(&p), Ok(()));
    let run = native(&p);
    assert_eq!(run.printed, ["42"]);
    assert_eq!((run.live_allocs, run.allocations), (0, 0));
}

#[test]
fn a_closure_capturing_a_record_frees_it_with_the_closure() {
    need_clang!();
    let body = closure_fn(
        vec![(0, MTy::Int)],
        1,
        vec![record_ty()],
        MTy::Int,
        let_(
            2,
            Expr::Capture(0),
            let_(
                3,
                Expr::Field(Local(2), 0),
                let_(4, drop_(2), let_(5, drop_(1), add(local(3), local(0)))),
            ),
        ),
    );
    let main = func(
        MTy::Int,
        let_(
            0,
            alloc_record(7),
            let_(
                1,
                Expr::MakeClosure(FuncId(1), vec![local(0)]),
                let_(
                    2,
                    Expr::Dup(Local(1)),
                    let_(
                        3,
                        call_closure(local(1), vec![int(5)]),
                        let_(
                            4,
                            call_closure(local(1), vec![int(1)]),
                            add(local(3), local(4)),
                        ),
                    ),
                ),
            ),
        ),
    );
    let p = with_closures(program(vec![main, body]), vec![MTy::Int]);
    assert_eq!(verify(&p), Ok(()));
    let expected = goat_mir::run(&p).expect("the interpreter runs it");
    let run = native(&p);
    assert_eq!(run.printed, ["20"]);
    assert_eq!(run.live_allocs, 0);
    assert_eq!(run.allocations, expected.allocations as u64);
}

#[test]
fn a_record_of_closures_frees_each_through_its_own_drop_id() {
    need_clang!();
    let double = closure_fn(
        vec![(0, MTy::Int)],
        1,
        vec![],
        MTy::Int,
        let_(2, drop_(1), mul(local(0), int(2))),
    );
    let holds = closure_fn(
        vec![(0, MTy::Int)],
        1,
        vec![record_ty()],
        MTy::Int,
        let_(
            2,
            Expr::Capture(0),
            let_(
                3,
                Expr::Field(Local(2), 0),
                let_(4, drop_(2), let_(5, drop_(1), add(local(3), local(0)))),
            ),
        ),
    );
    let main = func(
        MTy::Int,
        let_(
            0,
            Expr::AllocRecord(
                FNS,
                vec![
                    Expr::MakeClosure(FuncId(1), vec![]),
                    Expr::MakeClosure(FuncId(2), vec![alloc_record(10)]),
                ],
            ),
            let_(
                1,
                call_closure(Expr::Field(Local(0), 0), vec![int(7)]),
                let_(
                    2,
                    call_closure(Expr::Field(Local(0), 1), vec![local(1)]),
                    let_(3, drop_(0), local(2)),
                ),
            ),
        ),
    );
    let p = with_closures(program(vec![main, double, holds]), vec![MTy::Int]);
    assert_eq!(verify(&p), Ok(()));
    let expected = goat_mir::run(&p).expect("the interpreter runs it");
    let run = native(&p);
    assert_eq!(run.printed, ["24"]);
    assert_eq!(run.live_allocs, 0);
    assert_eq!(
        run.allocations,
        expected.allocations as u64 - 1,
        "the interpreter allocates the closure that captures nothing"
    );
}

const DEEP: &str = "down = program(n) do if n < 1 then 0 else 1 + down(n - 1) done done\n\
                    r = down(100)\nprint(r);\nr + 0";
const DEEP_CLOSURE: &str = "make = program(k) do\n\
       go = program(n) do if n < 1 then k else 1 + go(n - 1) done done\n\
       go\n\
     done\ngo = make(0)\nr = go(100)\nprint(r);\nr + 0";

fn embedded_native(source: &str, call_depth: u32) -> Run<NoHost> {
    let checked = goat_checker::check(source).expect("type-checks");
    let program = goat_mir::mono_for(&checked, Profile::Embedded).expect("monomorphizes");
    assert_eq!(verify(&program), Ok(()), "{source}");
    let options = EmitOptions {
        call_depth,
        ..EmitOptions::default()
    };
    let ll = emit_with_options(&program, options).expect("emits");
    Library::build(&ll)
        .expect("clang builds it")
        .run(NoHost)
        .expect("it runs")
}

fn embedded_wasm(source: &str, call_depth: u32) -> goat::native::Finished<NoHost> {
    let limits = EmbeddedLimits {
        call_depth,
        ..EmbeddedLimits::default()
    };
    let host = HostInterface::new(goat_checker::PRELUDE);
    let (wasm, _) = goat::compile_embedded(source, &host, limits).expect("compiles");
    goat::native::run_to_end(&wasm, NoHost).expect("loads")
}

/// The depth trap fires at the same call as in the embedded wasm build, with
/// the same message and the same blamed range, for every bound around the
/// depth the program reaches.
#[test]
fn the_depth_trap_fires_where_embedded_wasm_fires() {
    need_clang!();
    for source in [DEEP, DEEP_CLOSURE] {
        let mut trapped = 0;
        for call_depth in 98..=106 {
            let wasm = embedded_wasm(source, call_depth);
            let run = embedded_native(source, call_depth);
            match (&wasm.result, &run.result) {
                (Ok(_), Ok(())) => assert_eq!(run.printed, wasm.printed),
                (Err(expected), Err(stopped)) => {
                    trapped += 1;
                    assert_eq!(stopped.message, STACK_OVERFLOW);
                    assert_eq!(stopped.message, expected.message);
                    assert_eq!(stopped.site, expected.site, "{source}");
                }
                (wasm, native) => panic!("bound {call_depth}: wasm {wasm:?}, native {native:?}"),
            }
        }
        assert!(
            (1..9).contains(&trapped),
            "the bounds straddle the program's depth: {source}"
        );
    }
}

#[test]
fn a_desktop_program_has_no_depth_bound() {
    need_clang!();
    let host = HostInterface::new(goat_checker::PRELUDE);
    let run = build(Profile::Desktop, DEEP, &host)
        .unwrap()
        .run(NoHost)
        .unwrap();
    assert_eq!(run.printed, ["100", "100"]);
    assert_eq!(run.result, Ok(()));
}

#[test]
fn a_tail_call_still_falls_back_with_a_reason() {
    need_clang!();
    let source = "loop = program(n) do if n < 1 then 7 else loop(n - 1) done done\nloop(10)";
    let host = HostInterface::new(goat_checker::PRELUDE);
    let error = build(Profile::Desktop, source, &host)
        .err()
        .expect("tail calls are not lowered yet");
    assert!(
        error
            .unsupported()
            .is_some_and(|r| r.contains("tail calls")),
        "{error}"
    );
}
