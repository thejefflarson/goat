#[path = "../../mir/tests/common/mod.rs"]
mod common;

use common::*;
use goat::{Boundary, Host, HostInterface, HostValue, NoHost, Profile};
use goat_mir::*;
use goat_native::abi::INSTANCE_VERSION;
use goat_native::abi::{HOST_VERSION, Instance};
use goat_native::{Library, NativeError, Stopped, Versions, build, clang_available};

macro_rules! need_clang {
    () => {
        if !clang_available() {
            eprintln!("skipping: clang is not available");
            return;
        }
    };
}

/// A host that only remembers which one it is.
struct Tagged(u32);

impl Host for Tagged {
    fn signature(&self, _: &str, _: &str) -> Option<(Vec<Boundary>, Boundary)> {
        None
    }

    fn call(&mut self, module: &str, name: &str, _: &[HostValue]) -> Result<HostValue, String> {
        Err(format!("no host function {module}.{name}"))
    }
}

fn library(source: &str) -> Library {
    build(Profile::Desktop, source, &HostInterface::new("")).expect("program builds")
}

#[test]
fn a_program_prints_its_value_through_the_table() {
    need_clang!();
    for (source, expected) in [
        ("6 * 7", "42"),
        ("1.25 * 2", "2.5"),
        ("1 < 2", "true"),
        ("2 < 1", "false"),
    ] {
        let run = library(source).run(NoHost).unwrap();
        assert_eq!(run.printed, [expected], "{source}");
        assert_eq!(run.result, Ok(()));
        assert_eq!(run.live_allocs, 0);
    }
}

#[test]
fn the_embedded_profile_prints_through_the_same_table() {
    need_clang!();
    let lib = build(Profile::Embedded, "6 * 7", &HostInterface::new("")).unwrap();
    assert_eq!(lib.run(NoHost).unwrap().printed, ["42"]);
    let lib = build(Profile::Embedded, "1.5 * 2", &HostInterface::new("")).unwrap();
    assert_eq!(lib.run(NoHost).unwrap().printed, ["3"]);
}

#[test]
fn two_programs_run_at_once_each_with_its_own_instance_and_host() {
    need_clang!();
    let (sum, product) = (library("40 + 2"), library("if 1 < 2 then 0.5 else 1 done"));
    let repeat = |lib: &Library, tag: u32| {
        let mut run = lib.run(Tagged(tag)).unwrap();
        for _ in 0..49 {
            run = lib.run(Tagged(tag)).unwrap();
        }
        run
    };
    let (a, b) = std::thread::scope(|scope| {
        let a = scope.spawn(|| repeat(&sum, 1));
        let b = scope.spawn(|| repeat(&product, 2));
        (a.join().unwrap(), b.join().unwrap())
    });
    assert_eq!((a.printed, a.host.0), (vec!["42".to_string()], 1));
    assert_eq!((b.printed, b.host.0), (vec!["0.5".to_string()], 2));
}

#[test]
fn interleaved_runs_do_not_share_state() {
    need_clang!();
    let (first, second) = (library("6 * 7"), library("1 + 1 < 3"));
    let one = first.run(Tagged(1)).unwrap();
    let two = second.run(Tagged(2)).unwrap();
    let again = first.run(Tagged(3)).unwrap();
    assert_eq!(one.printed, ["42"]);
    assert_eq!(two.printed, ["true"]);
    assert_eq!(again.printed, ["42"]);
    assert_eq!((one.host.0, two.host.0, again.host.0), (1, 2, 3));
}

#[test]
fn an_old_table_or_instance_is_rejected_before_anything_runs() {
    need_clang!();
    let lib = library("6 * 7");
    let old_host = lib.run_versioned(
        NoHost,
        Versions {
            host: 0,
            instance: INSTANCE_VERSION,
        },
    );
    assert!(matches!(
        old_host,
        Err(NativeError::Version {
            what: "goat_host",
            found: 0,
            ..
        })
    ));
    let old_instance = lib.run_versioned(
        NoHost,
        Versions {
            host: goat_native::abi::HOST_VERSION,
            instance: 0,
        },
    );
    let Err(error) = old_instance else {
        panic!("an old instance ran");
    };
    assert!(
        error.to_string().contains("goat_instance version"),
        "{error}"
    );
    assert_eq!(lib.run(NoHost).unwrap().printed, ["42"], "still runs");
}

#[test]
fn a_newer_table_is_accepted() {
    need_clang!();
    let versions = Versions {
        host: goat_native::abi::HOST_VERSION + 1,
        instance: INSTANCE_VERSION + 1,
    };
    let run = library("6 * 7").run_versioned(NoHost, versions).unwrap();
    assert_eq!(run.printed, ["42"]);
}

#[test]
fn a_trap_comes_back_as_a_stop_through_the_tables_trap_entry() {
    need_clang!();
    let run = library("1 // 0").run(NoHost).unwrap();
    assert!(run.printed.is_empty());
    assert_eq!(
        run.result,
        Err(Stopped {
            message: DIVISION_BY_ZERO.to_string(),
            site: Some((0, 6))
        })
    );
    let after = library("6 * 7").run(NoHost).unwrap();
    assert_eq!(after.result, Ok(()), "a trap leaves no state behind");
}

#[test]
fn a_trap_names_the_site_stored_in_the_instance() {
    need_clang!();
    let body = let_(
        0,
        Expr::Site(3, 9),
        Expr::BinInt(IntOp::Div, Box::new(int(1)), Box::new(int(0))),
    );
    let program = program(vec![func(MTy::Int, body)]);
    assert_eq!(verify(&program), Ok(()));
    let lib = Library::build(&goat_llvm::emit(&program).unwrap()).unwrap();
    let run = lib.run(NoHost).unwrap();
    assert_eq!(
        run.result,
        Err(Stopped {
            message: DIVISION_BY_ZERO.to_string(),
            site: Some((3, 9))
        })
    );
}

#[test]
fn an_unsupported_program_says_why() {
    let looping = "loop = program(i) do if i == 0 then 0 else loop(i - 1) done done\nloop(3)";
    let Err(error) = build(Profile::Desktop, looping, &HostInterface::new("")) else {
        panic!("a program that loops by tail call built");
    };
    assert!(error.unsupported().is_some(), "{error}");
}

#[test]
fn a_trapped_instance_is_refused_until_it_is_reset() {
    need_clang!();
    let (trapping, fine) = (library("1 // 0"), library("6 * 7"));
    let mut instance = Instance::new(4096);
    let run = trapping
        .run_in(&mut instance, NoHost, HOST_VERSION)
        .unwrap();
    assert!(run.result.is_err());
    assert!(instance.is_dead());

    for lib in [&trapping, &fine] {
        let Err(error) = lib.run_in(&mut instance, NoHost, HOST_VERSION) else {
            panic!("a dead instance ran");
        };
        assert!(matches!(error, NativeError::DeadInstance), "{error}");
        assert!(error.to_string().contains("reset"), "{error}");
    }

    instance.reset();
    assert!(!instance.is_dead());
    let run = fine.run_in(&mut instance, NoHost, HOST_VERSION).unwrap();
    assert_eq!((run.printed, run.result), (vec!["42".to_string()], Ok(())));
    let again = fine.run_in(&mut instance, NoHost, HOST_VERSION).unwrap();
    assert_eq!(again.printed, ["42"], "a live instance runs again");

    let mut fresh = Instance::new(4096);
    let run = fine.run_in(&mut fresh, NoHost, HOST_VERSION).unwrap();
    assert_eq!(run.printed, ["42"]);
}
