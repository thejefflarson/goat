//! Tail calls on the native backend: a loop runs 10^8 deep in constant stack
//! whether it calls itself, a partner function or a closure, arguments past
//! the register budget reach the callee through the spill area, and the
//! results and allocation counts match the interpreter's.

mod support;

use goat::{NoHost, Profile};
use goat_llvm::{Abi, EmitOptions, emit_with_options};
use goat_native::{Library, Run, clang_available};
use std::process::Command;
use support::interpreted;

macro_rules! need_clang {
    () => {
        if !clang_available() {
            eprintln!("skipping: clang is not available");
            return;
        }
    };
}

fn native(profile: Profile, source: &str, abi: Abi) -> Run<NoHost> {
    let checked = goat_checker::check(source).expect("type-checks");
    let program = goat_mir::mono_for(&checked, profile).expect("monomorphizes");
    let options = EmitOptions {
        abi,
        ..EmitOptions::default()
    };
    let ll = emit_with_options(&program, options).unwrap_or_else(|e| panic!("{source}: {e}"));
    Library::build(&ll)
        .unwrap_or_else(|e| panic!("{source}: {e}"))
        .run(NoHost)
        .expect("it runs")
}

fn cramped() -> Abi {
    Abi {
        int_registers: 2,
        float_registers: 1,
        musttail: true,
    }
}

const SELF_LOOP: &str = "count = program(n, acc) do if n == 0 then acc else count(n - 1, acc + 1) done done\n\
                         count(100000000, 0)";

const MUTUAL: &str = "is_even = program(n) do if n == 0 then true else is_odd(n - 1, 7) done done\n\
                      is_odd = program(n, spare) do if n == 0 then false else is_even(n - 1) done done\n\
                      is_even(100000000)";

/// `bounce` calls its closure argument in tail position, which tail-calls `go`
/// again through a closure of its own: indirect recursion with no direct cycle.
const INDIRECT: &str = "bounce = program(f, n) do if n == 0 then 0 else f(n - 1) done done\n\
                        go = program(n) do bounce(program(m) do go(m) done, n) done\n\
                        go(100000000)";

#[test]
fn deep_loops_run_in_constant_stack() {
    need_clang!();
    for profile in [Profile::Desktop, Profile::Embedded] {
        for (source, printed) in [(SELF_LOOP, "100000000"), (MUTUAL, "true"), (INDIRECT, "0")] {
            let run = native(profile, source, Abi::DEFAULT);
            assert_eq!(run.result, Ok(()), "{source}");
            assert_eq!(run.printed, [printed], "{profile:?}: {source}");
            assert_eq!(run.live_allocs, 0, "{source}");
        }
    }
}

/// Programs whose loops carry integers, floats, booleans and heap values, and
/// call each other with different parameter lists.
const CORPUS: &[&str] = &[
    "sum = program(n, a, b, c, d, g, h, k) do if n == 0 then a + b + c + d + g + h + k else sum(n - 1, a + 1, b, c, d, g, h, k) done done\n\
     sum(1000, 1, 2, 3, 4, 5, 6, 7)",
    "mix = program(n, x, y, z) do if n == 0 then x + y + z else mix(n - 1, x + 0.5, y, z * 1.0) done done\n\
     mix(100, 0.25, 2.5, 4.0)",
    "pick = program(n, flag, s, t) do if n == 0 then (if flag then s else t done) else pick(n - 1, flag, s, t) done done\n\
     pick(50, true, \"yes\", \"no\")",
    "even = program(n, x, f) do if n == 0 then x else odd(n - 1, x + 1) done done\n\
     odd = program(n, x) do if n == 0 then x else even(n - 1, x * 2, 1.5) done done\n\
     r = even(20, 0, 0.5)\nr + 0",
    "bounce = program(f, n, a, b, c, d, g, h) do if n < 1 then a + b + c + d + g + h else f(n - 1, a + 1, b + 2, c, d, g, h) done done\n\
     go = program(n, a, b, c, d, g, h) do bounce(program(m, a, b, c, d, g, h) do go(m, a, b, c, d, g, h) done, n, a, b, c, d, g, h) done\n\
     r = go(300, 0, 0, 1, 2, 3, 4)\nr + 0",
    "walk = program(xs, total, scale) do match xs do [] then total [x, ...rest] then walk(rest, total + x * scale, scale) done done\n\
     r = walk([1.5, 2.5, 3.0, 4.0], 0.0, 2.0)\nr + 0.0",
    "up = program(n, acc) do if n == 0 then acc else up(n - 1, link(n, acc)) done done\n\
     total = program(xs, sum) do match xs do [] then sum [x, ...rest] then total(rest, sum + x) done done\n\
     r = total(up(200, []), 0)\nr + 0",
];

#[test]
fn spilled_and_registered_arguments_agree_with_the_interpreter() {
    need_clang!();
    for profile in [Profile::Desktop, Profile::Embedded] {
        for source in CORPUS {
            let (expected, live) = interpreted(profile, source);
            for abi in [Abi::DEFAULT, cramped()] {
                let run = native(profile, source, abi);
                assert_eq!(run.result, Ok(()), "{source}");
                assert_eq!(run.printed, expected, "{profile:?} {abi:?}: {source}");
                assert_eq!(
                    run.live_allocs as usize, live,
                    "{profile:?} {abi:?}: {source}"
                );
            }
        }
    }
}

/// The particle benchmark's `spawn` and `change_each` loop by tail call. The
/// interpreter counts every closure object it makes, and native shares a closure
/// that captures nothing, so the totals differ by those objects; they scale with
/// the frames and not with the particles, so a particle's records are counted
/// the same.
fn particle_allocations(particles: u32, frames: u32) -> (u64, u64) {
    let source = format!(
        "spawn = program(i, acc) do
  if i == 0 then acc else
    spawn(i - 1, link({{p: {{x: i * 0.4, y: i * 0.3}}, v: {{x: 1.5 - i * 0.003, y: 0.7 + i * 0.002}}}}, acc))
  done
done
step = program(q) do
  p = q.p + q.v
  v = q.v * {{x: 0.999, y: 0.999}}
  hit_x = p.x < 0 or p.x > 400
  hit_y = p.y < 0 or p.y > 300
  {{
    p: p,
    v: {{
      x: if hit_x then 0 - v.x else v.x done,
      y: if hit_y then 0 - v.y else v.y done
    }}
  }}
done
frames = program(ps, n) do if n == 0 then ps else frames(change_each(ps, step), n - 1) done done
sum = program(xs, acc) do match xs do [] then acc [q, ...rest] then sum(rest, acc + q.p.x + q.p.y) done done
r = sum(frames(spawn({particles}, []), {frames}), 0.0)
r + 0.0"
    );
    let checked = goat_checker::check(&source).expect("type-checks");
    let program = goat_mir::mono_for(&checked, Profile::Desktop).expect("monomorphizes");
    let expected = goat_mir::run(&program).expect("interprets");
    let run = native(Profile::Desktop, &source, Abi::DEFAULT);
    assert_eq!(run.result, Ok(()));
    assert_eq!(run.live_allocs, 0);
    assert_eq!(run.printed, interpreted(Profile::Desktop, &source).0);
    (run.allocations, expected.allocations as u64)
}

#[test]
fn the_benchmark_particles_run_natively_with_the_interpreters_record_allocations() {
    need_clang!();
    let (small_native, small_interpreted) = particle_allocations(10, 4);
    let (large_native, large_interpreted) = particle_allocations(1000, 4);
    let gap = small_interpreted - small_native;
    assert_eq!(large_interpreted - large_native, gap);
    assert!(gap <= 16, "only closure objects differ: {gap}");
}

/// `tests/ll/tailcc_stack_arguments.ll` is the miscompile ADR 0042 records:
/// Apple clang on aarch64, at -O1 and above, returns from a `tailcc` function
/// with stack arguments without popping them. This reports whether the clang on
/// this machine still does; the spill rule holds either way, and the register
/// loop in the same file must always be right.
#[test]
fn the_register_only_loop_is_right_and_the_stack_loop_is_reported() {
    need_clang!();
    let dir = std::env::temp_dir().join(format!("goat_tailcc_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let ll = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/ll/tailcc_stack_arguments.ll"
    );
    for level in ["-O0", "-O1", "-O2"] {
        let exe = dir.join(format!("loop{level}"));
        let built = Command::new(goat_native::driver::clang())
            .args([level, "-x", "ir", ll, "-o"])
            .arg(&exe)
            .output()
            .unwrap();
        assert!(
            built.status.success(),
            "{}",
            String::from_utf8_lossy(&built.stderr)
        );
        let registers = Command::new(&exe).arg("registers").output().unwrap();
        assert_eq!(
            String::from_utf8_lossy(&registers.stdout).trim(),
            "1000",
            "register-only tailcc at {level}"
        );
        let stack = Command::new(&exe).output().unwrap();
        let correct =
            stack.status.success() && String::from_utf8_lossy(&stack.stdout).trim() == "1000";
        eprintln!(
            "tailcc with stack arguments at {level}: {}",
            if correct {
                "correct"
            } else {
                "MISCOMPILED (the spill rule stays)"
            }
        );
    }
}
