//! Mono emits only what a program reaches, so prelude definitions it never
//! calls cost nothing.

use goat_checker::check_with_prelude;
use goat_mir::*;

const PRELUDE: &str = "tag Box double = program(n) do n * 2 done\n\
                       twice = program(f, x) do f(f(x)) done\n\
                       count_down = program(n) do if n < 1 then 0 else count_down(n - 1) done done\n\
                       make = program(n) do Box(n) done\n";

fn lower(prelude: &str, src: &str) -> Program {
    let checked = check_with_prelude(prelude, src).expect("checks");
    let p = mono(&checked).expect("lowers");
    assert_eq!(verify(&p), Ok(()), "{src}");
    p
}

#[test]
fn unused_prelude_definitions_emit_no_code() {
    let src = "1 + 2";
    let without = lower("", src);
    let with = lower(PRELUDE, src);
    assert_eq!(with.funcs.len(), without.funcs.len());
    assert_eq!(with.funcs.len(), 1, "only the entry function");
    assert_eq!(with.data, without.data);
}

#[test]
fn only_the_prelude_definitions_a_program_calls_are_emitted() {
    let entry_only = lower(PRELUDE, "1").funcs.len();
    let uses_double = lower(PRELUDE, "double(4)");
    assert_eq!(uses_double.funcs.len(), entry_only + 1);
    let out = run(&uses_double).expect("runs");
    assert_eq!(out.value, Value::Float(8.0));
    assert_eq!(out.live_allocations, 0);
}

#[test]
fn a_prelude_function_can_take_another_prelude_function() {
    let p = lower(PRELUDE, "twice(double, 3)");
    let out = run(&p).expect("runs");
    assert_eq!(out.value, Value::Float(12.0));
}
