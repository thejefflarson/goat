//! `foreign` functions run under wasmtime and the interpreter against one test
//! host (`support::TestHost`). Each program is checked for the same output, the
//! same host calls in the same order, and nothing left allocated on either side.

#[allow(dead_code)]
mod support;

use support::run_foreign;
use wasmtime::{Engine, Module};

const DECLS: &str = "\
note = foreign \"test\" \"note\" (Number) -> Unit
double = foreign \"test\" \"double\" (Number) -> Number
negate = foreign \"test\" \"negate\" (Bool) -> Bool
say = foreign \"test\" \"say\" (String) -> Unit
shout = foreign \"test\" \"shout\" (String) -> String
greeting = foreign \"test\" \"greeting\" () -> String
nothing = foreign \"test\" \"nothing\" () -> String
mix = foreign \"test\" \"mix\" (Number, Bool, String) -> Number
";

fn go(body: &str) -> (String, Vec<String>) {
    run_foreign(&format!("{DECLS}{body}"))
}

#[test]
fn a_number_round_trips() {
    let (printed, log) = go("print(double(21))");
    assert_eq!(printed, "42");
    assert_eq!(log, ["double(21)"]);
}

#[test]
fn a_bool_round_trips() {
    let (printed, log) = go("print(negate(true)); print(negate(false))");
    assert_eq!(printed, "false\ntrue");
    assert_eq!(log, ["negate(true)", "negate(false)"]);
}

#[test]
fn unit_calls_in_discard_positions_run_once_each_in_order() {
    let (printed, log) = go("note(1); note(2); r = note(3); note(4); print(0)");
    assert_eq!(printed, "0");
    assert_eq!(log, ["note(1)", "note(2)", "note(3)", "note(4)"]);

    let (_, log) = go("x = note(5)\nnote(6); 0");
    assert_eq!(log, ["note(5)", "note(6)"]);
}

#[test]
fn a_unit_call_whose_value_is_the_program_runs() {
    let (printed, log) = go("note(9)");
    assert_eq!(printed, "");
    assert_eq!(log, ["note(9)"]);
}

#[test]
fn a_string_goes_to_the_host_and_a_string_comes_back() {
    let (printed, log) = go("print(shout(\"hi\"))");
    assert_eq!(printed, "HI!");
    assert_eq!(log, ["shout(\"hi\")"]);
}

#[test]
fn a_returned_string_is_owned_borrowed_by_calls_and_then_freed() {
    let (printed, log) = go("s = greeting()\nsay(s); say(s); print(s)");
    assert_eq!(printed, "hello from the host");
    let said = "say(\"hello from the host\")";
    assert_eq!(log, ["greeting()", said, said]);
}

#[test]
fn strings_returned_by_the_host_free_whether_or_not_they_are_used() {
    go("greeting(); 0");
    go("s = greeting()\n0");
    go("print(shout(shout(shout(\"a\"))))");
    go("print(nothing())");
    go("repeat 50 times do say(shout(greeting())) done;\n0");
}

#[test]
fn an_empty_string_crosses_the_boundary() {
    let (printed, log) = go("print(nothing()); say(nothing()); 0");
    assert_eq!(printed, "\n0");
    assert_eq!(log, ["nothing()", "nothing()", "say(\"\")"]);
}

#[test]
fn mixed_parameters_arrive_in_order() {
    let (printed, log) = go("print(mix(double(1), negate(false), shout(\"a\")))");
    assert_eq!(printed, "5");
    assert_eq!(
        log,
        [
            "double(1)",
            "negate(false)",
            "shout(\"a\")",
            "mix(2, true, \"A!\")"
        ]
    );
}

#[test]
fn a_foreign_function_is_a_value() {
    let (printed, log) = go("g = double\nprint(g(4))");
    assert_eq!(printed, "8");
    assert_eq!(log, ["double(4)"]);

    let (printed, _) = go("apply = program(f, x) do f(x) done\nprint(apply(double, 5))");
    assert_eq!(printed, "10");

    let (printed, _) = go("apply = program(f, x) do f(x) done\nprint(apply(shout, \"a\"))");
    assert_eq!(printed, "A!");

    let (_, log) = go("h = note\nh(1); h(2); 0");
    assert_eq!(log, ["note(1)", "note(2)"]);

    let (_, log) = go("fs = {a: say, b: note}\nfs.a(\"x\"); fs.b(2); 0");
    assert_eq!(log, ["say(\"x\")", "note(2)"]);
}

#[test]
fn calls_inside_functions_closures_and_loops_run_every_time() {
    let src = "speak = program(s) do say(s) done\n\
               speak(\"a\"); speak(shout(\"b\"))\n";
    let (_, log) = go(&format!("{src}; 0"));
    assert_eq!(log, ["say(\"a\")", "shout(\"b\")", "say(\"B!\")"]);

    let (_, log) = go("repeat 3 times do note(7) done;\nfor i from 1 to 2 do note(i) done;\n0");
    assert_eq!(log.len(), 5);

    let (_, log) = go("n = 3\nlater = program(k) do note(n + k) done\nlater(1); later(2); 0");
    assert_eq!(log, ["note(4)", "note(5)"]);
}

#[test]
fn only_the_foreign_functions_a_program_uses_are_imported() {
    let engine = Engine::default();
    let imports = |src: &str| -> Vec<String> {
        let wasm = goat::compile_turtle(src).expect("compiles");
        let module = Module::new(&engine, wasm).expect("valid");
        module
            .imports()
            .filter(|i| i.module() == "test")
            .map(|i| i.name().to_string())
            .collect()
    };
    assert!(imports(&format!("{DECLS}print(1)")).is_empty());
    assert_eq!(imports(&format!("{DECLS}print(double(1))")), ["double"]);
    let twice = format!("{DECLS}print(double(double(1)))");
    assert_eq!(imports(&twice), ["double"]);
    let two = format!("{DECLS}note(1); print(double(1))");
    assert_eq!(imports(&two), ["note", "double"]);
}

#[test]
fn programs_without_foreign_functions_import_nothing_of_the_hosts() {
    let wasm = goat::compile_turtle("print(1)").expect("compiles");
    let module = Module::new(&Engine::default(), wasm).expect("valid");
    assert!(module.imports().all(|i| i.module() == "goat"));
}

#[test]
fn a_program_run_without_its_host_function_fails_to_link() {
    let wasm = goat::compile_turtle(&format!("{DECLS}print(double(1))")).expect("compiles");
    let error = support::execute(&wasm).err().expect("no host");
    assert!(
        error.contains("provides no function test.double"),
        "{error}"
    );
}
