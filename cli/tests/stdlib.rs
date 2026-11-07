//! The list functions in the prelude: every program runs through the
//! interpreter and through wasm under wasmtime, which must print the same
//! lines and leave no heap object live. The MIR verifier runs on every program
//! too (see `support::interpret`).

use goat_mir::interp::{self, InterpError};

#[allow(dead_code)]
mod support;

use support::run;

const DOUBLE: &str = "double = program(n) do n * 2 done ";
const BIG: &str = "big = program(n) do n > 2 done ";

/// A list of `1..=n` built in constant stack.
const BUILD: &str = "build = program(n, acc) do \
                       if n < 1 then acc else build(n - 1, Link(n, acc)) done \
                     done ";

fn interp_error(src: &str) -> InterpError {
    let checked = goat_checker::check(src).expect("type-checks");
    let program = goat_mir::mono(&checked).expect("monomorphizes");
    assert_eq!(goat_mir::verify(&program), Ok(()), "{src}");
    interp::run(&program).expect_err("the program should trap")
}

fn wasm_error(src: &str) -> String {
    let wasm = goat::compile(src).expect("compiles");
    match goat_cli::run(&wasm) {
        Ok(_) => panic!("the program should trap: {src}"),
        Err(error) => error,
    }
}

fn assert_traps(src: &str, message: &str) {
    assert_eq!(
        interp_error(src),
        InterpError::Trap(message.into()),
        "{src}"
    );
    assert_eq!(wasm_error(src), format!("trap: {message}"), "{src}");
}

#[test]
fn link_puts_an_item_in_front() {
    assert_eq!(run("print(link(0, [1, 2]))"), "[0, 1, 2]");
    assert_eq!(run("print(link(\"a\", []))"), "[\"a\"]");
    assert_eq!(run("print(link([1], [[2]]))"), "[[1], [2]]");
}

#[test]
fn add_puts_an_item_at_the_end() {
    assert_eq!(run("print(add([1, 2], 3))"), "[1, 2, 3]");
    assert_eq!(run("print(add([], 1))"), "[1]");
    assert_eq!(run("print(add([\"a\"], \"b\"))"), "[\"a\", \"b\"]");
}

#[test]
fn join_appends_two_lists() {
    assert_eq!(run("print(join([1, 2], [3, 4]))"), "[1, 2, 3, 4]");
    assert_eq!(run("print(join([], [3]))"), "[3]");
    assert_eq!(run("print(join([1], []))"), "[1]");
    assert_eq!(run("print(length(join([], [])))"), "0");
    assert_eq!(run("print(join([\"a\"], [\"b\"]))"), "[\"a\", \"b\"]");
}

#[test]
fn length_counts_items() {
    assert_eq!(run("length([])"), "0");
    assert_eq!(run("length([5])"), "1");
    assert_eq!(run("length([1, 2, 3])"), "3");
    assert_eq!(run("length([\"a\", \"b\"])"), "2");
    assert_eq!(run("length([[1, 2], []])"), "2");
}

#[test]
fn item_counts_from_one() {
    assert_eq!(run("item([10, 20, 30], 1)"), "10");
    assert_eq!(run("item([10, 20, 30], 2)"), "20");
    assert_eq!(run("item([10, 20, 30], 3)"), "30");
    assert_eq!(run("item([\"a\", \"b\"], 2)"), "b");
    assert_eq!(run("item([true], 1)"), "true");
}

#[test]
fn first_and_rest_take_a_list_apart() {
    assert_eq!(run("first([7, 8, 9])"), "7");
    assert_eq!(run("print(rest([7, 8, 9]))"), "[8, 9]");
    assert_eq!(run("print(rest([7]))"), "[]");
    assert_eq!(run("first(rest(rest([7, 8, 9])))"), "9");
    assert_eq!(run("first([\"x\"])"), "x");
}

#[test]
fn each_runs_the_function_on_every_item_in_order() {
    assert_eq!(run("each([1, 2, 3], print)"), "1\n2\n3");
    assert_eq!(run("each([\"a\", \"b\"], print)"), "a\nb");
    assert_eq!(run("each([], print)"), "");
    let doubled = format!("{DOUBLE} each([1, 2, 3], program(n) do print(double(n)) done)");
    assert_eq!(run(&doubled), "2\n4\n6");
    let src = "a = each([1, 2], print)\nb = print(0)\nc = each([3], print)";
    assert_eq!(run(src), "1\n2\n0\n3");
}

#[test]
fn change_each_transforms_every_item() {
    let src = format!("{DOUBLE} print(change_each([1, 2, 3], double))");
    assert_eq!(run(&src), "[2, 4, 6]");
    assert_eq!(
        run("print(change_each([1, 5], program(n) do n > 2 done))"),
        "[false, true]"
    );
    assert_eq!(run("print(change_each([], print))"), "[]");
}

#[test]
fn keep_filters_in_order() {
    let src = format!("{BIG} print(keep([1, 5, 2, 7, 3], big))");
    assert_eq!(run(&src), "[5, 7, 3]");
    let src = format!("{BIG} print(keep([1, 2], big))");
    assert_eq!(run(&src), "[]");
    assert_eq!(
        run("print(keep([\"a\", \"b\", \"a\"], program(s) do s == \"a\" done))"),
        "[\"a\", \"a\"]"
    );
}

#[test]
fn count_counts_the_items_that_pass() {
    let src = format!("{BIG} count([1, 5, 2, 7, 3], big)");
    assert_eq!(run(&src), "3");
    assert_eq!(run(&format!("{BIG} count([], big)")), "0");
}

#[test]
fn sum_biggest_and_smallest() {
    assert_eq!(run("sum([1, 2, 3, 4])"), "10");
    assert_eq!(run("sum([])"), "0");
    assert_eq!(run("sum([0.5, 0.25])"), "0.75");
    assert_eq!(run("biggest([3, 9, 2])"), "9");
    assert_eq!(run("biggest([4])"), "4");
    assert_eq!(run("biggest([-3, -9])"), "-3");
    assert_eq!(run("smallest([3, 9, 2])"), "2");
    assert_eq!(run("smallest([4])"), "4");
    assert_eq!(run("smallest([-3, -9])"), "-9");
}

#[test]
fn has_compares_with_equals() {
    assert_eq!(run("has([1, 2, 3], 2)"), "true");
    assert_eq!(run("has([1, 2, 3], 4)"), "false");
    assert_eq!(run("has([], 1)"), "false");
    assert_eq!(run("has([\"a\", \"b\"], \"b\")"), "true");
    assert_eq!(run("has([\"a\", \"b\"], \"c\")"), "false");
    assert_eq!(run("has([{x: 1}, {x: 2}], {x: 2})"), "true");
    assert_eq!(run("has([[1], [2, 3]], [2, 3])"), "true");
    assert_eq!(run("has([[1], [2, 3]], [2])"), "false");
}

#[test]
fn reverse_flips_a_list() {
    assert_eq!(run("print(reverse([1, 2, 3]))"), "[3, 2, 1]");
    assert_eq!(run("print(reverse([]))"), "[]");
    assert_eq!(run("print(reverse([\"a\"]))"), "[\"a\"]");
}

#[test]
fn sort_orders_numbers_smallest_first() {
    assert_eq!(run("print(sort([3, 1, 2]))"), "[1, 2, 3]");
    assert_eq!(run("print(sort([5, 4, 3, 2, 1]))"), "[1, 2, 3, 4, 5]");
    assert_eq!(run("print(sort([1, 2, 3]))"), "[1, 2, 3]");
    assert_eq!(run("print(sort([2, 1, 2, 1]))"), "[1, 1, 2, 2]");
    assert_eq!(run("print(sort([-1, 0.5, -3]))"), "[-3, -1, 0.5]");
    assert_eq!(run("print(sort([]))"), "[]");
    assert_eq!(run("print(sort([7]))"), "[7]");
}

#[test]
fn the_functions_compose() {
    let src = format!(
        "{DOUBLE} {BIG} \
         print(sort(change_each(keep(join([5, 1], [4, 3]), big), double)))"
    );
    assert_eq!(run(&src), "[6, 8, 10]");
    assert_eq!(run("item(reverse(add(link(0, [1, 2]), 3)), 1)"), "3");
    assert_eq!(run("length(rest(rest(join([1], [2, 3]))))"), "1");
}

#[test]
fn long_lists_do_not_overflow_the_stack() {
    let n = 100000;
    let cases = [
        (format!("length(build({n}, []))"), "100000"),
        (format!("sum(build({n}, []))"), "5000050000"),
        (format!("biggest(build({n}, []))"), "100000"),
        (format!("smallest(build({n}, []))"), "1"),
        (format!("first(reverse(build({n}, [])))"), "100000"),
        (format!("length(add(build({n}, []), 0))"), "100001"),
        (format!("item(add(build({n}, []), 0), {})", n + 1), "0"),
        (
            format!("length(join(build({n}, []), build({n}, [])))"),
            "200000",
        ),
        (
            format!("length(keep(build({n}, []), program(k) do k > 50000 done))"),
            "50000",
        ),
        (
            format!("count(build({n}, []), program(k) do k > 50000 done)"),
            "50000",
        ),
        (
            format!("sum(change_each(build({n}, []), program(k) do 1 done))"),
            "100000",
        ),
        (format!("has(build({n}, []), {n})"), "true"),
        (format!("has(build({n}, []), 0)"), "false"),
        (format!("item(build({n}, []), {n})"), "100000"),
    ];
    for (body, expected) in cases {
        assert_eq!(run(&format!("{BUILD} {body}")), expected, "{body}");
    }
}

#[test]
fn each_walks_a_long_list_in_constant_stack() {
    let src = format!("{BUILD} each(build(20000, []), program(k) do 0 done)");
    assert_eq!(run(&src), "");
}

#[test]
fn sort_handles_a_few_hundred_items() {
    let src = format!(
        "{BUILD} xs = sort(reverse(build(400, []))) \
         first(xs) + item(xs, 200) + item(xs, 400) + length(xs)"
    );
    assert_eq!(run(&src), "1001");
}

#[test]
fn an_empty_list_has_no_first_or_rest() {
    assert_traps("first([]) + 1", "first of an empty list");
    assert_traps("rest([]) == []", "rest of an empty list");
    assert_traps("first(rest([1])) + 1", "first of an empty list");
    assert_traps(
        "first(keep([1], program(n) do n > 1 done)) + 1",
        "first of an empty list",
    );
}

#[test]
fn item_outside_the_list_is_a_trap() {
    let message = "item past the end of the list";
    assert_traps("item([1, 2], 3)", message);
    assert_traps("item([], 1)", message);
    assert_traps("item([1, 2], 0)", message);
    assert_traps("item([1, 2], -1)", message);
    assert_traps("item([1, 2], 1.5)", message);
}

#[test]
fn biggest_and_smallest_of_nothing_are_traps() {
    assert_traps("biggest([])", "biggest of an empty list");
    assert_traps("smallest([])", "smallest of an empty list");
}

#[test]
fn a_trap_after_output_still_ends_the_program() {
    assert_traps("shown = print(1)\nfirst([]) + 1", "first of an empty list");
}

#[test]
fn trap_is_only_taken_when_reached() {
    assert_eq!(run("if 1 < 2 then 5 else trap(\"no\") done"), "5");
    assert_eq!(run("if 2 < 1 then trap(\"no\") else 6 done"), "6");
    assert_eq!(
        run("match Circle(2) do Circle(r) then r Square(s) then trap(\"no\") done"),
        "2"
    );
}

#[test]
fn a_user_written_trap_stops_the_program() {
    assert_traps("trap(\"boom\") + 1", "boom");
    assert_traps(
        "f = program(n) do if n > 1 then trap(\"too big\") else n done done f(2)",
        "too big",
    );
}

#[test]
fn unused_list_functions_add_no_code() {
    let with = goat_checker::check("1 + 2").unwrap();
    let without = goat_checker::check_with_prelude("", "1 + 2").unwrap();
    assert_eq!(
        goat_mir::mono(&with).unwrap().funcs.len(),
        goat_mir::mono(&without).unwrap().funcs.len()
    );
}

#[test]
fn a_user_may_replace_a_list_function() {
    let src = "length = program(xs) do 42 done length([1, 2])";
    assert_eq!(run(src), "42");
    let src = "item = program(xs, n) do n done item([1], 0)";
    assert_eq!(run(src), "0");
}
