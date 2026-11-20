//! An `Int` widens to a `Float` where two scalars must agree (ADR 0040),
//! end to end: each program runs through the interpreter and through wasm,
//! which must print the same lines.

#[allow(dead_code)]
mod support;

use support::run;

#[test]
fn a_generic_function_takes_an_int_and_a_float() {
    let add = "f = program(a, b) do a + b done\n";
    assert_eq!(run(&format!("{add}print(f(7 // 2, 2.5))")), "5.5");
    assert_eq!(run(&format!("{add}print(f(2.5, 7 // 2))")), "5.5");
    assert_eq!(run(&format!("{add}print(f(truncate(3.7), 2.5))")), "5.5");
    assert_eq!(run(&format!("{add}print(f(2.5, truncate(3.7)))")), "5.5");
    assert_eq!(
        run(&format!("{add}print(f(truncate(3.7), truncate(4.2)))")),
        "7"
    );
}

#[test]
fn the_branches_of_an_if_widen() {
    let src = |branches: &str| format!("c = true\nprint(if c then {branches} done)");
    assert_eq!(run(&src("7 // 2 else 2.5")), "3");
    assert_eq!(run(&src("2.5 else 7 // 2")), "2.5");
    let int = "truncate(3.7)";
    assert_eq!(run(&src(&format!("{int} else 2.5"))), "3");
    let other = "c = false\nprint(if c then truncate(3.7) else 2.5 done)";
    assert_eq!(run(other), "2.5");
}

#[test]
fn a_widened_branch_ends_a_tail_call_correctly() {
    let src = "count = program(n, acc) do
  if n == 0 then acc else count(n - 1, acc + 1) done
done
f = program(n) do if n == 0 then truncate(2.0) else 0.5 done done
print(count(3, f(0)) + f(1))";
    assert_eq!(run(src), "5.5");
}

#[test]
fn the_arms_of_a_match_widen() {
    let one = "print(match [truncate(3.7)] do [x, ...r] then x [] then 2.5 done)";
    assert_eq!(run(one), "3");
    let other = "print(match [] do [x, ...r] then truncate(3.7) [] then 2.5 done)";
    assert_eq!(run(other), "2.5");
}

#[test]
fn the_elements_of_a_list_literal_widen() {
    assert_eq!(run("i = truncate(3.7)\nprint([i, 2.5])"), "[3, 2.5]");
    assert_eq!(run("i = truncate(3.7)\nprint([2.5, i])"), "[2.5, 3]");
    assert_eq!(run("i = truncate(3.7)\nprint(sum([2.5, i, 4]))"), "9.5");
    assert_eq!(run("i = truncate(3.7)\nprint(sum([i, 4]))"), "7");
    assert_eq!(
        run("xs = [1.5, 2.5]\nprint(sum(Link(truncate(3.7), xs)))"),
        "7"
    );
}

#[test]
fn comparisons_widen() {
    assert_eq!(run("print(truncate(3.7) == 3.0)"), "true");
    assert_eq!(run("print(truncate(3.7) < 3.5)"), "true");
    assert_eq!(run("print(2.5 < truncate(3.7))"), "true");
}

#[test]
fn an_argument_widens_to_a_float_parameter() {
    assert_eq!(
        run("g = program(x) do sqrt(x) done\nprint(g(truncate(9.5)))"),
        "3"
    );
    assert_eq!(
        run("h = program(x) do x * 1.5 done\nprint(h(truncate(3.7)))"),
        "4.5"
    );
}

#[test]
fn a_recursive_group_widens_through_both_members() {
    let src = "f = program(a, n) do if n == 0 then a else g(a, n - 1) + 1.5 done done
g = program(b, n) do if n == 0 then b else f(b, n - 1) done done
print(f(truncate(3.7), 3))";
    assert_eq!(run(src), "6");
}

#[test]
fn the_order_of_the_uses_does_not_change_the_answer() {
    let a = "n = 2 * 3\nprint({a: n + 1.5, b: n // 2})";
    let b = "n = 2 * 3\nprint({b: n // 2, a: n + 1.5})";
    assert_eq!(run(a), "{a: 7.5, b: 3}");
    assert_eq!(run(b), "{a: 7.5, b: 3}");
}
