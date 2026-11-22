//! Record arithmetic writes its result into an operand nothing else holds, and
//! a record read only through its fields is released as soon as they are
//! loaded. Every program runs through the interpreter and through wasm under
//! wasmtime, which must print the same lines and leave no heap object live. A
//! shared operand must come out unchanged. Floats print without a `.0`.

#[allow(dead_code)]
mod support;

use support::run;

/// The lines as one program, a `;` after each `print` that another line follows.
fn program(lines: &[&str]) -> String {
    let last = lines.len() - 1;
    lines
        .iter()
        .enumerate()
        .map(|(i, line)| {
            let sep = if i < last && line.starts_with("print(") {
                ";"
            } else {
                ""
            };
            format!("{line}{sep}\n")
        })
        .collect()
}

const PARTICLES: &str = "spawn = program(i, acc) do
  if i == 0 then acc else
    spawn(i - 1, link({p: {x: i * 1.0, y: 0.5}, v: {x: 1.0, y: 2.0}}, acc))
  done
done
step = program(q) do
  p = q.p + q.v
  v = q.v * {x: 0.5, y: 0.5}
  {p: p, v: v}
done";

#[test]
fn a_shared_operand_is_left_unchanged() {
    let src = program(&[
        "a = {x: 1.0, y: 2.0}",
        "b = {x: 3.0, y: 4.0}",
        "c = a + b",
        "print(a)",
        "print(b)",
        "print(c)",
        "print(a + b)",
    ]);
    assert_eq!(
        run(&src),
        "{x: 1, y: 2}\n{x: 3, y: 4}\n{x: 4, y: 6}\n{x: 4, y: 6}"
    );
}

#[test]
fn an_operand_added_to_itself_is_not_overwritten_while_it_is_read() {
    let src = program(&["a = {x: 1.0, y: 2.0}", "print(a + a)", "print(a)"]);
    assert_eq!(run(&src), "{x: 2, y: 4}\n{x: 1, y: 2}");
    let src = "f = program(r) do r * r done\nprint(f({x: 3.0, y: 4.0}))";
    assert_eq!(run(src), "{x: 9, y: 16}");
}

#[test]
fn a_nested_record_sum_keeps_a_shared_inner_record() {
    let src = program(&[
        "inner = {x: 1.0, y: 2.0}",
        "a = {p: inner, n: 1.0}",
        "b = {p: {x: 10.0, y: 20.0}, n: 2.0}",
        "print(a + b)",
        "print(inner)",
        "print(a)",
    ]);
    assert_eq!(
        run(&src),
        "{n: 3, p: {x: 11, y: 22}}\n{x: 1, y: 2}\n{n: 1, p: {x: 1, y: 2}}"
    );
}

#[test]
fn a_step_over_a_list_that_is_kept_leaves_the_list_intact() {
    let src = program(&[
        PARTICLES,
        "ps = spawn(3, [])",
        "a = change_each(ps, step)",
        "b = change_each(ps, step)",
        "print(a == b)",
        "print(ps == a)",
        "print(ps)",
    ]);
    let out = run(&src);
    let lines: Vec<_> = out.lines().collect();
    assert_eq!(&lines[..2], ["true", "false"]);
    assert!(lines[2].contains("p: {x: 1, y: 0.5}"), "{out}");
}

#[test]
fn a_step_over_a_list_that_is_not_kept_computes_the_same_values() {
    let src = program(&[PARTICLES, "print(change_each(spawn(2, []), step))"]);
    assert_eq!(
        run(&src),
        "[{p: {x: 2, y: 2.5}, v: {x: 0.5, y: 1}}, {p: {x: 3, y: 2.5}, v: {x: 0.5, y: 1}}]"
    );
}

#[test]
fn fields_read_in_a_branch_and_outside_it_agree() {
    let src = program(&[
        "pick = program(q, flag) do",
        "  a = q.p + q.v",
        "  if flag then a + q.p else a + q.v done",
        "done",
        "q = {p: {x: 1.0, y: 1.0}, v: {x: 2.0, y: 3.0}}",
        "print(pick(q, true))",
        "print(pick(q, false))",
        "print(q)",
    ]);
    assert_eq!(
        run(&src),
        "{x: 4, y: 5}\n{x: 5, y: 7}\n{p: {x: 1, y: 1}, v: {x: 2, y: 3}}"
    );
}
