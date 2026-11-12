//! `self` marks a method; a record literal's methods share one receiver type,
//! and `.` calls methods only (ADR 0034).

use goat_checker::check_with_prelude;
use std::time::{Duration, Instant};

fn type_of(source: &str) -> String {
    match check_with_prelude("", source) {
        Ok(checked) => checked.typed.root_ty.to_string(),
        Err(errors) => panic!("should check: {source}\n{errors:?}"),
    }
}

/// The first error's message and the source it covers.
fn first_diagnostic(source: &str) -> (String, String) {
    let Err(errors) = check_with_prelude("", source) else {
        panic!("should not check: {source}")
    };
    let span = errors[0].span;
    (
        errors[0].message.clone(),
        source[span.start..span.end].to_string(),
    )
}

const THREE_METHOD_MODEL: &str = "init = program() do {x: 0, y: 1,
        update: program(self) do {...self, x: self.x + 1} done,
        nudge: program(self) do {...self, y: self.y + 1} done,
        draw: program(self) do self.x done} done
    run = program(m, n) do if n == 0 then m else run(m.update(), n - 1) done done";

#[test]
fn a_chain_of_three_methods_checks() {
    let source = format!("{THREE_METHOD_MODEL}\nm = init()\nm.nudge().update().draw()");
    assert_eq!(type_of(&source), "Number");
}

#[test]
fn a_looped_three_method_model_checks() {
    let source = format!("{THREE_METHOD_MODEL}\nm = run(init(), 4)\nm.draw()");
    assert_eq!(type_of(&source), "Number");
}

#[test]
fn a_method_result_is_the_receivers_own_type() {
    let source = format!("{THREE_METHOD_MODEL}\nm = init()\nm.nudge().update().x + m.y");
    assert_eq!(type_of(&source), "Number");
}

#[test]
fn checking_the_three_method_model_stays_within_a_small_budget() {
    let source = format!("{THREE_METHOD_MODEL}\nm = run(init(), 4)\nm.nudge().update().draw()");
    let start = Instant::now();
    check_with_prelude("", &source).expect("checks");
    assert!(
        start.elapsed() < Duration::from_secs(2),
        "{:?}",
        start.elapsed()
    );
}

#[test]
fn an_extension_of_a_record_with_methods_calls_them_at_its_own_type() {
    let source = "ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}
        big = {...ball, size: 10}
        big.moved().size";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_method_in_a_spread_literal_is_a_method() {
    let source = "ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}
        other = {...ball, again: program(self) do self.x done}
        other.again()";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_dot_call_on_a_plain_function_suggests_the_take() {
    let source = "tools = {double: program(n) do n * 2 done}\ntools.double(5)";
    assert_eq!(
        first_diagnostic(source),
        (
            "`double` has no `self`, so `tools.double(5)` can't hand it `tools`. Call it with `tools::double(5)`. \
             If `double` is meant to work on `tools`, make it a method by writing `self` first: `program(self, n)`."
                .to_string(),
            "tools.double(5)".to_string()
        )
    );
}

#[test]
fn a_dot_call_on_a_plain_function_of_a_parameter_names_the_field_in_a_mismatch() {
    let source = "call = program(r) do r.f(1) done
        call({f: program(a) do a done})";
    let (message, _) = first_diagnostic(source);
    assert_eq!(
        message,
        "`f` is a method in one record and a plain function in the other, so they don't have the same shape. \
         Start both with `self`, or neither."
    );
}

#[test]
fn a_list_of_a_method_and_a_plain_function_says_so() {
    let source = "xs = [{f: program(self) do 1 done}, {f: program(a) do 1 done}]\nlength(xs)";
    let Err(errors) = check_with_prelude(goat_checker::PRELUDE, source) else {
        panic!("should not check: {source}")
    };
    assert_eq!(
        errors[0].message,
        "`f` is a method in one record and a plain function in the other, so they don't have the same shape. \
         Start both with `self`, or neither."
    );
}

#[test]
fn self_outside_a_record_says_where_it_goes() {
    let message = "`self` only works in a function written right inside a record, like `{moved: program(self) do … done}`.";
    assert_eq!(
        first_diagnostic("add = program(self, n) do n done\n1"),
        (message.to_string(), "self".to_string())
    );
    assert_eq!(
        first_diagnostic("x = self.y\n1"),
        (message.to_string(), "self".to_string())
    );
    assert_eq!(
        first_diagnostic("r = {f: program(a) do program(self) do a done done}\n1"),
        (message.to_string(), "self".to_string())
    );
}

#[test]
fn self_not_first_says_to_move_it() {
    assert_eq!(
        first_diagnostic("r = {moved: program(dt, self) do dt done}\n1"),
        (
            "`self` has to be the first parameter: `program(self, dt)`.".to_string(),
            "self".to_string()
        )
    );
}

#[test]
fn a_take_on_a_method_steers_to_the_dot() {
    let source = "ball = {x: 1, moved: program(self) do self.x done}\nball::moved()";
    assert_eq!(
        first_diagnostic(source),
        (
            "`moved` has `self`, so call it with a dot: `ball.moved()`. \
             `::` is for functions without `self`, like `math::double(5)`."
                .to_string(),
            "ball::moved".to_string()
        )
    );
}

#[test]
fn a_take_on_a_method_names_the_records_own_tool_as_the_example() {
    let source = "ball = {pos: 1, x: program(self) do self.pos done, \
                  clamp: program(v) do if v > 2 then 2 else v done done}\n\
                  ball::x()";
    assert_eq!(
        first_diagnostic(source),
        (
            "`x` has `self`, so call it with a dot: `ball.x()`. \
             `::` is for functions without `self`, like `ball::clamp(…)`."
                .to_string(),
            "ball::x".to_string()
        )
    );
}

#[test]
fn a_dot_on_a_records_tool_steers_to_the_double_colon() {
    let source = "ball = {pos: 1, x: program(self) do self.pos done, \
                  clamp: program(v) do if v > 2 then 2 else v done done}\n\
                  ball.clamp(3)";
    assert_eq!(
        first_diagnostic(source),
        (
            "`clamp` has no `self`, so `ball.clamp(3)` can't hand it `ball`. Call it with `ball::clamp(3)`. \
             If `clamp` is meant to work on `ball`, make it a method by writing `self` first: `program(self, v)`."
                .to_string(),
            "ball.clamp(3)".to_string()
        )
    );
}

#[test]
fn a_record_of_tools_is_called_with_a_double_colon() {
    let source = "math = {clamp: program(x, lo, hi) do if x < lo then lo else if x > hi then hi else x done done done, \
                  double: program(n) do n * 2 done}\n\
                  math::clamp(12, 0, 10) + math::double(5)";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn methods_calling_siblings_share_the_receiver() {
    let methods: Vec<String> = (0..5)
        .map(|i| format!("m{i}: program(self) do self.m{}() done", i + 1))
        .collect();
    let source = format!(
        "r = {{x: 0, {}, m5: program(self) do {{...self, x: self.x + 1}} done}}\nr.m0().x",
        methods.join(", ")
    );
    let start = Instant::now();
    assert_eq!(type_of(&source), "Number");
    assert!(start.elapsed() < Duration::from_secs(5));
}

#[test]
fn a_sibling_call_in_one_method_and_an_update_in_another_agree_on_the_type() {
    let source = "ball = {x: 1,
        moved: program(self) do {...self, x: self.x + 1} done,
        twice: program(self) do self.moved().x + self.x done}
        ball.moved().twice()";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn an_extension_of_a_record_whose_methods_call_siblings_calls_them_at_its_own_type() {
    let source = "ball = {x: 1,
        moved: program(self) do {...self, x: self.x + 1} done,
        again: program(self) do self.moved() done}
        big = {...ball, size: 10}
        big.again().size";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_method_hands_self_to_a_function_that_reads_a_field() {
    let source = "read_x = program(r) do r.x done
        ball = {x: 1, get: program(self) do read_x(self) done}
        ball.get()";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_helper_inside_a_method_keeps_the_type_of_the_field_it_reads() {
    let source = "ball = {x: \"far\", get: program(self) do
            helper = program() do self.x done
            helper() * 2
        done}
        ball.get()";
    let (message, _) = first_diagnostic(source);
    assert!(message.contains("`String`"), "{message}");
}

#[test]
fn a_record_literal_inside_a_method_has_its_own_receiver() {
    let source = "outer = {n: 1, make: program(self) do
            {m: self.n, get: program(self) do self.m done}
        done}
        outer.make().get()";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_method_that_builds_a_record_without_self_drops_the_methods() {
    let source = "ball = {x: 1, where: program(self) do self.x done,
        moved: program(self) do {x: self.x + 1} done}
        ball.moved().where()";
    assert_eq!(
        first_diagnostic(source),
        (
            "`ball.moved()` gave back a record with no `where`. If `moved` builds a new record, start it with `...self` so the methods come along."
                .to_string(),
            "ball.moved().where()".to_string()
        )
    );
}

#[test]
fn no_message_shows_a_recursive_type_or_a_raw_variable() {
    for source in [
        "ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}\nball.x(1)",
        "ball = {x: 1, moved: program(self) do {...self, x: \"hi\"} done}\nball.moved()",
        "ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}\nball.moved(ball)",
    ] {
        let (message, _) = first_diagnostic(source);
        assert!(!message.contains('μ'), "{message}");
        assert!(!message.contains("`t"), "{message}");
    }
}

#[test]
fn a_method_that_needs_a_missing_field_rejects_the_record() {
    let source = "ball = {x: 1, moved: program(self) do self.z done}\nball.moved()";
    let (message, _) = first_diagnostic(source);
    assert!(message.contains("`z`"), "{message}");
}
