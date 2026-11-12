//! A function that calls a method on its own parameter has a record type that
//! mentions itself: `p.moved()` makes `p : {moved: (P) -> … | ρ}`. The
//! checker ties that knot when the cycle runs through a record field and a
//! function type, and keeps rejecting every other cycle.

use goat_checker::check_with_prelude;

fn error_of(source: &str) -> Option<String> {
    check_with_prelude("", source)
        .err()
        .map(|errors| errors[0].message.clone())
}

#[test]
fn a_method_on_a_parameter_checks() {
    assert_eq!(error_of("step = program(p) do p.moved() done  1"), None);
}

#[test]
fn two_methods_on_one_parameter_check() {
    let source = "f = program(x) do x.do_thing(); x.do_another(5) done  1";
    assert_eq!(error_of(source), None);
}

#[test]
fn a_method_that_returns_the_receiver_checks() {
    let source = "ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}
        step = program(p) do p.moved() done
        step(ball).x";
    assert_eq!(error_of(source), None);
}

#[test]
fn a_call_result_is_a_receiver() {
    let source = "ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}
        b2 = ball.moved()
        b2.moved().x";
    assert_eq!(error_of(source), None);
}

#[test]
fn self_application_stays_rejected() {
    let message = error_of("f = program(x) do x(x) done  1").expect("should not check");
    assert!(message.contains("infinite type"), "{message}");
}

#[test]
fn a_cycle_through_a_field_alone_stays_rejected() {
    let source = "f = program(x) do if true then x else {a: x} done done  1";
    let message = error_of(source).expect("should not check");
    assert!(message.contains("infinite"), "{message}");
}

#[test]
fn a_cycle_through_a_function_alone_stays_rejected() {
    let source = "f = program(x) do if true then x else program() do x done done done  1";
    let message = error_of(source).expect("should not check");
    assert!(message.contains("infinite"), "{message}");
}

#[test]
fn pure_extension_spread_recursion_stays_rejected() {
    let message =
        error_of("go = program(s) do go({...s, stop: true}) done  1").expect("should not check");
    assert!(
        message.contains("adds field `stop`") && message.contains("grow without bound"),
        "{message}"
    );
}

#[test]
fn a_wrong_shaped_method_names_no_type_variable() {
    let source = "step = program(p) do q = p.moved(); q.moved() done
        ball = {x: 1, moved: program(self) do self.x done}
        step(ball)";
    let message = error_of(source).expect("should not check");
    assert!(message.contains("{moved: …}"), "{message}");
    assert!(!message.contains('μ'), "{message}");
    assert!(!message.contains("t4"), "{message}");
}

const TWO_METHOD_MODEL: &str =
    "init = program() do {x: 0, speed: 3, update: program(self) do {...self, x: self.x + self.speed} done, draw: program(self) do self.x done} done
     run = program(m, n) do if n == 0 then m else run(m.update(), n - 1) done done
     m = run(init(), 4)";

#[test]
fn two_methods_whose_rows_differ_check() {
    let source = format!("{TWO_METHOD_MODEL}\nm.draw()");
    assert_eq!(error_of(&source), None);
}

#[test]
fn three_methods_whose_rows_differ_finish_with_a_plain_answer() {
    let source = "init = program() do {x: 0, y: 1, update: program(self) do {...self, x: self.x + 1} done, nudge: program(self) do {...self, y: self.y + 1, x: self.x} done, draw: program(self) do self.x + self.y done} done
        run = program(m, n) do if n == 0 then m else run(m.update(), n - 1) done done
        m = run(init(), 2)
        m.nudge().draw()";
    if let Some(message) = error_of(source) {
        assert!(!message.contains('μ'), "{message}");
    }
}

#[test]
fn a_missing_method_on_a_two_method_model_is_still_an_error() {
    let source = format!("{TWO_METHOD_MODEL}\nm.undraw()");
    let message = error_of(&source).expect("should not check");
    assert!(!message.contains('μ'), "{message}");
}
