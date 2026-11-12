//! A spread updates a field the record has, extends with one it lacks, and
//! never changes a field's type (ADR 0033).

use goat_checker::check_with_prelude;

fn type_of(source: &str) -> String {
    match check_with_prelude("", source) {
        Ok(checked) => checked.typed.root_ty.to_string(),
        Err(errors) => panic!("should check: {source}\n{errors:?}"),
    }
}

fn first_error(source: &str) -> String {
    match check_with_prelude("", source) {
        Ok(_) => panic!("should not check: {source}"),
        Err(errors) => errors[0].message.clone(),
    }
}

#[test]
fn an_update_keeps_the_records_type() {
    assert_eq!(
        type_of("ball = {x: 1, y: 2}\n{...ball, x: 5}"),
        "{x: Number, y: Number}"
    );
}

#[test]
fn a_spread_adds_a_field_the_record_lacks() {
    assert_eq!(
        type_of("ball = {x: 1}\n{...ball, y: true}"),
        "{x: Number, y: Bool}"
    );
}

#[test]
fn an_update_may_not_change_a_fields_type() {
    let message = first_error("ball = {x: 1}\n{...ball, x: \"hi\"}");
    assert_eq!(
        message,
        "`x` is `Number` in this record, and `...` keeps a field's type, so it can't become `String`"
    );
}

#[test]
fn a_spread_over_an_unknown_record_sets_the_field_either_way() {
    let source = "set_x = program(r) do {...r, x: 1} done\n";
    assert_eq!(
        type_of(&format!("{source}set_x({{y: true}})")),
        "{x: Number, y: Bool}"
    );
    assert_eq!(
        type_of(&format!("{source}set_x({{x: 5, y: true}})")),
        "{x: Number, y: Bool}"
    );
}

#[test]
fn the_inferred_type_marks_the_field_optional() {
    let ty = type_of("program(r) do {...r, x: 1} done");
    assert!(ty.contains("x?: Number"), "{ty}");
}

#[test]
fn a_spread_over_an_unknown_record_still_rejects_a_type_change() {
    let source = "set_x = program(r) do {...r, x: 1} done\nset_x({x: \"hi\"})";
    let message = first_error(source);
    assert!(message.contains("mismatch"), "{message}");
}

#[test]
fn a_recursive_call_that_spreads_its_parameter_checks() {
    assert_eq!(
        type_of("go = program(s) do go({...s, stop: true}) done  1"),
        "Number"
    );
}

#[test]
fn an_update_method_returns_its_receivers_type() {
    let source = "ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}\nball.moved().moved().x";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_rest_pattern_over_an_updated_record_checks() {
    let source = "r = {...{x: 1, y: 2}, x: 3}\n{x, ...rest} = r\nrest";
    assert_eq!(type_of(source), "{y: Number}");
}

#[test]
fn three_methods_whose_rows_differ_check() {
    let source = "init = program() do {x: 0, y: 1, update: program(self) do {...self, x: self.x + 1} done, nudge: program(self) do {...self, y: self.y + 1} done, draw: program(self) do self.x + self.y done} done
        run = program(m, n) do if n == 0 then m else run(m.nudge().update(), n - 1) done done
        m = run(init(), 2)
        m.draw()";
    assert_eq!(type_of(source), "Number");
}
