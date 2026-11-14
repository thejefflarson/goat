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
        "`x` is a `Number` in `ball`, and `{...ball, x: …}` keeps each field's type, so `x` can't become a `String`. To keep the text too, give it its own field, like `x_text`."
    );
}

#[test]
fn a_type_change_names_the_record_being_copied_when_it_has_no_name() {
    let message = first_error("{...{x: 1}, x: true}");
    assert!(
        message.starts_with("`x` is a `Number` in the record being copied, and"),
        "{message}"
    );
    assert!(message.contains("can't become a `Bool`"), "{message}");
}

#[test]
fn a_type_change_through_an_unknown_record_shows_no_presence_mark() {
    let message = first_error("set_x = program(r) do {...r, x: 1} done\nset_x({x: \"hi\"})");
    assert!(!message.contains('?'), "{message}");
}

#[test]
fn separate_updates_of_one_label_keep_their_own_types() {
    let source = "a = program(r) do {...r, x: 1} done\nb = program(r) do {...r, x: true} done\n{a: a({y: 0}), b: b({y: 0})}";
    assert_eq!(
        type_of(source),
        "{a: {x: Number, y: Number}, b: {x: Bool, y: Number}}"
    );
}

#[test]
fn a_rest_pattern_cannot_take_its_label_back() {
    let source = "f = program(p) do {x, ...r} = p if true then r else {x: 1} done done\n1";
    assert!(first_error(source).contains("was taken out of this record"));
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
    let checked = check_with_prelude("", "program(r) do {...r, x: 1} done").unwrap();
    let ty = checked.typed.root_ty;
    assert!(ty.exact().to_string().contains("x?: Int"), "{}", ty.exact());
    assert!(!ty.to_string().contains('?'), "{ty}");
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
fn a_spread_that_stores_its_own_base_is_a_plain_error() {
    let message = first_error("k = program(s) do {...s, next: s} done\nk({a: 1})");
    assert!(
        message.contains("this record would have to contain itself"),
        "{message}"
    );
}
