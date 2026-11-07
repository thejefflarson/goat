//! The interactive contract (ADR 0015): a program that binds `init`, `update`
//! and `draw` must give them compatible types, and each failure points at the
//! binding that broke it.

use goat_checker::{Checked, GoatError, check};

const UPDATE: &str = "update = program(model, event) do
  match event do
    Tick(dt) then {...model, x: model.x + dt}
    Reset then {...model, x: 0}
  done
done
";

const DRAW: &str = "draw = program(model) do [Circle(model.x)] done\n";

fn interactive(init: &str, update: &str, draw: &str) -> String {
    format!("init = {init}\n{update}{draw}")
}

fn checks(source: &str) -> Checked {
    check(source).unwrap_or_else(|e| panic!("should check: {source}\n{e:?}"))
}

fn errors_of(source: &str) -> Vec<GoatError> {
    match check(source) {
        Ok(_) => panic!("should not check: {source}"),
        Err(errors) => errors,
    }
}

/// The one error, its message and the source text its span covers.
fn the_error(source: &str) -> (String, String) {
    let errors = errors_of(source);
    assert_eq!(errors.len(), 1, "{errors:?}");
    let span = errors[0].span;
    (
        errors[0].message.clone(),
        source[span.start..span.end].to_string(),
    )
}

#[test]
fn a_program_with_the_three_bindings_is_interactive() {
    let checked = checks(&interactive("{x: 0, y: 0}", UPDATE, DRAW));
    assert!(checked.interactive.is_some());
}

#[test]
fn a_program_without_them_is_not() {
    assert!(checks("1 + 2").interactive.is_none());
    assert!(
        checks("init = {x: 0}\ndraw = program(m) do [Circle(1)] done\n1")
            .interactive
            .is_none()
    );
}

#[test]
fn rebinding_a_name_shadows_it_and_the_program_runs_once() {
    let source = format!("{}init = 5\n", interactive("{x: 0}", UPDATE, DRAW));
    assert!(checks(&source).interactive.is_none());
}

#[test]
fn the_models_of_update_and_draw_are_unified_with_init() {
    let checked = checks(&interactive("{x: 0, y: 0}", UPDATE, DRAW));
    let model = "{x: Number, y: Number}";
    let ty = checked.typed.root_ty.to_string();
    assert!(ty.contains(&format!("init: {model}")), "{ty}");
    assert!(ty.contains(&format!("({model}, ")), "{ty}");
}

#[test]
fn init_must_be_a_record() {
    let (message, text) = the_error(&interactive("5", UPDATE, DRAW));
    assert!(message.starts_with("init must be a record"), "{message}");
    assert_eq!(text, "5");
}

#[test]
fn update_must_take_a_model_and_an_event() {
    let update = "update = program(model) do model done\n";
    let (message, text) = the_error(&interactive("{x: 0}", update, DRAW));
    assert!(
        message.starts_with("update must be a function of"),
        "{message}"
    );
    assert!(text.starts_with("program(model)"), "{text}");
}

#[test]
fn update_must_return_the_models_type() {
    let update = "update = program(model, event) do
  match event do Tick(dt) then {x: \"no\"} done
done
";
    let (message, text) = the_error(&interactive("{x: 0}", update, DRAW));
    assert!(message.starts_with("update's"), "{message}");
    assert!(text.starts_with("program(model, event)"), "{text}");
}

#[test]
fn updates_model_must_match_init() {
    let update = "update = program(model, event) do
  match event do Tick(dt) then {...model, z: dt} done
done
";
    let (message, _) = the_error(&interactive("{x: 0}", update, DRAW));
    assert!(message.starts_with("update's"), "{message}");
}

#[test]
fn the_event_must_be_a_variant() {
    let update = "update = program(model, event) do {...model, x: event + 1} done\n";
    let source = interactive("{x: 0}", update, DRAW);
    let errors = errors_of(&source);
    let error = errors
        .iter()
        .find(|e| e.message.contains("must be an event"))
        .expect("an event error");
    assert!(source[error.span.start..].starts_with("program(model, event)"));
}

#[test]
fn draw_must_take_the_model() {
    let draw = "draw = program() do [Circle(1)] done\n";
    let (message, text) = the_error(&interactive("{x: 0}", UPDATE, draw));
    assert!(message.starts_with("draw must be a function"), "{message}");
    assert!(text.starts_with("program()"), "{text}");
}

#[test]
fn draw_must_return_a_list_of_variants() {
    for body in ["1", "[1, 2]", "Circle(1)"] {
        let draw = format!("draw = program(model) do {body} done\n");
        let (message, text) = the_error(&interactive("{x: 0}", UPDATE, &draw));
        assert!(message.starts_with("draw must return a list"), "{message}");
        assert!(text.starts_with("program(model)"), "{text}");
    }
}

#[test]
fn draws_model_must_match_init() {
    let draw = "draw = program(model) do [Circle(model.y)] done\n";
    let (message, _) = the_error(&interactive("{x: 0}", UPDATE, draw));
    assert!(message.starts_with("draw's model"), "{message}");
}

#[test]
fn an_empty_picture_is_a_list_of_shapes() {
    checks(&interactive(
        "{x: 0}",
        UPDATE,
        "draw = program(model) do [] done\n",
    ));
}
