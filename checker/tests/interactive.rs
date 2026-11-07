//! The interactive contract (ADR 0015): a program that binds `init`, `update`
//! and `draw` must give them compatible types, and each failure points at the
//! binding that broke it.

use goat_checker::{Checked, GoatError, check};

const UPDATE: &str = "update = program(model, event) do
  match event do
    Tick(dt) then {...model, x: model.x + dt}
    KeyDown(key) then {...model, x: 0}
  done
done
";

const DRAW: &str =
    "draw = program(model) do [Line({x1: 0, y1: 0, x2: model.x, y2: 0, color: \"red\"})] done\n";

/// Declared so the host contract, not name resolution, is what rejects them.
const OFF_CONTRACT_TAGS: &str = "tag Circle tag Frobnicate\n";

fn interactive(init: &str, update: &str, draw: &str) -> String {
    format!("{OFF_CONTRACT_TAGS}init = {init}\n{update}{draw}")
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
        checks("tag Circle init = {x: 0}\ndraw = program(m) do [Circle(1)] done\n1")
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
    let draw = "draw = program() do [] done\n";
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
    let draw = "draw = program(model) do [Line({x1: 0, y1: 0, x2: model.y, y2: 0, color: \"red\"})] done\n";
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

fn update_of(arms: &str) -> String {
    format!("update = program(model, event) do\n  match event do\n{arms}\n  done\ndone\n")
}

fn draw_of(shapes: &str) -> String {
    format!("draw = program(model) do {shapes} done\n")
}

fn update_type(source: &str) -> String {
    let ty = checks(source).typed.root_ty.to_string();
    let start = ty.find("update: ").expect("update in root type");
    let end = ty.find(", draw: ").expect("draw in root type");
    ty[start..end].to_string()
}

#[test]
fn every_host_event_and_shape_checks() {
    let update = update_of(
        "    Tick(dt) then model
    KeyDown(k) then match k do Up then model Down then model Left then model Right then model Other(s) then model done
    KeyUp(k) then model
    PointerMove(p) then {x: p.x}
    PointerDown(p) then {x: p.y}
    PointerUp(p) then model",
    );
    let draw = draw_of(
        "[Polyline({points: [{x: 0, y: 0}, {x: model.x, y: 1}], color: \"blue\"}), Line({x1: 0, y1: 0, x2: 1, y2: 1, color: \"#fa0\"})]",
    );
    checks(&interactive("{x: 0}", &update, &draw));
}

#[test]
fn the_event_row_closes_to_the_handled_tags() {
    let update = update_of("    Tick(dt) then model\n    KeyUp(k) then model");
    let ty = update_type(&interactive("{x: 0}", &update, DRAW));
    assert!(ty.contains("Tick") && ty.contains("KeyUp"), "{ty}");
    assert!(!ty.contains("KeyDown") && !ty.contains('|'), "{ty}");
}

#[test]
fn an_else_arm_leaves_the_row_at_the_tags_named_before_it() {
    let update = "update = program(model, event) do
  match event do
    Tick(dt) then model
  else model done
done
";
    let ty = update_type(&interactive("{x: 0}", update, DRAW));
    assert!(ty.contains("Tick") && !ty.contains('|'), "{ty}");
}

#[test]
fn an_unknown_event_tag_is_a_spanned_error() {
    let update = update_of("    Tick(dt) then model\n    Frobnicate then model");
    let (message, text) = the_error(&interactive("{x: 0}", &update, DRAW));
    assert!(
        message.starts_with("the host doesn't send a `Frobnicate` event"),
        "{message}"
    );
    assert!(text.starts_with("program(model, event)"), "{text}");
}

#[test]
fn an_event_payload_the_host_does_not_send_is_a_spanned_error() {
    for arm in [
        "Tick(dt) then {...model, x: dt + \"a\"}",
        "Tick(a, b) then model",
        "KeyDown(k) then {...model, x: k + 1}",
        "PointerMove(p) then {...model, x: p.z}",
    ] {
        let update = update_of(&format!("    {arm}"));
        let source = interactive("{x: 0}", &update, DRAW);
        assert!(!errors_of(&source).is_empty(), "{arm}");
    }
    let update = update_of("    Tick(a, b) then model");
    let (message, text) = the_error(&interactive("{x: 0}", &update, DRAW));
    assert!(
        message.contains("`Tick` event carries `Number`"),
        "{message}"
    );
    assert!(text.starts_with("program(model, event)"), "{text}");
}

#[test]
fn a_partial_key_match_without_else_is_rejected() {
    let update = update_of("    KeyDown(k) then match k do Up then model Down then model done");
    let (message, _) = the_error(&interactive("{x: 0}", &update, DRAW));
    assert!(message.contains("`KeyDown` event carries"), "{message}");
}

#[test]
fn a_key_match_with_else_checks() {
    let update = update_of(
        "    KeyDown(k) then match k do Up then model else model done\n    Tick(dt) then model",
    );
    checks(&interactive("{x: 0}", &update, DRAW));
}

#[test]
fn an_unknown_shape_tag_is_a_spanned_error() {
    let draw = draw_of("[Circle({x: 0, y: 0, r: 1, color: \"red\"})]");
    let (message, text) = the_error(&interactive("{x: 0}", UPDATE, &draw));
    assert!(
        message.starts_with("the host can't draw a `Circle` shape"),
        "{message}"
    );
    assert!(text.starts_with("program(model)"), "{text}");
}

#[test]
fn a_shape_payload_the_host_cannot_read_is_a_spanned_error() {
    for shape in [
        "Line({x1: 0, y1: 0, x2: 1, y2: 1})",
        "Line({x1: 0, y1: 0, x2: 1, y2: 1, color: 7})",
        "Line(1, 2, 3, 4, \"red\")",
        "Polyline({points: [1], color: \"red\"})",
        "Polyline({points: [{x: 0, y: \"a\"}], color: \"red\"})",
        "Polyline({color: \"red\"})",
    ] {
        let draw = draw_of(&format!("[{shape}]"));
        let (message, text) = the_error(&interactive("{x: 0}", UPDATE, &draw));
        assert!(message.contains("shape needs"), "{shape}: {message}");
        assert!(text.starts_with("program(model)"), "{text}");
    }
}

#[test]
fn a_polyline_may_be_built_from_the_model() {
    let draw = "draw = program(model) do
  [Polyline({points: model.path, color: \"red\"})]
done
";
    checks(&interactive("{x: 0, path: [{x: 0, y: 0}]}", UPDATE, draw));
}

fn key_update(arms: &str) -> String {
    update_of(&format!(
        "    KeyDown(key) then match key do\n{arms}\n    done"
    ))
}

const EVERY_KEY: &str =
    "Up then model Down then model Left then model Right then model Other(s) then model";

#[test]
fn the_key_group_is_closed_so_its_match_needs_no_else() {
    checks(&interactive("{x: 0}", &key_update(EVERY_KEY), DRAW));
}

#[test]
fn a_key_match_missing_a_key_is_a_spanned_error() {
    let arms = EVERY_KEY.replace("Right then model ", "");
    let (message, text) = the_error(&interactive("{x: 0}", &key_update(&arms), DRAW));
    assert!(message.contains("`Right`"), "{message}");
    assert!(text.starts_with("program(model, event)"), "{text}");
}

#[test]
fn a_key_tag_cannot_be_redeclared() {
    let source = format!("tag Up | Sideways\n{}", interactive("{x: 0}", UPDATE, DRAW));
    let (message, text) = the_error(&source);
    assert!(message.starts_with("duplicate tag `Up`"), "{message}");
    assert_eq!(text, "Up");
}
