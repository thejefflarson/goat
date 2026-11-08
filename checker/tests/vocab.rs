//! A host declares its own closed vocabulary (ADR 0020). The checker closes a
//! program's events, shapes and keys to that set exactly as it does the
//! turtle's, and rejects any tag outside it with a spanned error.

use goat_checker::hir::Span;
use goat_checker::ty::{Group, Row, Ty};
use goat_checker::vocab::{Decode, EventTag, SceneCalls, ShapeTag, payload_list};
use goat_checker::{Checked, GoatError, Vocab, check_with_vocab};

fn record<const N: usize>(fields: [(&str, Ty); N]) -> Ty {
    Ty::Record(Row::of(
        fields
            .into_iter()
            .map(|(label, field)| (label.to_string(), field)),
    ))
}

const PAD_OF: &str = "pad_of = program(n) do if n == 0 then A else B done done\n";

/// An embedded-style host: a button with two pads decoded from a number, a
/// tilt sensor and a bare press in; one LED and a strip of pixels out.
fn toy() -> Vocab {
    let pad = Group {
        tags: vec![("A".into(), Ty::Unit), ("B".into(), Ty::Unit)],
        recursive: false,
    };
    let event = |name: &str, payload, decode| EventTag {
        name: name.into(),
        payload,
        decode,
    };
    Vocab {
        events: vec![
            event("Press", Ty::Unit, None),
            event("Tilt", Ty::Float, None),
            event(
                "Button",
                pad.instantiate(0),
                Some(Decode {
                    wire: Ty::Int,
                    function: "pad_of".into(),
                }),
            ),
        ],
        shapes: vec![
            ShapeTag {
                name: "Led".into(),
                payload: record([("pin", Ty::Int), ("on", Ty::Bool)]),
                scene: SceneCalls::Call("led".into()),
            },
            ShapeTag {
                name: "Strip".into(),
                payload: record([
                    ("color", Ty::Str),
                    (
                        "pixels",
                        payload_list(record([("r", Ty::Int), ("g", Ty::Int), ("b", Ty::Int)])),
                    ),
                ]),
                scene: SceneCalls::Stream {
                    begin: "strip_begin".into(),
                    element: "pixel".into(),
                    end: "strip_end".into(),
                },
            },
        ],
        keys: pad,
        prelude: PAD_OF.into(),
    }
}

fn check_toy(source: &str) -> Result<Checked, Vec<GoatError>> {
    let vocab = toy();
    check_with_vocab(&vocab.prelude, &vocab, source)
}

fn program(update_arms: &str, draw_body: &str) -> String {
    format!(
        "init = {{n: 0}}\n\
         update = program(model, event) do match event do {update_arms} done done\n\
         draw = program(model) do {draw_body} done\n"
    )
}

type Break = fn(&mut Vocab);

const LED: &str = "[Led({pin: model.n, on: true})]";

fn the_error(source: &str) -> (String, String) {
    let errors = check_toy(source).err().expect("should not check");
    assert_eq!(errors.len(), 1, "{errors:?}");
    let span = errors[0].span;
    (
        errors[0].message.clone(),
        source[span.start..span.end].to_string(),
    )
}

#[test]
fn a_program_checks_against_the_hosts_own_events_and_shapes() {
    let source = program("Press then {n: model.n + 1} Tilt(t) then {n: 0}", LED);
    assert!(check_toy(&source).unwrap().interactive.is_some());
}

#[test]
fn the_handled_events_close_to_exactly_the_tags_handled() {
    let source = program("Press then model Tilt(t) then model", LED);
    let ty = check_toy(&source).unwrap().typed.root_ty.to_string();
    assert!(ty.contains("[Press, Tilt: Number]"), "{ty}");
}

#[test]
fn a_decoded_event_carries_the_hosts_key_group() {
    let source = program(
        "Button(pad) then match pad do A then {n: 1} B then {n: 2} done",
        LED,
    );
    assert!(check_toy(&source).is_ok());
}

#[test]
fn a_key_match_without_else_must_name_every_tag_of_the_hosts_group() {
    let source = program("Button(pad) then match pad do A then {n: 1} done", LED);
    let (message, text) = the_error(&source);
    assert!(message.contains("`B`"), "{message}");
    assert!(text.starts_with("program(model, event)"), "{text}");
}

#[test]
fn else_is_the_catch_all_over_the_hosts_group() {
    let source = program(
        "Button(pad) then match pad do A then {n: 1} else model done",
        LED,
    );
    assert!(check_toy(&source).is_ok());
}

#[test]
fn the_turtles_events_are_not_the_toy_hosts() {
    let source = format!("tag Tick\n{}", program("Tick then model", LED));
    let (message, text) = the_error(&source);
    assert_eq!(
        message,
        "the host doesn't send a `Tick` event; the host knows `Press`, `Tilt` and `Button`"
    );
    assert!(text.starts_with("program(model, event)"), "{text}");
}

#[test]
fn a_tag_no_host_declared_is_an_unknown_name() {
    let (message, text) = the_error(&program("Tick(dt) then model", LED));
    assert!(message.contains("Tick"), "{message}");
    assert_eq!(text, "Tick");
}

#[test]
fn the_turtles_shapes_are_not_the_toy_hosts() {
    let source = format!(
        "tag Line\n{}",
        program(
            "Press then model",
            "[Line({x1: 0, y1: 0, x2: 1, y2: 1, color: \"red\"})]"
        )
    );
    let (message, text) = the_error(&source);
    assert_eq!(
        message,
        "the host can't draw a `Line` shape; the host knows `Led` and `Strip`"
    );
    assert!(text.starts_with("program(model)"), "{text}");
}

#[test]
fn a_payload_the_host_does_not_send_is_a_spanned_error() {
    let (message, text) = the_error(&program("Tilt(t) then {n: t.x}", LED));
    assert!(
        message.starts_with("the host's `Tilt` event carries `Number`"),
        "{message}"
    );
    assert!(text.starts_with("program(model, event)"), "{text}");
}

#[test]
fn a_shape_with_a_list_streams_its_elements_through_the_hosts_types() {
    let draw = "[Strip({color: \"red\", pixels: [{r: 1, g: 2, b: 3}]})]";
    assert!(check_toy(&program("Press then model", draw)).is_ok());
    let bad = "[Strip({color: \"red\", pixels: [{r: 1, g: 2}]})]";
    let (message, _) = the_error(&program("Press then model", bad));
    assert!(
        message.starts_with("the host's `Strip` shape needs"),
        "{message}"
    );
}

#[test]
fn a_decoder_of_the_wrong_type_is_a_spanned_error_in_the_prelude() {
    let mut vocab = toy();
    vocab.prelude = "pad_of = program(n) do 5 done\n".into();
    let source = program("Press then model", LED);
    let errors = check_with_vocab(&vocab.prelude, &vocab, &source)
        .err()
        .expect("should not check");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0]
            .message
            .starts_with("the host's `pad_of` decodes its events, so it must have the type"),
        "{}",
        errors[0].message
    );
    assert!(errors[0].span.in_prelude());
}

#[test]
fn a_host_prelude_that_lacks_its_decoder_is_a_spanned_error() {
    let vocab = toy();
    let source = program("Press then model", LED);
    let errors = check_with_vocab("", &vocab, &source)
        .err()
        .expect("should not check");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].message.contains("must define `pad_of`"));
    assert!(errors[0].span.end > 0);
}

#[test]
fn a_program_that_rebinds_a_decoders_name_does_not_replace_it() {
    let source = format!(
        "pad_of = program(n) do n done\n{}",
        program("Press then model", LED)
    );
    assert!(check_toy(&source).is_ok());
}

#[test]
fn a_vocabulary_that_cannot_be_realized_is_a_spanned_error() {
    let ill_formed: [(&str, Break); 4] = [
        ("declared twice", |v| v.events[1].name = "Press".into()),
        ("not a tag a host can declare", |v| {
            v.events[0].name = "Link".into()
        }),
        ("numbers, strings or records", |v| {
            v.events[1].payload = Ty::Func(vec![], Box::new(Ty::Unit))
        }),
        ("do not match", |v| {
            v.shapes[0].scene = SceneCalls::Stream {
                begin: "a".into(),
                element: "b".into(),
                end: "c".into(),
            }
        }),
    ];
    for (reason, break_it) in ill_formed {
        let mut vocab = toy();
        break_it(&mut vocab);
        let errors = check_with_vocab(&vocab.prelude, &vocab, "1")
            .err()
            .unwrap_or_else(|| panic!("`{reason}` should not check"));
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert_eq!(errors[0].span, Span::new(0, 0));
        assert!(
            errors[0]
                .message
                .starts_with("the host's vocabulary is invalid"),
            "{}",
            errors[0].message
        );
        assert!(errors[0].message.contains(reason), "{}", errors[0].message);
    }
}

#[test]
fn the_turtle_vocabulary_is_well_formed_and_matches_what_the_checker_always_accepted() {
    let turtle = Vocab::turtle();
    assert_eq!(turtle.validate(), Ok(()));
    let events: Vec<&str> = turtle.events.iter().map(|e| e.name.as_str()).collect();
    assert_eq!(
        events,
        [
            "Tick",
            "KeyDown",
            "KeyUp",
            "PointerMove",
            "PointerDown",
            "PointerUp"
        ]
    );
    let shapes: Vec<&str> = turtle.shapes.iter().map(|s| s.name.as_str()).collect();
    assert_eq!(shapes, ["Polyline", "Line"]);
    let keys: Vec<&str> = turtle.key_tag_names().collect();
    assert_eq!(keys, ["Up", "Down", "Left", "Right", "Other"]);
    assert_eq!(turtle.event("Tick").unwrap().payload, Ty::Float);
    assert_eq!(
        turtle.event("KeyDown").unwrap().payload,
        turtle.keys.instantiate(0)
    );
    let decode = |name: &str| turtle.event(name).unwrap().decode.clone();
    assert_eq!(decode("KeyDown"), decode("KeyUp"));
    assert_eq!(decode("KeyDown").unwrap().function, "key_of");
}
