//! The glue an interactive host calls is derived from its vocabulary's payload
//! types (ADR 0020): a second host's constructors and scene calls come out of
//! its `Vocab`, with no backend code written for its tags.

use goat_checker::ty::{Group, Row, Ty};
use goat_checker::vocab::{Decode, EventTag, SceneCalls, ShapeTag, payload_list};
use goat_checker::{Vocab, check_with_vocab};
use goat_mir::*;

fn record<const N: usize>(fields: [(&str, Ty); N]) -> Ty {
    Ty::Record(Row::of(
        fields
            .into_iter()
            .map(|(label, field)| (label.to_string(), field)),
    ))
}

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
            event(
                "Touch",
                record([
                    ("at", record([("x", Ty::Float), ("y", Ty::Float)])),
                    ("hard", Ty::Bool),
                ]),
                None,
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
        prelude: "pad_of = program(n) do if n == 0 then A else B done done\n".into(),
    }
}

const PROGRAM: &str = r#"
init = {n: 0}
update = program(model, event) do
  match event do
    Press then model
    Tilt(t) then {n: model.n + 1}
    Button(pad) then match pad do A then {n: 1} B then {n: 2} done
    Touch(t) then if t.hard then model else {n: 0} done
  done
done
draw = program(model) do
  [Led({pin: 3, on: true}), Strip({color: "red", pixels: [{r: 1, g: 2, b: 3}]})]
done
"#;

fn lower(vocab: &Vocab, source: &str) -> Program {
    let checked = check_with_vocab(&vocab.prelude, vocab, source).expect("checks");
    let program = mono(&checked).expect("lowers");
    assert_eq!(verify(&program), Ok(()));
    program
}

fn import(program: &Program, name: &str) -> Vec<MTy> {
    program
        .foreign
        .iter()
        .find(|f| f.module == "scene" && f.name == name)
        .unwrap_or_else(|| panic!("scene.{name} is not imported: {:?}", program.foreign))
        .params
        .clone()
}

fn ctor_params(program: &Program, label: &str) -> Vec<MTy> {
    let events = &program.interactive.as_ref().unwrap().events;
    let ctor = events
        .iter()
        .find(|e| e.label == label)
        .expect("subscribed");
    program.funcs[ctor.func.0 as usize]
        .params
        .iter()
        .map(|(_, ty)| *ty)
        .collect()
}

#[test]
fn a_shape_streams_through_the_scene_imports_its_vocabulary_names() {
    let program = lower(&toy(), PROGRAM);
    assert_eq!(import(&program, "led"), [MTy::Int, MTy::Bool]);
    assert_eq!(import(&program, "strip_begin"), [MTy::Ptr(HeapKind::Str)]);
    assert_eq!(import(&program, "pixel"), [MTy::Int; 3]);
    assert_eq!(import(&program, "strip_end"), []);
    let turtle_calls = ["line", "polyline_begin", "vertex", "polyline_end"];
    assert!(
        program
            .foreign
            .iter()
            .all(|f| !turtle_calls.contains(&f.name.as_str()))
    );
}

#[test]
fn an_event_constructor_takes_the_leaves_of_what_the_host_sends() {
    let program = lower(&toy(), PROGRAM);
    assert_eq!(ctor_params(&program, "Press"), []);
    assert_eq!(ctor_params(&program, "Tilt"), [MTy::Float]);
    assert_eq!(ctor_params(&program, "Button"), [MTy::Int]);
    assert_eq!(
        ctor_params(&program, "Touch"),
        [MTy::Float, MTy::Float, MTy::Bool]
    );
}

#[test]
fn only_the_events_the_program_handles_get_a_constructor() {
    let source = PROGRAM
        .replace("    Press then model\n", "")
        .replace("Tilt(t) then {n: model.n + 1}\n", "");
    let program = lower(&toy(), &source);
    let mut labels: Vec<_> = program
        .interactive
        .unwrap()
        .events
        .into_iter()
        .map(|e| e.label)
        .collect();
    labels.sort();
    assert_eq!(labels, ["Button", "Touch"]);
}

#[test]
fn the_order_a_host_lists_its_tags_in_changes_no_layout() {
    let forward = toy();
    let mut backward = toy();
    backward.events.reverse();
    backward.shapes.reverse();
    backward.keys.tags.reverse();
    assert_eq!(lower(&forward, PROGRAM), lower(&backward, PROGRAM));
}

const KEY_OF: &str = include_str!("../../prelude/turtle_keys.goat");

#[test]
fn a_decoder_nothing_uses_adds_no_tags_to_the_numbering() {
    let with = Vocab::turtle();
    let without = Vocab {
        prelude: String::new(),
        events: Vec::new(),
        ..Vocab::turtle()
    };
    let source = "tag Circle\nCircle(1)";
    assert_eq!(lower(&with, source), lower(&without, source));
}

#[test]
fn a_decoder_a_program_calls_brings_its_tags() {
    let source = "match key_of(\"ArrowUp\") do Up then 1 else 2 done";
    let checked = check_with_vocab(KEY_OF, &Vocab::turtle(), source).expect("checks");
    let program = mono(&checked).expect("lowers");
    assert_eq!(verify(&program), Ok(()));
    let out = run(&program).expect("runs");
    assert_eq!(out.value, Value::Int(1));
}

#[test]
fn the_turtle_streams_the_scene_calls_it_always_has() {
    let turtle = Vocab::turtle();
    let source = "init = {n: 0}\n\
                  update = program(model, event) do match event do Tick(dt) then model done done\n\
                  draw = program(model) do [Line({x1: 0, y1: 0, x2: 1, y2: 1, color: \"red\"}), \
                  Polyline({points: [{x: 0, y: 0}], color: \"blue\"})] done\n";
    let program = lower(&turtle, source);
    let float = MTy::Float;
    let string = MTy::Ptr(HeapKind::Str);
    assert_eq!(
        import(&program, "line"),
        [float, float, float, float, string]
    );
    assert_eq!(import(&program, "polyline_begin"), [string]);
    assert_eq!(import(&program, "vertex"), [float, float]);
    assert_eq!(import(&program, "polyline_end"), []);
}
