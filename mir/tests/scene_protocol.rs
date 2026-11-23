//! The `scene.*` wire protocol is written down three times: `Vocab::turtle()`,
//! `Vocab::editor()` and `Vocab::theme()` (the source of truth, ADR 0020), the
//! Rust scene host, and the browser's `web/scene.ts`. The browser is checked through `web/scene-signatures.txt`,
//! which `web/scene-signatures.test.ts` holds `scene.ts` to. A change to one
//! copy that skips the others fails here or there.

use goat_checker::Vocab;
use goat_checker::hir::Boundary;
use goat_checker::ty::Ty;
use goat_checker::vocab::{Leaf, SceneCalls, shape_leaves};
use goat_mir::frame::{Calls, Wire};
use goat_mir::{Host, SceneCommand, SceneHost};
use std::collections::BTreeMap;

type Table = BTreeMap<String, Vec<String>>;

fn wire(ty: &Ty) -> String {
    match ty {
        Ty::Float => "number",
        Ty::Int => "int",
        Ty::Str => "string",
        other => panic!("{other:?} has no scene wire type"),
    }
    .to_string()
}

fn wires(leaves: &[Leaf]) -> Vec<String> {
    leaves.iter().map(|leaf| wire(&leaf.ty)).collect()
}

/// The scene calls the vocabularies imply, plus the
/// frame brackets every interactive program streams inside.
fn from_vocab() -> Table {
    let mut table = Table::new();
    table.insert("begin".into(), vec![]);
    table.insert("end".into(), vec![]);
    let shapes = [Vocab::turtle(), Vocab::editor(), Vocab::theme()].map(|vocab| vocab.shapes);
    for shape in shapes.iter().flatten() {
        let leaves = shape_leaves(&shape.payload).expect("a flat payload");
        match &shape.scene {
            SceneCalls::Call(call) => {
                table.insert(call.clone(), wires(&leaves.head));
            }
            SceneCalls::Stream {
                begin,
                element,
                end,
            } => {
                table.insert(begin.clone(), wires(&leaves.head));
                table.insert(
                    element.clone(),
                    wires(&leaves.list.expect("a list").element),
                );
                table.insert(end.clone(), vec![]);
            }
        }
    }
    table
}

fn from_host(names: impl Iterator<Item = String>) -> Table {
    names
        .map(|name| {
            let (params, ret) = SceneHost::default()
                .signature("scene", &name)
                .unwrap_or_else(|| panic!("the scene host lacks scene.{name}"));
            assert_eq!(ret, Boundary::Unit, "scene.{name} returns nothing");
            let params = params
                .iter()
                .map(|param| match param {
                    Boundary::Number => "number".to_string(),
                    Boundary::Int => "int".to_string(),
                    Boundary::Str => "string".to_string(),
                    other => panic!("{other:?} is not a scene wire type"),
                })
                .collect();
            (name, params)
        })
        .collect()
}

fn golden() -> Table {
    include_str!("../../web/scene-signatures.txt")
        .lines()
        .map(|line| {
            let mut words = line.split(' ').map(String::from);
            (words.next().expect("a name"), words.collect())
        })
        .collect()
}

#[test]
fn the_scene_host_agrees_with_the_vocabularies() {
    let vocab = from_vocab();
    assert_eq!(from_host(vocab.keys().cloned()), vocab);
}

#[test]
fn the_web_golden_agrees_with_the_vocabularies() {
    assert_eq!(golden(), from_vocab());
}

#[test]
fn the_color_allowlist_is_one_rule() {
    for ok in ["red", "#ff8800", &"a".repeat(32)] {
        assert_eq!(goat_mir::check_color(ok), Ok(()), "{ok}");
    }
    for bad in ["", "\"/><script>", "re d", &"a".repeat(33)] {
        let error = goat_mir::check_color(bad).unwrap_err();
        assert!(error.contains("color wants a name"), "{bad}: {error}");
    }
}

fn frame_of(name: &str, params: &[Wire], values: &[u8]) -> Vec<u8> {
    let mut calls = Calls::default();
    let index = calls.index(name, params);
    let mut bytes = calls.header();
    bytes.push(index);
    bytes.extend(values);
    bytes
}

fn text(s: &str) -> Vec<u8> {
    let mut bytes = (s.len() as u32).to_le_bytes().to_vec();
    bytes.extend(s.as_bytes());
    bytes
}

#[test]
fn a_frame_replays_into_the_sink_with_every_color_checked() {
    let mut host = SceneHost::default();
    let ok = frame_of("polyline_begin", &[Wire::Str], &text("red"));
    host.frame(&ok).unwrap();
    assert_eq!(
        host.commands,
        [SceneCommand::PolylineBegin("red".to_string())]
    );
    let bad = frame_of("polyline_begin", &[Wire::Str], &text("\"/><script>"));
    assert!(host.frame(&bad).unwrap_err().contains("color wants a name"));
}

#[test]
fn a_malformed_frame_is_an_error_and_never_a_panic() {
    let mut host = SceneHost::default();
    let circle = [Wire::Float, Wire::Float, Wire::Float, Wire::Str];
    let values = [[0u8; 24].as_slice(), &text("red")].concat();
    let whole = frame_of("circle", &circle, &values);
    host.frame(&whole).unwrap();
    let record = whole.len() - 1 - values.len();
    for len in 0..whole.len() {
        let cut = host.frame(&whole[..len]);
        assert_eq!(cut.is_ok(), len == record, "cut at {len}");
    }
    let unknown = frame_of("sparkle", &[], &[]);
    assert!(host.frame(&unknown).unwrap_err().contains("sparkle"));
    let wrong_types = frame_of("circle", &[Wire::Str], &text("red"));
    assert!(host.frame(&wrong_types).is_err());
    let huge = frame_of("polyline_begin", &[Wire::Str], &u32::MAX.to_le_bytes());
    assert!(host.frame(&huge).is_err());
    assert!(host.frame(&[]).is_err());
    assert!(host.frame(&[0xFF; 64]).is_err());
}
