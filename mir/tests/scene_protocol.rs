//! The `scene.*` wire protocol is written down three times: `Vocab::turtle()`
//! (the source of truth, ADR 0020), the Rust scene host, and the browser's
//! `web/scene.ts`. The browser is checked through `web/scene-signatures.txt`,
//! which `web/scene-signatures.test.ts` holds `scene.ts` to. A change to one
//! copy that skips the others fails here or there.

use goat_checker::Vocab;
use goat_checker::hir::Boundary;
use goat_checker::ty::Ty;
use goat_checker::vocab::{Leaf, SceneCalls, shape_leaves};
use goat_mir::{Host, SceneHost};
use std::collections::BTreeMap;

type Table = BTreeMap<String, Vec<String>>;

fn wire(ty: &Ty) -> String {
    match ty {
        Ty::Float => "number",
        Ty::Str => "string",
        other => panic!("{other:?} has no scene wire type"),
    }
    .to_string()
}

fn wires(leaves: &[Leaf]) -> Vec<String> {
    leaves.iter().map(|leaf| wire(&leaf.ty)).collect()
}

/// The scene calls `Vocab::turtle()` implies, plus the frame brackets every
/// interactive program streams inside.
fn from_vocab() -> Table {
    let mut table = Table::new();
    table.insert("begin".into(), vec![]);
    table.insert("end".into(), vec![]);
    for shape in &Vocab::turtle().shapes {
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
fn the_scene_host_agrees_with_the_turtle_vocab() {
    let vocab = from_vocab();
    assert_eq!(from_host(vocab.keys().cloned()), vocab);
}

#[test]
fn the_web_golden_agrees_with_the_turtle_vocab() {
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
