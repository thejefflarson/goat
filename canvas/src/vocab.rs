//! The canvas host's vocabulary: what it sends `update`, what `draw` may
//! return, and the keys events carry. Every shape streams through an existing
//! `scene.*` import, so the wire protocol is the turtle's.

use goat_checker::Vocab;
use goat_checker::ty::{Group, Row, Ty};
use goat_checker::vocab::{Decode, EventTag, SceneCalls, ShapeTag};

const KEYS: &str = include_str!("canvas_keys.goat");

fn record<const N: usize>(fields: [(&str, Ty); N]) -> Ty {
    Ty::Record(Row::of(fields.map(|(label, ty)| (label.to_string(), ty))))
}

/// A shape of `numbers` and then a `fill` color, streamed to one `scene.*` call.
fn shape(name: &str, scene: &str, numbers: &[&str], extra: Option<(&str, Ty)>) -> ShapeTag {
    let numbers = numbers.iter().map(|label| (label.to_string(), Ty::Float));
    let fields = numbers.chain(extra.map(|(label, ty)| (label.to_string(), ty)));
    ShapeTag {
        name: name.to_string(),
        payload: Ty::Record(Row::of(
            fields
                .chain([("fill".to_string(), Ty::Str)])
                .collect::<Vec<_>>(),
        )),
        scene: SceneCalls::Call(scene.to_string()),
    }
}

pub fn vocab() -> Vocab {
    let keys = Group {
        tags: ["Space", "Left", "Right", "Up", "Down"]
            .map(|tag| (tag.to_string(), Ty::Unit))
            .into_iter()
            .chain([("Char".to_string(), Ty::Str)])
            .collect(),
        recursive: false,
    };
    let key = keys.instantiate(0);
    let mouse = || record([("x", Ty::Float), ("y", Ty::Float)]);
    let event = |name: &str, payload: Ty, decode: Option<Decode>| EventTag {
        name: name.to_string(),
        payload,
        decode,
    };
    let key_event = |name: &str| {
        let decode = Decode {
            wire: Ty::Str,
            function: "canvas_key_of".to_string(),
        };
        event(name, key.clone(), Some(decode))
    };
    Vocab {
        events: vec![
            event("Frame", Ty::Float, None),
            key_event("KeyPress"),
            key_event("KeyRelease"),
            event("MouseMove", mouse(), None),
            event("MousePress", mouse(), None),
            event("MouseRelease", mouse(), None),
        ],
        shapes: vec![
            shape("Segment", "line", &["x1", "y1", "x2", "y2"], None),
            shape("Dot", "circle", &["x", "y", "r"], None),
            shape("Box", "rect", &["x", "y", "w", "h"], None),
            shape("Label", "text", &["x", "y"], Some(("text", Ty::Str))),
        ],
        keys,
        prelude: KEYS.to_string(),
    }
}
