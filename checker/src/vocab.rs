//! What the interactive host speaks (ADR 0015): the events it sends `update`
//! and the shapes it draws from `draw`. A program may use any subset; the
//! checker rejects a tag outside these lists.

use crate::ty::{Row, Ty, TypeVar};

pub const EVENT_TAGS: [&str; 6] = [
    "Tick",
    "KeyDown",
    "KeyUp",
    "PointerMove",
    "PointerDown",
    "PointerUp",
];

pub const SHAPE_TAGS: [&str; 2] = ["Polyline", "Line"];

/// The tags of `Key`, the payload of `KeyDown` and `KeyUp`.
pub const KEY_TAGS: [&str; 5] = ["Up", "Down", "Left", "Right", "Other"];

fn row<const N: usize>(fields: [(&str, Ty); N]) -> Row {
    fields
        .into_iter()
        .rev()
        .fold(Row::Empty, |rest, (label, field)| Row::Extend {
            label: label.to_string(),
            field: Box::new(field),
            rest: Box::new(rest),
        })
}

fn record<const N: usize>(fields: [(&str, Ty); N]) -> Ty {
    Ty::Record(row(fields))
}

fn point() -> Ty {
    record([("x", Ty::Number), ("y", Ty::Number)])
}

fn key() -> Ty {
    Ty::Variant(row([
        ("Up", Ty::Unit),
        ("Down", Ty::Unit),
        ("Left", Ty::Unit),
        ("Right", Ty::Unit),
        ("Other", Ty::Str),
    ]))
}

/// `μbinder. [Empty, Link: {0: item, 1: binder}]`
pub fn list(binder: TypeVar, item: Ty) -> Ty {
    let link = record([("0", item), ("1", Ty::Var(binder))]);
    Ty::Rec(
        binder,
        Box::new(Ty::Variant(row([("Empty", Ty::Unit), ("Link", link)]))),
    )
}

/// The payload type of the host event `tag`.
pub fn event_payload(tag: &str) -> Option<Ty> {
    Some(match tag {
        "Tick" => Ty::Number,
        "KeyDown" | "KeyUp" => key(),
        "PointerMove" | "PointerDown" | "PointerUp" => point(),
        _ => return None,
    })
}

/// The payload type of the shape `tag`; `binder` names the list of a
/// `Polyline`'s points.
pub fn shape_payload(tag: &str, binder: TypeVar) -> Option<Ty> {
    Some(match tag {
        "Polyline" => record([("points", list(binder, point())), ("color", Ty::Str)]),
        "Line" => record([
            ("x1", Ty::Number),
            ("y1", Ty::Number),
            ("x2", Ty::Number),
            ("y2", Ty::Number),
            ("color", Ty::Str),
        ]),
        _ => return None,
    })
}
