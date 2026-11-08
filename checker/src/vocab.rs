//! What a host speaks (ADR 0020): the events it sends `update`, the shapes it
//! draws from `draw`, and the keys that ride in events. Each family is a closed
//! set of tags the host declares; a program may use any subset, and the checker
//! rejects a tag outside the set.

use crate::infer::subst_vars;
use crate::kinds::is_list_tag;
use crate::ty::{Group, Row, Ty, TypeVar};
use std::collections::{HashMap, HashSet};

/// The turtle's `key_of`, which decodes a browser `KeyboardEvent.key` into a `Key`.
const TURTLE_KEYS: &str = include_str!("../../prelude/turtle_keys.goat");

/// The binder a stored list type names itself with; [`Vocab::shape_payload`]
/// renames it to a fresh one per use.
const LIST_BINDER: TypeVar = TypeVar::MAX;

/// One host's closed vocabulary. Tag numbers are not part of it: mono numbers
/// every tag in sorted-label order (ADR 0010), so the order tags are listed in
/// here changes nothing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Vocab {
    pub events: Vec<EventTag>,
    pub shapes: Vec<ShapeTag>,
    /// The tags of `Key`, the one closed group a host's events may carry.
    pub keys: Group,
    /// Goat source the host's decoders live in, appended to its prelude.
    pub prelude: String,
}

/// An event the host sends `update`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EventTag {
    pub name: String,
    /// The goat type `update` sees.
    pub payload: Ty,
    /// How the host's values become `payload`, when they are not already it.
    pub decode: Option<Decode>,
}

impl EventTag {
    fn decoder(&self) -> Option<&str> {
        self.decode.as_ref().map(|d| d.function.as_str())
    }

    /// The type of this event's decoder: its wire to its payload.
    fn decoder_ty(&self) -> Option<Ty> {
        let wire = self.decode.as_ref()?.wire.clone();
        Some(Ty::Func(vec![wire], Box::new(self.payload.clone())))
    }
}

/// A host event arrives as the leaves of `wire` and reaches `update` through
/// `function`, a goat function `wire -> payload` in the host's prelude.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decode {
    pub wire: Ty,
    pub function: String,
}

/// A shape `draw` returns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShapeTag {
    pub name: String,
    pub payload: Ty,
    pub scene: SceneCalls,
}

/// The `scene.*` imports a shape streams through.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SceneCalls {
    /// One call with every leaf of the payload, in field order.
    Call(String),
    /// For a payload with one list: `begin` with the leaves outside the list,
    /// `element` with the leaves of each element, then `end`.
    Stream {
        begin: String,
        element: String,
        end: String,
    },
}

/// A scalar or string reached through `path`, the field labels from the payload
/// down.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Leaf {
    pub path: Vec<String>,
    pub ty: Ty,
}

/// A shape payload's leaves: those outside its list, and the list's own.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShapeLeaves {
    pub head: Vec<Leaf>,
    pub list: Option<ListLeaves>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ListLeaves {
    pub field: String,
    pub element: Vec<Leaf>,
}

fn fields(row: &Row) -> Option<Vec<(&String, &Ty)>> {
    let mut out = Vec::new();
    let mut next = row;
    loop {
        match next {
            Row::Extend { label, field, rest } => {
                out.push((label, &**field));
                next = rest;
            }
            Row::Empty => return Some(out),
            Row::Var(_) => return None,
        }
    }
}

fn collect_leaves(ty: &Ty, path: &mut Vec<String>, out: &mut Vec<Leaf>) -> bool {
    match ty {
        Ty::Int | Ty::Float | Ty::Str | Ty::Bool => {
            out.push(Leaf {
                path: path.clone(),
                ty: ty.clone(),
            });
            true
        }
        Ty::Record(row) => fields(row).is_some_and(|fields| {
            fields.into_iter().all(|(label, field)| {
                path.push(label.clone());
                let ok = collect_leaves(field, path, out);
                path.pop();
                ok
            })
        }),
        _ => false,
    }
}

/// The scalar and string leaves of `ty`, left to right in field order: a
/// scalar is one, a record's are its fields', and `Unit` has none. `None` for
/// anything else, which has no flat form.
pub fn leaves(ty: &Ty) -> Option<Vec<Leaf>> {
    if *ty == Ty::Unit {
        return Some(Vec::new());
    }
    let mut out = Vec::new();
    collect_leaves(ty, &mut Vec::new(), &mut out).then_some(out)
}

/// The element type of `ty` if it is the list `list` builds.
pub fn list_element(ty: &Ty) -> Option<&Ty> {
    let Ty::Rec(_, body) = ty else { return None };
    let Ty::Variant(Row::Extend {
        label: empty, rest, ..
    }) = &**body
    else {
        return None;
    };
    let Row::Extend {
        label: link, field, ..
    } = &**rest
    else {
        return None;
    };
    let Ty::Record(Row::Extend {
        label: head,
        field: item,
        ..
    }) = &**field
    else {
        return None;
    };
    (empty == "Empty" && link == "Link" && head == "0").then_some(&**item)
}

/// The leaves a shape's payload streams: its record's fields in order, with at
/// most one of them a list whose elements are flat.
pub fn shape_leaves(ty: &Ty) -> Option<ShapeLeaves> {
    let Ty::Record(row) = ty else { return None };
    let (mut head, mut list) = (Vec::new(), None);
    for (label, field) in fields(row)? {
        if let Some(element) = list_element(field) {
            if list.is_some() {
                return None;
            }
            list = Some(ListLeaves {
                field: label.clone(),
                element: leaves(element)?,
            });
        } else {
            let mut found = Vec::new();
            if !collect_leaves(field, &mut vec![label.clone()], &mut found) {
                return None;
            }
            head.extend(found);
        }
    }
    Some(ShapeLeaves { head, list })
}

impl Vocab {
    /// A host that sends and draws nothing.
    pub fn empty() -> Vocab {
        Vocab {
            events: Vec::new(),
            shapes: Vec::new(),
            keys: Group {
                tags: Vec::new(),
                recursive: false,
            },
            prelude: String::new(),
        }
    }

    /// The vocabulary of the turtle host, the CLI and the web player.
    pub fn turtle() -> Vocab {
        let keys = Group {
            tags: ["Up", "Down", "Left", "Right"]
                .map(|tag| (tag.to_string(), Ty::Unit))
                .into_iter()
                .chain([("Other".to_string(), Ty::Str)])
                .collect(),
            recursive: false,
        };
        let key = keys.instantiate(0);
        let point = || record([float("x"), float("y")]);
        let event = |name: &str, payload: Ty, decode: Option<Decode>| EventTag {
            name: name.to_string(),
            payload,
            decode,
        };
        let key_decode = || {
            Some(Decode {
                wire: Ty::Str,
                function: "key_of".to_string(),
            })
        };
        let shape = |name: &str, payload: Ty, scene: SceneCalls| ShapeTag {
            name: name.to_string(),
            payload,
            scene,
        };
        Vocab {
            events: vec![
                event("Tick", Ty::Float, None),
                event("KeyDown", key.clone(), key_decode()),
                event("KeyUp", key, key_decode()),
                event("PointerMove", point(), None),
                event("PointerDown", point(), None),
                event("PointerUp", point(), None),
            ],
            shapes: vec![
                shape(
                    "Polyline",
                    record([("points", payload_list(point())), ("color", Ty::Str)]),
                    SceneCalls::Stream {
                        begin: "polyline_begin".to_string(),
                        element: "vertex".to_string(),
                        end: "polyline_end".to_string(),
                    },
                ),
                shape(
                    "Line",
                    record([
                        float("x1"),
                        float("y1"),
                        float("x2"),
                        float("y2"),
                        ("color", Ty::Str),
                    ]),
                    SceneCalls::Call("line".to_string()),
                ),
            ],
            keys,
            prelude: TURTLE_KEYS.to_string(),
        }
    }

    /// The tags that stay open rows until `update` and `draw` close them to
    /// the ones the program handles or draws: events and shapes.
    pub fn tag_names(&self) -> impl Iterator<Item = &str> {
        let events = self.events.iter().map(|e| e.name.as_str());
        events.chain(self.shapes.iter().map(|s| s.name.as_str()))
    }

    pub fn key_tag_names(&self) -> impl Iterator<Item = &str> {
        self.keys.tags.iter().map(|(tag, _)| tag.as_str())
    }

    pub fn event(&self, name: &str) -> Option<&EventTag> {
        self.events.iter().find(|e| e.name == name)
    }

    pub fn shape(&self, name: &str) -> Option<&ShapeTag> {
        self.shapes.iter().find(|s| s.name == name)
    }

    /// The names of the decoders the events use, each once.
    pub fn decoders(&self) -> Vec<&str> {
        let mut names: Vec<&str> = Vec::new();
        for decode in self.events.iter().filter_map(|e| e.decode.as_ref()) {
            if !names.contains(&decode.function.as_str()) {
                names.push(&decode.function);
            }
        }
        names
    }

    /// The type of the decoder `function`: from the wire of an event that
    /// names it to that event's payload.
    pub fn decoder_ty(&self, function: &str) -> Option<Ty> {
        self.events
            .iter()
            .find(|e| e.decoder() == Some(function))
            .and_then(EventTag::decoder_ty)
    }

    /// The payload type of the shape `tag`, its list named `binder`.
    pub fn shape_payload(&self, tag: &str, binder: TypeVar) -> Option<Ty> {
        let mapping = HashMap::from([(LIST_BINDER, binder)]);
        Some(subst_vars(&self.shape(tag)?.payload, &mapping))
    }

    /// Why this vocabulary cannot be realized, if it cannot. The backend
    /// derives its glue from the payload types, so each must have a flat form,
    /// and each tag must be one the program can spell.
    pub fn validate(&self) -> Result<(), String> {
        let mut seen = HashSet::new();
        let names = self.tag_names().chain(self.key_tag_names());
        for name in names {
            if name.is_empty() || is_list_tag(name) {
                return Err(format!("`{name}` is not a tag a host can declare"));
            }
            if !seen.insert(name) {
                return Err(format!("the tag `{name}` is declared twice"));
            }
        }
        for event in &self.events {
            let wire = event.decode.as_ref().map_or(&event.payload, |d| &d.wire);
            if leaves(wire).is_none() {
                return Err(format!(
                    "the `{}` event's host values must be numbers, strings or records of them",
                    event.name
                ));
            }
        }
        for event in &self.events {
            if let Some(function) = event.decoder()
                && self.decoder_ty(function) != event.decoder_ty()
            {
                return Err(format!(
                    "the decoder `{function}` is given two different types"
                ));
            }
        }
        for shape in &self.shapes {
            let streamed = shape_leaves(&shape.payload).ok_or_else(|| {
                format!(
                    "the `{}` shape must be a record of numbers, strings and at most one list of them",
                    shape.name
                )
            })?;
            let fits = matches!(
                (&shape.scene, &streamed.list),
                (SceneCalls::Call(_), None) | (SceneCalls::Stream { .. }, Some(_))
            );
            if !fits {
                return Err(format!(
                    "the `{}` shape's scene calls do not match whether its payload holds a list",
                    shape.name
                ));
            }
        }
        Ok(())
    }
}

fn float(label: &str) -> (&str, Ty) {
    (label, Ty::Float)
}

fn record<const N: usize>(fields: [(&str, Ty); N]) -> Ty {
    Ty::Record(row(fields))
}

fn row<const N: usize>(fields: [(&str, Ty); N]) -> Row {
    Row::of(
        fields
            .into_iter()
            .map(|(label, field)| (label.to_string(), field)),
    )
}

/// The list a shape payload holds: `list` under the binder every stored payload
/// names its list with.
pub fn payload_list(item: Ty) -> Ty {
    list(LIST_BINDER, item)
}

/// `μbinder. [Empty, Link: {0: item, 1: binder}]`
pub fn list(binder: TypeVar, item: Ty) -> Ty {
    let link = record([("0", item), ("1", Ty::Var(binder))]);
    Ty::Rec(
        binder,
        Box::new(Ty::Variant(row([("Empty", Ty::Unit), ("Link", link)]))),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn paths(leaves: &[Leaf]) -> Vec<String> {
        leaves.iter().map(|l| l.path.join(".")).collect()
    }

    #[test]
    fn leaves_run_left_to_right_through_nested_records() {
        let ty = record([
            ("at", record([("x", Ty::Float), ("y", Ty::Float)])),
            ("hard", Ty::Bool),
        ]);
        let found = leaves(&ty).unwrap();
        assert_eq!(paths(&found), ["at.x", "at.y", "hard"]);
        assert_eq!(found[2].ty, Ty::Bool);
    }

    #[test]
    fn a_scalar_is_one_leaf_at_the_root_and_unit_has_none() {
        assert_eq!(paths(&leaves(&Ty::Str).unwrap()), [""]);
        assert_eq!(leaves(&Ty::Unit), Some(Vec::new()));
    }

    #[test]
    fn a_type_without_a_flat_form_has_no_leaves() {
        assert_eq!(leaves(&Ty::Func(Vec::new(), Box::new(Ty::Unit))), None);
        assert_eq!(leaves(&record([("f", Ty::Unit)])), None);
        assert_eq!(leaves(&payload_list(Ty::Float)), None);
        assert_eq!(leaves(&Ty::Record(Row::Var(0))), None);
    }

    #[test]
    fn a_list_is_recognized_by_its_shape_and_gives_its_element() {
        let point = record([("x", Ty::Float), ("y", Ty::Float)]);
        assert_eq!(list_element(&payload_list(point.clone())), Some(&point));
        assert_eq!(list_element(&point), None);
        assert_eq!(list_element(&Ty::Rec(0, Box::new(Ty::Unit))), None);
    }

    #[test]
    fn a_shape_streams_its_head_leaves_in_field_order_and_its_one_list() {
        let polyline = Vocab::turtle().shape("Polyline").unwrap().payload.clone();
        let streamed = shape_leaves(&polyline).unwrap();
        assert_eq!(paths(&streamed.head), ["color"]);
        let list = streamed.list.unwrap();
        assert_eq!(list.field, "points");
        assert_eq!(paths(&list.element), ["x", "y"]);

        let line = Vocab::turtle().shape("Line").unwrap().payload.clone();
        let streamed = shape_leaves(&line).unwrap();
        assert_eq!(paths(&streamed.head), ["x1", "y1", "x2", "y2", "color"]);
        assert!(streamed.list.is_none());
    }

    #[test]
    fn a_shape_with_two_lists_has_no_stream() {
        let two = record([
            ("a", payload_list(Ty::Float)),
            ("b", payload_list(Ty::Float)),
        ]);
        assert_eq!(shape_leaves(&two), None);
        assert_eq!(shape_leaves(&Ty::Float), None);
    }

    #[test]
    fn a_shape_payload_renames_the_list_binder_per_use() {
        let turtle = Vocab::turtle();
        let Some(Ty::Record(row)) = turtle.shape_payload("Polyline", 7) else {
            panic!("a polyline is a record");
        };
        let Row::Extend { field, .. } = row else {
            panic!("a polyline has fields");
        };
        assert!(matches!(*field, Ty::Rec(7, _)), "{field:?}");
        assert_eq!(turtle.shape_payload("Frobnicate", 0), None);
    }

    #[test]
    fn the_turtle_decodes_both_key_events_with_one_function() {
        let turtle = Vocab::turtle();
        assert_eq!(turtle.decoders(), ["key_of"]);
        assert_eq!(
            turtle.decoder_ty("key_of"),
            Some(Ty::Func(
                vec![Ty::Str],
                Box::new(turtle.keys.instantiate(0))
            ))
        );
    }

    #[test]
    fn a_decoder_given_two_types_is_ill_formed() {
        let mut vocab = Vocab::turtle();
        vocab.events[0].decode = Some(Decode {
            wire: Ty::Str,
            function: "key_of".to_string(),
        });
        let error = vocab.validate().unwrap_err();
        assert!(error.contains("two different types"), "{error}");
    }
}
