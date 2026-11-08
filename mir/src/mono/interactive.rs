//! The glue an interactive host calls (ADR 0015): the `update` and `draw`
//! entry points, one event constructor per tag `update` handles, and the walk
//! that streams `draw`'s picture out through the `scene.*` imports. The host
//! never reads goat's heap, so everything that touches variant tags, payload
//! slots or record layouts lives here, over types the checker has fixed.

use std::collections::BTreeMap;

use super::{FnCx, Mono, Subst, field_index, positional_fields, variant_row};
use crate::canon::ground_fields;
use crate::mir::*;
use goat_checker::ty::Ty;
use goat_checker::vocab::KEY_TAGS;

/// The most shapes plus vertices one frame may stream before it traps.
const PICTURE_BUDGET: i64 = 100_000;

/// The `KeyboardEvent.key` of each arrow, and the `Key` tag it maps to.
const ARROWS: [(&str, &str); 4] = [
    ("ArrowUp", "Up"),
    ("ArrowDown", "Down"),
    ("ArrowLeft", "Left"),
    ("ArrowRight", "Right"),
];

fn local(l: Local) -> Expr {
    Expr::Local(l)
}

fn int(n: i64) -> Expr {
    Expr::Const(Const::Int(n))
}

fn lets(bindings: Vec<(Local, Expr)>, body: Expr) -> Expr {
    bindings.into_iter().rev().fold(body, |body, (l, value)| {
        Expr::Let(l, Box::new(value), Box::new(body))
    })
}

/// Take one from `budget`, trapping first if none is left.
fn spend(budget: Local, body: impl FnOnce(Expr) -> Expr) -> Expr {
    let left = Expr::BinInt(IntOp::Sub, Box::new(local(budget)), Box::new(int(1)));
    Expr::If(
        Box::new(Expr::Cmp(
            CmpOp::Le,
            Box::new(local(budget)),
            Box::new(int(0)),
        )),
        Box::new(Expr::Trap("this picture has too many shapes".into())),
        Box::new(body(left)),
    )
}

/// `Switch` on `scrutinee`; the last arm doubles as the default.
fn switch_on(scrutinee: Local, mut arms: Vec<(u32, Expr)>) -> Expr {
    let default = arms
        .pop()
        .map_or_else(|| Expr::Trap("no arm matches".into()), |(_, arm)| arm);
    Expr::Switch(scrutinee, arms, Box::new(default))
}

impl Mono<'_> {
    /// The host-facing functions of an interactive program, whose root type
    /// `root_ty` is the record of its `draw`, `init` and `update`.
    pub(super) fn interactive(&mut self, root_ty: &Ty) -> Interactive {
        let Ty::Record(row) = root_ty else {
            unreachable!("an interactive root is a record");
        };
        let fields: Vec<(&String, &Ty)> = crate::canon::layout_fields(row).collect();
        let slot = |label: &str| {
            fields
                .iter()
                .position(|(l, _)| *l == label)
                .expect("the root record holds init, update and draw")
        };
        let (draw_slot, init_slot, update_slot) = (slot("draw"), slot("init"), slot("update"));
        let (Ty::Func(update_args, _), Ty::Func(_, shapes_ty)) =
            (fields[update_slot].1, fields[draw_slot].1)
        else {
            unreachable!("the checker makes update and draw functions");
        };
        let model = self.lower_ty(&update_args[0]);
        let event = self.lower_ty(&update_args[1]);
        let update_closure = self.lower_ty(fields[update_slot].1);
        let draw_closure = self.lower_ty(fields[draw_slot].1);
        let MTy::Ptr(HeapKind::Closure(update_sig)) = update_closure else {
            unreachable!("function type lowers to a closure");
        };
        let update_ret = self.sigs[update_sig.0 as usize].ret;
        let (closure, model_local, event_local) = (Local(0), Local(1), Local(2));
        let update = self.push_func(Func {
            params: vec![
                (closure, update_closure),
                (model_local, model),
                (event_local, event),
            ],
            env: None,
            ret: update_ret,
            body: Expr::CallClosure(
                Box::new(local(closure)),
                vec![local(model_local), local(event_local)],
            ),
            locals: BTreeMap::new(),
        });
        let events = self.event_ctors(&update_args[1]);
        let draw = self.draw_func(draw_closure, model, shapes_ty);
        Interactive {
            draw_slot,
            init_slot,
            update_slot,
            update,
            draw,
            events,
            model,
        }
    }

    fn event_ctors(&mut self, event_ty: &Ty) -> Vec<EventCtor> {
        let MTy::Ptr(HeapKind::Variant(layout)) = self.lower_ty(event_ty) else {
            unreachable!("an event is a variant");
        };
        let payloads: Vec<(String, Ty)> = ground_fields(&variant_row(event_ty))
            .map(|(label, payload)| (label.clone(), payload.clone()))
            .collect();
        let mut ctors = Vec::new();
        for (label, payload) in payloads {
            let tag = self.tags[&label];
            let mut cx = FnCx::new(Subst::new());
            let (params, body) = match label.as_str() {
                "Tick" => {
                    let dt = cx.fresh(MTy::Float);
                    let body = Expr::AllocVariant(layout, tag, vec![local(dt)]);
                    (vec![(dt, MTy::Float)], body)
                }
                "KeyDown" | "KeyUp" => {
                    let key = cx.fresh(MTy::Ptr(HeapKind::Str));
                    let keyed = self.key_of(&mut cx, key, &payload);
                    let event = cx.fresh(self.lower_ty(&payload));
                    let body = lets(
                        vec![(event, keyed)],
                        Expr::AllocVariant(layout, tag, vec![local(event)]),
                    );
                    (vec![(key, MTy::Ptr(HeapKind::Str))], body)
                }
                "PointerMove" | "PointerDown" | "PointerUp" => {
                    let MTy::Ptr(HeapKind::Record(point)) = self.lower_ty(&payload) else {
                        unreachable!("a pointer payload is a record");
                    };
                    let (x, y) = (cx.fresh(MTy::Float), cx.fresh(MTy::Float));
                    let at = Expr::AllocRecord(point, vec![local(x), local(y)]);
                    let body = Expr::AllocVariant(layout, tag, vec![at]);
                    (vec![(x, MTy::Float), (y, MTy::Float)], body)
                }
                _ => unreachable!("the checker admits only events the host sends"),
            };
            let ret = MTy::Ptr(HeapKind::Variant(layout));
            let func = self.push_func(cx.into_func(params, None, ret, body));
            ctors.push(EventCtor { label, func });
        }
        ctors
    }

    /// The `Key` of the `KeyboardEvent.key` string `key`: an arrow's name maps
    /// to its tag and anything else is `Other(key)`.
    fn key_of(&mut self, cx: &mut FnCx, key: Local, key_ty: &Ty) -> Expr {
        let MTy::Ptr(HeapKind::Variant(layout)) = self.lower_ty(key_ty) else {
            unreachable!("a key is a variant");
        };
        debug_assert!(KEY_TAGS.iter().all(|t| self.tags.contains_key(*t)));
        let other = Expr::AllocVariant(layout, self.tags["Other"], vec![local(key)]);
        ARROWS.iter().rev().fold(other, |otherwise, (name, tag)| {
            let literal = cx.fresh(MTy::Ptr(HeapKind::Str));
            let data = self.intern(name);
            let arrow = Expr::AllocVariant(layout, self.tags[*tag], Vec::new());
            Expr::Let(
                literal,
                Box::new(Expr::StrLit(data)),
                Box::new(Expr::If(
                    Box::new(Expr::StrEq(key, literal)),
                    Box::new(arrow),
                    Box::new(otherwise),
                )),
            )
        })
    }

    /// `(closure, model) -> Unit`: run `draw` and stream the shapes it returns
    /// between `scene.begin` and `scene.end`. The shapes are dropped when the
    /// walk is done.
    fn draw_func(&mut self, closure_ty: MTy, model_ty: MTy, shapes_ty: &Ty) -> FuncId {
        let walk = self.shapes_walk(shapes_ty);
        let begin = self.scene("begin", Vec::new());
        let end = self.scene("end", Vec::new());
        let mut cx = FnCx::new(Subst::new());
        let shapes_mty = self.lower_ty(shapes_ty);
        let (closure, model, shapes) = (
            cx.fresh(closure_ty),
            cx.fresh(model_ty),
            cx.fresh(shapes_mty),
        );
        let mut steps = vec![
            (
                shapes,
                Expr::CallClosure(Box::new(local(closure)), vec![local(model)]),
            ),
            (cx.fresh(MTy::Unit), Expr::CallForeign(begin, Vec::new())),
        ];
        if let Some(walk) = walk {
            steps.push((
                cx.fresh(MTy::Unit),
                Expr::CallDirect(walk, vec![local(shapes), int(PICTURE_BUDGET)]),
            ));
        }
        steps.push((cx.fresh(MTy::Unit), Expr::CallForeign(end, Vec::new())));
        let body = lets(steps, Expr::Const(Const::Unit));
        self.push_func(cx.into_func(
            vec![(closure, closure_ty), (model, model_ty)],
            None,
            MTy::Unit,
            body,
        ))
    }

    /// `(shapes, budget) -> Unit`, if the picture can hold any shape.
    fn shapes_walk(&mut self, shapes_ty: &Ty) -> Option<FuncId> {
        let (item, link) = self.list_item(shapes_ty)?;
        // An empty picture leaves the item type unconstrained.
        let Ty::Variant(_) = item.unfold_head() else {
            return None;
        };
        let list = self.lower_ty(shapes_ty);
        let shape = self.shape_func(&item);

        let id = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let (shapes, budget) = (cx.fresh(list), cx.fresh(MTy::Int));
        let item_ty = self.lower_ty(&item);
        let (head, rest, left) = (cx.fresh(item_ty), cx.fresh(list), cx.fresh(MTy::Int));
        let step = spend(budget, |remaining| {
            lets(
                vec![
                    (head, Expr::Payload(shapes, link, 0)),
                    (rest, Expr::Payload(shapes, link, 1)),
                    (left, Expr::CallDirect(shape, vec![local(head), remaining])),
                ],
                Expr::TailCall(Callee::Direct(id), vec![local(rest), local(left)]),
            )
        });
        let body = Expr::Switch(
            shapes,
            vec![(link, step)],
            Box::new(Expr::Const(Const::Unit)),
        );
        let params = vec![(shapes, list), (budget, MTy::Int)];
        self.out[id.0 as usize] = Some(cx.into_func(params, None, MTy::Unit, body));
        Some(id)
    }

    /// `(shape, budget) -> budget`: stream one shape, returning what its
    /// vertices left of the budget.
    fn shape_func(&mut self, shape_ty: &Ty) -> FuncId {
        let kind = self.lower_ty(shape_ty);
        let payloads: Vec<(String, Ty)> = ground_fields(&variant_row(shape_ty))
            .map(|(label, payload)| (label.clone(), payload.clone()))
            .collect();
        let id = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let (shape, budget) = (cx.fresh(kind), cx.fresh(MTy::Int));
        let mut arms = Vec::new();
        for (label, payload) in &payloads {
            let tag = self.tags[label];
            let record = cx.fresh(self.lower_ty(payload));
            let read = |m: &Self, name: &str| Expr::Field(record, m.slot(payload, name));
            let mut steps = vec![(record, Expr::Payload(shape, tag, 0))];
            let body = match label.as_str() {
                "Line" => {
                    let arg_tys = [
                        MTy::Float,
                        MTy::Float,
                        MTy::Float,
                        MTy::Float,
                        MTy::Ptr(HeapKind::Str),
                    ];
                    let args: Vec<Local> = arg_tys.into_iter().map(|ty| cx.fresh(ty)).collect();
                    for (arg, name) in args.iter().zip(["x1", "y1", "x2", "y2", "color"]) {
                        steps.push((*arg, read(self, name)));
                    }
                    let line = self.scene(
                        "line",
                        [MTy::Float; 4]
                            .into_iter()
                            .chain([MTy::Ptr(HeapKind::Str)])
                            .collect(),
                    );
                    steps.push((cx.fresh(MTy::Unit), Expr::CallForeign(line, args)));
                    local(budget)
                }
                "Polyline" => {
                    let points_ty = self.field_ty(payload, "points");
                    let points_mty = self.lower_ty(&points_ty);
                    let (color, points, left) = (
                        cx.fresh(MTy::Ptr(HeapKind::Str)),
                        cx.fresh(points_mty),
                        cx.fresh(MTy::Int),
                    );
                    let walk = self.points_walk(&points_ty);
                    let begin = self.scene("polyline_begin", vec![MTy::Ptr(HeapKind::Str)]);
                    let end = self.scene("polyline_end", Vec::new());
                    steps.push((color, read(self, "color")));
                    steps.push((points, read(self, "points")));
                    steps.push((cx.fresh(MTy::Unit), Expr::CallForeign(begin, vec![color])));
                    let walked = match walk {
                        Some(walk) => Expr::CallDirect(walk, vec![local(points), local(budget)]),
                        None => local(budget),
                    };
                    steps.push((left, walked));
                    steps.push((cx.fresh(MTy::Unit), Expr::CallForeign(end, Vec::new())));
                    local(left)
                }
                _ => unreachable!("the checker admits only shapes the host draws"),
            };
            arms.push((tag, lets(steps, body)));
        }
        let params = vec![(shape, kind), (budget, MTy::Int)];
        self.out[id.0 as usize] =
            Some(cx.into_func(params, None, MTy::Int, switch_on(shape, arms)));
        id
    }

    /// `(points, budget) -> budget`: one `scene.vertex` per point, if the list
    /// can hold any.
    fn points_walk(&mut self, points_ty: &Ty) -> Option<FuncId> {
        let (point, link) = self.list_item(points_ty)?;
        let list = self.lower_ty(points_ty);
        let vertex = self.scene("vertex", vec![MTy::Float; 2]);
        let id = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let (points, budget) = (cx.fresh(list), cx.fresh(MTy::Int));
        let point_ty = self.lower_ty(&point);
        let (head, rest) = (cx.fresh(point_ty), cx.fresh(list));
        let (x, y) = (cx.fresh(MTy::Float), cx.fresh(MTy::Float));
        let (x_slot, y_slot) = (self.slot(&point, "x"), self.slot(&point, "y"));
        let step = spend(budget, |remaining| {
            lets(
                vec![
                    (head, Expr::Payload(points, link, 0)),
                    (rest, Expr::Payload(points, link, 1)),
                    (x, Expr::Field(head, x_slot)),
                    (y, Expr::Field(head, y_slot)),
                    (cx.fresh(MTy::Unit), Expr::CallForeign(vertex, vec![x, y])),
                ],
                Expr::TailCall(Callee::Direct(id), vec![local(rest), remaining]),
            )
        });
        let body = Expr::Switch(points, vec![(link, step)], Box::new(local(budget)));
        let params = vec![(points, list), (budget, MTy::Int)];
        self.out[id.0 as usize] = Some(cx.into_func(params, None, MTy::Int, body));
        Some(id)
    }

    /// The element type and `Link` tag of a list type that can have elements.
    fn list_item(&self, list_ty: &Ty) -> Option<(Ty, u32)> {
        let row = variant_row(list_ty);
        let (_, link) = ground_fields(&row).find(|(label, _)| *label == "Link")?;
        let item = positional_fields(link)?.into_iter().next()?;
        Some((item, self.tags["Link"]))
    }

    fn field_ty(&self, record_ty: &Ty, label: &str) -> Ty {
        let Ty::Record(row) = record_ty.unfold_head() else {
            unreachable!("a shape payload is a record");
        };
        ground_fields(&row)
            .find(|(l, _)| *l == label)
            .map(|(_, ty)| ty.clone())
            .expect("the checker gives each shape its fields")
    }

    fn slot(&self, record_ty: &Ty, label: &str) -> usize {
        let Ty::Record(row) = record_ty.unfold_head() else {
            unreachable!("a shape payload is a record");
        };
        field_index(&row, label)
    }

    /// A function id to fill in once its body can name itself.
    fn reserve(&mut self) -> FuncId {
        self.out.push(None);
        FuncId(self.out.len() as u32 - 1)
    }

    /// The import `scene.name`, registered on first use.
    fn scene(&mut self, name: &str, params: Vec<MTy>) -> ForeignId {
        self.register_import(ForeignFn {
            module: "scene".into(),
            name: name.into(),
            params,
            ret: MTy::Unit,
        })
    }
}
