//! The glue an interactive host calls (ADR 0015): the `update` and `draw`
//! entry points, one event constructor per tag `update` handles, and the walk
//! that streams `draw`'s picture out through the `scene.*` imports. The host
//! never reads goat's heap, so everything that touches variant tags, payload
//! slots or record layouts lives here, over types the checker has fixed.
//!
//! Both are derived from the host's vocabulary (ADR 0020), not written per
//! tag. A constructor takes the leaves of its host values, left to right, and
//! rebuilds the records around them; a shape streams as its leaves, with a
//! list as a begin, one call per element and an end.

use std::collections::BTreeMap;

use super::{FnCx, Mono, Subst, field_index, positional_fields, variant_row};
use crate::canon::{ground_fields, layout_fields};
use crate::mir::*;
use goat_checker::Target;
use goat_checker::ty::Ty;
use goat_checker::vocab::{Leaf, SceneCalls, leaves, shape_leaves};
use std::collections::HashMap;

/// The most shapes plus vertices one frame may stream before it traps.
const PICTURE_BUDGET: i64 = 100_000;

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
        let vocab = self.vocab;
        let mut ctors = Vec::new();
        for (label, payload) in payloads {
            let tag = self.tags[&label];
            let event = vocab
                .event(&label)
                .expect("the checker admits only events the host sends");
            let wire = event.decode.as_ref().map_or(&event.payload, |d| &d.wire);
            let mut cx = FnCx::new(Subst::new());
            let mut params = Vec::new();
            let mut values = HashMap::new();
            for leaf in leaves(wire).expect("the host's event values are flat") {
                let ty = self.lower_ty(&leaf.ty);
                let param = cx.fresh(ty);
                params.push((param, ty));
                values.insert(leaf.path, param);
            }
            let body = if payload == Ty::Unit {
                Expr::AllocVariant(layout, tag, Vec::new())
            } else {
                let wire_ty = self.ground(wire, &Subst::new());
                let mut value = self.assemble(&wire_ty, &mut Vec::new(), &values);
                if let Some(decode) = &event.decode {
                    let decoder = self.decoder(&decode.function);
                    value = Expr::CallDirect(decoder, vec![value]);
                }
                match value {
                    Expr::Local(_) => Expr::AllocVariant(layout, tag, vec![value]),
                    _ => {
                        let held = cx.fresh(self.lower_ty(&payload));
                        lets(
                            vec![(held, value)],
                            Expr::AllocVariant(layout, tag, vec![local(held)]),
                        )
                    }
                }
            };
            let ret = MTy::Ptr(HeapKind::Variant(layout));
            let func = self.push_func(cx.into_func(params, None, ret, body));
            ctors.push(EventCtor { label, func });
        }
        ctors
    }

    /// The value of the ground type `ty` whose leaf at each path is in
    /// `values`: records are rebuilt around them in layout order.
    fn assemble(
        &mut self,
        ty: &Ty,
        path: &mut Vec<String>,
        values: &HashMap<Vec<String>, Local>,
    ) -> Expr {
        let Ty::Record(row) = ty else {
            return local(values.get(path.as_slice()).copied().unwrap_or_else(|| {
                unreachable!("the host's event values cover every leaf of the payload")
            }));
        };
        let MTy::Ptr(HeapKind::Record(layout)) = self.lower_ty(ty) else {
            unreachable!("a record lowers to a record layout");
        };
        let fields: Vec<(String, Ty)> = layout_fields(row)
            .map(|(label, field)| (label.clone(), field.clone()))
            .collect();
        let slots = fields
            .into_iter()
            .map(|(label, field)| {
                path.push(label);
                let slot = self.assemble(&field, path, values);
                path.pop();
                slot
            })
            .collect();
        Expr::AllocRecord(layout, slots)
    }

    /// The host's decoder `function`, specialized at the type its vocabulary
    /// gives it.
    fn decoder(&mut self, function: &str) -> FuncId {
        let decoders = self.decoders;
        let decoder = decoders
            .iter()
            .find(|d| d.function == function)
            .expect("lowering binds every decoder the vocabulary names");
        let scope = Subst::new();
        let use_ty = self.ground(&self.typed.node_types[&decoder.binding.use_id], &scope);
        let target = Target::Named(decoder.symbol);
        self.specialize_at(&scope, target, use_ty, decoder.binding.span)
            .0
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
        let vocab = self.vocab;
        let id = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let (shape, budget) = (cx.fresh(kind), cx.fresh(MTy::Int));
        let mut arms = Vec::new();
        for (label, payload) in &payloads {
            let tag = self.tags[label];
            let spec = vocab
                .shape(label)
                .expect("the checker admits only shapes the host draws");
            let streamed = shape_leaves(&spec.payload).expect("the host's shape is flat");
            let record = cx.fresh(self.lower_ty(payload));
            let mut steps = vec![(record, Expr::Payload(shape, tag, 0))];
            let head = self.read_leaves(&mut cx, &mut steps, record, payload, &streamed.head);
            let head_tys: Vec<MTy> = streamed
                .head
                .iter()
                .map(|leaf| self.lower_ty(&leaf.ty))
                .collect();
            let body = match (&spec.scene, &streamed.list) {
                (SceneCalls::Call(name), _) => {
                    let call = self.scene(name, head_tys);
                    steps.push((cx.fresh(MTy::Unit), Expr::CallForeign(call, head)));
                    local(budget)
                }
                (
                    SceneCalls::Stream {
                        begin,
                        element,
                        end,
                    },
                    Some(list),
                ) => {
                    let points_ty = self.field_ty(payload, &list.field);
                    let points = cx.fresh(self.lower_ty(&points_ty));
                    let left = cx.fresh(MTy::Int);
                    let walk = self.points_walk(&points_ty, element, &list.element);
                    let begin = self.scene(begin, head_tys);
                    let end = self.scene(end, Vec::new());
                    let slot = self.slot(payload, &list.field);
                    steps.push((points, Expr::Field(record, slot)));
                    steps.push((cx.fresh(MTy::Unit), Expr::CallForeign(begin, head)));
                    let walked = match walk {
                        Some(walk) => Expr::CallDirect(walk, vec![local(points), local(budget)]),
                        None => local(budget),
                    };
                    steps.push((left, walked));
                    steps.push((cx.fresh(MTy::Unit), Expr::CallForeign(end, Vec::new())));
                    local(left)
                }
                (SceneCalls::Stream { .. }, None) => {
                    unreachable!("a streamed shape holds a list")
                }
            };
            arms.push((tag, lets(steps, body)));
        }
        let params = vec![(shape, kind), (budget, MTy::Int)];
        self.out[id.0 as usize] =
            Some(cx.into_func(params, None, MTy::Int, switch_on(shape, arms)));
        id
    }

    /// `(points, budget) -> budget`: one `scene.<element>` call per element,
    /// if the list can hold any.
    fn points_walk(&mut self, points_ty: &Ty, element: &str, leaves: &[Leaf]) -> Option<FuncId> {
        let (point, link) = self.list_item(points_ty)?;
        let list = self.lower_ty(points_ty);
        let leaf_tys = leaves.iter().map(|leaf| self.lower_ty(&leaf.ty)).collect();
        let call = self.scene(element, leaf_tys);
        let id = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let (points, budget) = (cx.fresh(list), cx.fresh(MTy::Int));
        let point_ty = self.lower_ty(&point);
        let (head, rest) = (cx.fresh(point_ty), cx.fresh(list));
        let mut steps = vec![
            (head, Expr::Payload(points, link, 0)),
            (rest, Expr::Payload(points, link, 1)),
        ];
        let args = self.read_leaves(&mut cx, &mut steps, head, &point, leaves);
        steps.push((cx.fresh(MTy::Unit), Expr::CallForeign(call, args)));
        let step = spend(budget, |remaining| {
            lets(
                steps,
                Expr::TailCall(Callee::Direct(id), vec![local(rest), remaining]),
            )
        });
        let body = Expr::Switch(points, vec![(link, step)], Box::new(local(budget)));
        let params = vec![(points, list), (budget, MTy::Int)];
        self.out[id.0 as usize] = Some(cx.into_func(params, None, MTy::Int, body));
        Some(id)
    }

    /// The locals holding each of `leaves` in `record`, whose ground type is
    /// `record_ty`, read by `steps`.
    fn read_leaves(
        &mut self,
        cx: &mut FnCx,
        steps: &mut Vec<(Local, Expr)>,
        record: Local,
        record_ty: &Ty,
        leaves: &[Leaf],
    ) -> Vec<Local> {
        leaves
            .iter()
            .map(|leaf| {
                let (mut holder, mut holder_ty) = (record, record_ty.clone());
                for label in &leaf.path {
                    let ty = self.field_ty(&holder_ty, label);
                    let next = cx.fresh(self.lower_ty(&ty));
                    steps.push((next, Expr::Field(holder, self.slot(&holder_ty, label))));
                    (holder, holder_ty) = (next, ty);
                }
                holder
            })
            .collect()
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
