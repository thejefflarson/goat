//! The glue that carries a model across a reload (ADR 0035): `snapshot` turns
//! a model into an image, `refresh` rebuilds a model of the new program's type
//! from an image. Both are generated per type here, in MIR, so the
//! interpreter runs them and a differential test can compare it with wasm.
//!
//! An image is a value of one fixed `Node` layout that every module builds the
//! same way, so a module can read the image another module wrote. Records and
//! variants carry their field and tag names; a method carries the name of the
//! top-level binding that made it; an object more than one reference points at
//! is written once (`Def`) and pointed at afterwards (`Ref`).
//!
//! The functions consume their arguments, so a snapshot takes the model apart
//! as it goes: a cell is freed before its children are visited, which leaves
//! each child with its own count and no one else's. That is what lets a count
//! above one mean "shared".

use std::collections::{BTreeMap, HashMap, HashSet};

use super::{FnCx, Lambda, Mono, Subst, match_ty, payload_fields, positional_fields, variant_row};
use crate::canon::{canonical, ground_fields};
use crate::mir::*;
use goat_checker::captures::for_each_node;
use goat_checker::hir::{self, ExprId, ExprKind, Span, Symbol};
use goat_checker::lower::SELF_NAME;
use goat_checker::ty::{Row, Ty, TypeVar};
use goat_checker::{Checked, Target};

const NIL: u32 = 0;
const CONS: u32 = 1;
const INT: u32 = 2;
const FLOAT: u32 = 3;
const BOOL: u32 = 4;
const UNIT: u32 = 5;
const STR: u32 = 6;
const FIELD: u32 = 7;
const REC: u32 = 8;
const VAR: u32 = 9;
const LIST: u32 = 10;
const METHOD: u32 = 11;
const DEF: u32 = 12;
const REF: u32 = 13;
const PAIR: u32 = 14;
const ENTRY: u32 = 15;
const TAGS: u32 = 16;

/// A method literal in the program: the top-level binding it sits in, its
/// field label, and the first variable it captures that is not top-level.
#[derive(Debug, Clone)]
pub(super) struct Site {
    pub binding: String,
    pub label: String,
    pub expr: ExprId,
    pub span: Span,
    pub captured: Option<String>,
}

/// What the generated code needs to know about the program's own names.
#[derive(Default)]
pub(super) struct Names {
    pub sites: Vec<Site>,
    pub bindings: Vec<String>,
}

/// The type of the model: what `update` takes first.
pub(super) fn model_ty(root: &Ty) -> Ty {
    let Ty::Record(row) = root else {
        unreachable!("an interactive root is a record");
    };
    let (_, update) = ground_fields(row)
        .find(|(label, _)| *label == "update")
        .expect("the root record holds update");
    match update.unfold_head() {
        Ty::Func(args, _) => args[0].clone(),
        _ => unreachable!("the checker makes update a function"),
    }
}

enum Kind {
    Int,
    Float,
    Bool,
    Unit,
    Str,
    Func,
    Record(Vec<(String, Ty)>),
    Variant(Vec<(String, Ty)>),
    List(Ty),
}

fn kind(ty: &Ty) -> Kind {
    match ty.unfold_head() {
        Ty::Int => Kind::Int,
        Ty::Float => Kind::Float,
        Ty::Bool => Kind::Bool,
        Ty::Unit => Kind::Unit,
        Ty::Str => Kind::Str,
        Ty::Func(..) => Kind::Func,
        Ty::Record(row) => Kind::Record(owned_fields(&row)),
        head @ Ty::Variant(_) => {
            let tags = owned_fields(&variant_row(&head));
            let link = tags.iter().find(|(label, _)| label == "Link");
            let is_list = tags.len() == 2 && tags.iter().any(|(label, _)| label == "Empty");
            match link.and_then(|(_, payload)| positional_fields(payload)) {
                Some(fields) if is_list && fields.len() == 2 => Kind::List(fields[0].clone()),
                _ => Kind::Variant(tags),
            }
        }
        other => unreachable!("a model type is a value type, not {other:?}"),
    }
}

fn owned_fields(row: &goat_checker::ty::Row) -> Vec<(String, Ty)> {
    ground_fields(row)
        .map(|(label, ty)| (label.clone(), ty.clone()))
        .collect()
}

/// What the user calls a type, for the reasons a reset gives.
fn type_name(ty: &Ty) -> &'static str {
    match kind(ty) {
        Kind::Int => "Int",
        Kind::Float => "Number",
        Kind::Bool => "Bool",
        Kind::Unit => "Unit",
        Kind::Str => "String",
        Kind::Func => "Method",
        Kind::Record(_) => "Record",
        Kind::Variant(_) => "Tag",
        Kind::List(_) => "List",
    }
}

fn local(l: Local) -> Expr {
    Expr::Local(l)
}

fn int(n: i64) -> Expr {
    Expr::Const(Const::Int(n))
}

fn boxed(e: Expr) -> Box<Expr> {
    Box::new(e)
}

fn lets(bindings: Vec<(Local, Expr)>, body: Expr) -> Expr {
    bindings.into_iter().rev().fold(body, |body, (l, value)| {
        Expr::Let(l, boxed(value), boxed(body))
    })
}

/// The functions made so far, so each type's code is generated once.
pub(super) struct Gen<'g, 'a> {
    m: &'g mut Mono<'a>,
    names: &'g Names,
    node: LayoutId,
    node_ty: MTy,
    sites_ty: MTy,
    /// The closures `setup` builds for the sites a refresh rebinds to, and the
    /// site and type of each.
    site_slots: Vec<(ExprId, Ty)>,
    snaps: HashMap<Ty, FuncId>,
    snap_bodies: HashMap<Ty, FuncId>,
    refreshes: HashMap<(Ty, bool), FuncId>,
    rf_bodies: HashMap<(Ty, bool), FuncId>,
    results: HashMap<MTy, LayoutId>,
    type_ids: HashMap<Ty, i64>,
    lookup: FuncId,
    next_id: FuncId,
    find_field: FuncId,
    kind_name: FuncId,
    known_binding: FuncId,
    reverse_nodes: FuncId,
    reversals: HashMap<Ty, FuncId>,
}

enum Part<'p> {
    Text(&'p str),
    /// A string made by this module.
    Local(Local),
    /// A string the image holds, copied out of the old module's memory.
    Image(Local),
}

pub(super) struct Built {
    pub reload: Reload,
    /// One closure expression per slot of the sites record.
    pub site_closures: Vec<Expr>,
    pub sites_layout: LayoutId,
}

impl<'g, 'a> Gen<'g, 'a> {
    pub(super) fn build(
        m: &'g mut Mono<'a>,
        names: &'g Names,
        model: &Ty,
        root: &mut FnCx,
    ) -> Built {
        let mut node = BTreeMap::new();
        let n = MTy::Ptr(HeapKind::Variant(LayoutId(m.layouts.len() as u32)));
        let node_layout = LayoutId(m.layouts.len() as u32);
        for (tag, fields) in [
            (NIL, vec![]),
            (CONS, vec![n, n]),
            (INT, vec![MTy::Int]),
            (FLOAT, vec![MTy::Float]),
            (BOOL, vec![MTy::Bool]),
            (UNIT, vec![]),
            (STR, vec![MTy::Ptr(HeapKind::Str)]),
            (FIELD, vec![MTy::Ptr(HeapKind::Str), n]),
            (REC, vec![n]),
            (VAR, vec![MTy::Ptr(HeapKind::Str), n]),
            (LIST, vec![n]),
            (METHOD, vec![MTy::Ptr(HeapKind::Str)]),
            (DEF, vec![MTy::Int, n]),
            (REF, vec![MTy::Int]),
            (PAIR, vec![n, n]),
            (ENTRY, vec![MTy::Int, MTy::Int, MTy::Int]),
        ] {
            node.insert(tag, fields);
        }
        m.layouts.push(Layout::Variant(node));
        let sites_layout = LayoutId(m.layouts.len() as u32);
        m.layouts.push(Layout::Record(Vec::new()));
        let mut g = Gen {
            m,
            names,
            node: node_layout,
            node_ty: n,
            sites_ty: MTy::Ptr(HeapKind::Record(sites_layout)),
            site_slots: Vec::new(),
            snaps: HashMap::new(),
            snap_bodies: HashMap::new(),
            refreshes: HashMap::new(),
            rf_bodies: HashMap::new(),
            results: HashMap::new(),
            type_ids: HashMap::new(),
            lookup: FuncId(0),
            next_id: FuncId(0),
            find_field: FuncId(0),
            kind_name: FuncId(0),
            known_binding: FuncId(0),
            reverse_nodes: FuncId(0),
            reversals: HashMap::new(),
        };
        g.helpers();
        let model = canonical(model);
        let snapshot = g.snapshot(&model);
        let (refresh, outcome) = g.refresh(&model);
        let part = g.part();
        let site_closures = g.site_closures(root);
        let closure_tys: Vec<MTy> = g
            .site_slots
            .clone()
            .iter()
            .map(|(_, ty)| g.m.lower_ty(ty))
            .collect();
        g.m.layouts[sites_layout.0 as usize] = Layout::Record(closure_tys);
        Built {
            reload: Reload {
                node: node_layout,
                snapshot,
                refresh,
                outcome,
                part,
            },
            site_closures,
            sites_layout,
        }
    }

    fn node(&self, tag: u32, fields: Vec<Expr>) -> Expr {
        Expr::AllocVariant(self.node, tag, fields)
    }

    fn nil(&self) -> Expr {
        self.node(NIL, Vec::new())
    }

    fn cons(&self, head: Expr, tail: Expr) -> Expr {
        self.node(CONS, vec![head, tail])
    }

    fn lit(&mut self, text: &str) -> Expr {
        Expr::StrLit(self.m.intern(text))
    }

    fn reserve(&mut self) -> FuncId {
        self.m.out.push(None);
        FuncId(self.m.out.len() as u32 - 1)
    }

    fn define(&mut self, id: FuncId, cx: FnCx, params: Vec<(Local, MTy)>, ret: MTy, body: Expr) {
        self.m.out[id.0 as usize] = Some(cx.into_func(params, None, ret, body));
    }

    /// A `Switch` on `scrutinee` whose arms are `arms` and whose default is
    /// `default`.
    fn switch(scrutinee: Local, arms: Vec<(u32, Expr)>, default: Expr) -> Expr {
        Expr::Switch(scrutinee, arms, boxed(default))
    }

    fn if_(cond: Expr, then: Expr, otherwise: Expr) -> Expr {
        Expr::If(boxed(cond), boxed(then), boxed(otherwise))
    }

    /// The layout of `Ok(value, table) | Fail(reason)` for values of `ty`.
    fn result(&mut self, ty: MTy) -> LayoutId {
        if let Some(&id) = self.results.get(&ty) {
            return id;
        }
        let id = LayoutId(self.m.layouts.len() as u32);
        let table = BTreeMap::from([
            (REFRESHED, vec![ty, self.node_ty]),
            (RESET, vec![self.node_ty]),
        ]);
        self.m.layouts.push(Layout::Variant(table));
        self.results.insert(ty, id);
        id
    }

    fn ok(&mut self, ty: MTy, value: Expr, table: Expr) -> Expr {
        let layout = self.result(ty);
        Expr::AllocVariant(layout, REFRESHED, vec![value, table])
    }

    fn fail(&mut self, ty: MTy, reason: Expr) -> Expr {
        let layout = self.result(ty);
        Expr::AllocVariant(layout, RESET, vec![reason])
    }

    /// `Fail` carrying the reason of `r`, a failed result of another type.
    fn forward(&mut self, ty: MTy, r: Local) -> Expr {
        self.fail(ty, Expr::Payload(r, RESET, 0))
    }

    /// A reason: its parts, a string each, as a chain. `dynamic` parts come
    /// from the image, whose string literals live in a block about to be
    /// freed, so they are copied out.
    fn reason(&mut self, cx: &mut FnCx, parts: &[Part<'_>]) -> Expr {
        let mut copies = Vec::new();
        let mut items = Vec::new();
        for part in parts {
            items.push(match part {
                Part::Text(text) => self.lit(text),
                Part::Local(s) => local(*s),
                Part::Image(s) => {
                    let copy = cx.fresh(MTy::Ptr(HeapKind::Str));
                    copies.push((copy, Expr::KeepStr(*s)));
                    local(copy)
                }
            });
        }
        let chain = items.into_iter().rev().fold(self.nil(), |rest, item| {
            let head = self.node(STR, vec![item]);
            self.cons(head, rest)
        });
        lets(copies, chain)
    }

    fn type_id(&mut self, ty: &Ty) -> i64 {
        let next = self.type_ids.len() as i64 + 1;
        *self.type_ids.entry(ty.clone()).or_insert(next)
    }

    fn helpers(&mut self) {
        let (n, string) = (self.node_ty, MTy::Ptr(HeapKind::Str));

        // lookup(table, key, type) -> value, or -1
        self.lookup = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let (table, key, ty) = (cx.fresh(n), cx.fresh(MTy::Int), cx.fresh(MTy::Int));
        let (entry, rest) = (cx.fresh(n), cx.fresh(n));
        let (k, t, value) = (cx.fresh(MTy::Int), cx.fresh(MTy::Int), cx.fresh(MTy::Int));
        let again = |rest| {
            Expr::TailCall(
                Callee::Direct(self.lookup),
                vec![local(rest), local(key), local(ty)],
            )
        };
        let step = lets(
            vec![
                (entry, Expr::Payload(table, CONS, 0)),
                (rest, Expr::Payload(table, CONS, 1)),
                (k, Expr::Payload(entry, ENTRY, 0)),
                (t, Expr::Payload(entry, ENTRY, 2)),
                (value, Expr::Payload(entry, ENTRY, 1)),
            ],
            Self::if_(
                Expr::Cmp(CmpOp::Eq, boxed(local(k)), boxed(local(key))),
                Self::if_(
                    Expr::Cmp(CmpOp::Eq, boxed(local(t)), boxed(local(ty))),
                    local(value),
                    again(rest),
                ),
                again(rest),
            ),
        );
        let body = Self::switch(table, vec![(CONS, step)], int(-1));
        let id = self.lookup;
        self.define(
            id,
            cx,
            vec![(table, n), (key, MTy::Int), (ty, MTy::Int)],
            MTy::Int,
            body,
        );

        // next_id(table) -> one past the newest entry's id
        self.next_id = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let (table, entry, id_local) = (cx.fresh(n), cx.fresh(n), cx.fresh(MTy::Int));
        let step = lets(
            vec![
                (entry, Expr::Payload(table, CONS, 0)),
                (id_local, Expr::Payload(entry, ENTRY, 1)),
            ],
            Expr::BinInt(IntOp::Add, boxed(local(id_local)), boxed(int(1))),
        );
        let body = Self::switch(table, vec![(CONS, step)], int(0));
        let id = self.next_id;
        self.define(id, cx, vec![(table, n)], MTy::Int, body);

        // find_field(fields, name) -> the field's node, or Nil
        self.find_field = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let (fields, name) = (cx.fresh(n), cx.fresh(string));
        let (field, rest, found) = (cx.fresh(n), cx.fresh(n), cx.fresh(string));
        let step = lets(
            vec![
                (field, Expr::Payload(fields, CONS, 0)),
                (rest, Expr::Payload(fields, CONS, 1)),
                (found, Expr::Payload(field, FIELD, 0)),
            ],
            Self::if_(
                Expr::StrEq(found, name),
                Expr::Payload(field, FIELD, 1),
                Expr::TailCall(
                    Callee::Direct(self.find_field),
                    vec![local(rest), local(name)],
                ),
            ),
        );
        let body = Self::switch(fields, vec![(CONS, step)], self.nil());
        let id = self.find_field;
        self.define(id, cx, vec![(fields, n), (name, string)], n, body);

        // kind_name(node) -> what the user calls the value the node holds
        self.kind_name = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let node = cx.fresh(n);
        let names = [
            (INT, "Int"),
            (FLOAT, "Number"),
            (BOOL, "Bool"),
            (UNIT, "Unit"),
            (STR, "String"),
            (REC, "Record"),
            (VAR, "Tag"),
            (LIST, "List"),
            (METHOD, "Method"),
        ];
        let arms = names
            .iter()
            .map(|(tag, text)| (*tag, self.lit(text)))
            .collect();
        let default = self.lit("Record");
        let body = Self::switch(node, arms, default);
        let id = self.kind_name;
        self.define(id, cx, vec![(node, n)], string, body);

        // reverse_nodes(chain, acc) -> the chain's nodes in reverse order
        self.reverse_nodes = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let (chain, acc) = (cx.fresh(n), cx.fresh(n));
        let (head, rest) = (cx.fresh(n), cx.fresh(n));
        let step = lets(
            vec![
                (head, Expr::Payload(chain, CONS, 0)),
                (rest, Expr::Payload(chain, CONS, 1)),
            ],
            Expr::TailCall(
                Callee::Direct(self.reverse_nodes),
                vec![local(rest), self.cons(local(head), local(acc))],
            ),
        );
        let body = Self::switch(chain, vec![(CONS, step)], local(acc));
        let id = self.reverse_nodes;
        self.define(id, cx, vec![(chain, n), (acc, n)], n, body);

        // known_binding(name) -> whether the program has a top-level binding so called
        self.known_binding = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let name = cx.fresh(string);
        let mut body = Expr::Const(Const::Bool(false));
        for binding in &self.names.bindings {
            let text = self.lit(binding);
            let at = cx.fresh(string);
            body = Expr::Let(
                at,
                boxed(text),
                boxed(Self::if_(
                    Expr::StrEq(name, at),
                    Expr::Const(Const::Bool(true)),
                    body,
                )),
            );
        }
        let id = self.known_binding;
        self.define(id, cx, vec![(name, string)], MTy::Bool, body);
    }

    /// `(reason, index) -> string`: the `index`th part of a reason.
    fn part(&mut self) -> FuncId {
        let (n, string) = (self.node_ty, MTy::Ptr(HeapKind::Str));
        let id = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let (reason, index) = (cx.fresh(n), cx.fresh(MTy::Int));
        let (head, rest, text) = (cx.fresh(n), cx.fresh(n), cx.fresh(string));
        let step = lets(
            vec![
                (head, Expr::Payload(reason, CONS, 0)),
                (rest, Expr::Payload(reason, CONS, 1)),
                (text, Expr::Payload(head, STR, 0)),
            ],
            Self::if_(
                Expr::Cmp(CmpOp::Eq, boxed(local(index)), boxed(int(0))),
                local(text),
                Expr::TailCall(
                    Callee::Direct(id),
                    vec![
                        local(rest),
                        Expr::BinInt(IntOp::Sub, boxed(local(index)), boxed(int(1))),
                    ],
                ),
            ),
        );
        let empty = self.lit("");
        let body = Self::switch(reason, vec![(CONS, step)], empty);
        self.define(id, cx, vec![(reason, n), (index, MTy::Int)], string, body);
        id
    }

    // ---- snapshot ----

    fn snapshot(&mut self, model: &Ty) -> FuncId {
        let n = self.node_ty;
        let body = self.snap_body(model);
        let model_ty = self.m.lower_ty(model);
        let id = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let (value, pair, image) = (cx.fresh(model_ty), cx.fresh(n), cx.fresh(n));
        let steps = vec![
            (pair, Expr::CallDirect(body, vec![local(value), self.nil()])),
            (image, Expr::Payload(pair, PAIR, 0)),
        ];
        let out = lets(steps, local(image));
        self.define(id, cx, vec![(value, model_ty)], n, out);
        id
    }

    /// `(value, table) -> Pair(node, table)`: the body, or a reference to the
    /// object's first appearance when something else holds it too.
    fn snap_fn(&mut self, ty: &Ty) -> FuncId {
        let ty = &canonical(ty);
        if let Some(&id) = self.snaps.get(ty) {
            return id;
        }
        let n = self.node_ty;
        let mty = self.m.lower_ty(ty);
        let id = self.reserve();
        self.snaps.insert(ty.clone(), id);
        let body = self.snap_body(ty);
        let mut cx = FnCx::new(Subst::new());
        let (value, table) = (cx.fresh(mty), cx.fresh(n));
        let address = cx.fresh(MTy::Int);
        let (seen, fresh_id, entry) = (cx.fresh(MTy::Int), cx.fresh(MTy::Int), cx.fresh(n));
        let (table2, pair, node, table3) = (cx.fresh(n), cx.fresh(n), cx.fresh(n), cx.fresh(n));
        let write = lets(
            vec![
                (fresh_id, Expr::CallDirect(self.next_id, vec![local(table)])),
                (
                    entry,
                    self.node(ENTRY, vec![local(address), local(fresh_id), int(0)]),
                ),
                (table2, self.cons(local(entry), local(table))),
                (
                    pair,
                    Expr::CallDirect(body, vec![local(value), local(table2)]),
                ),
                (node, Expr::Payload(pair, PAIR, 0)),
                (table3, Expr::Payload(pair, PAIR, 1)),
            ],
            self.node(
                PAIR,
                vec![
                    self.node(DEF, vec![local(fresh_id), local(node)]),
                    local(table3),
                ],
            ),
        );
        // The last holder of a shared object sees a count of one, so every
        // heap object is looked up, not only the ones with a count above one.
        let out = lets(
            vec![
                (address, Expr::Addr(value)),
                (
                    seen,
                    Expr::CallDirect(self.lookup, vec![local(table), local(address), int(0)]),
                ),
            ],
            Self::if_(
                Expr::Cmp(CmpOp::Ge, boxed(local(seen)), boxed(int(0))),
                self.node(PAIR, vec![self.node(REF, vec![local(seen)]), local(table)]),
                Self::if_(
                    Expr::Shared(value),
                    write,
                    Expr::CallDirect(body, vec![local(value), local(table)]),
                ),
            ),
        );
        self.define(id, cx, vec![(value, mty), (table, n)], n, out);
        id
    }

    /// `(value, table) -> Pair(node, table)` for an object written in place.
    fn snap_body(&mut self, ty: &Ty) -> FuncId {
        let ty = &canonical(ty);
        if let Some(&id) = self.snap_bodies.get(ty) {
            return id;
        }
        let n = self.node_ty;
        let mty = self.m.lower_ty(ty);
        let id = self.reserve();
        self.snap_bodies.insert(ty.clone(), id);
        let mut cx = FnCx::new(Subst::new());
        let (value, table) = (cx.fresh(mty), cx.fresh(n));
        let body = match kind(ty) {
            Kind::Record(fields) => self.snap_record(&mut cx, &fields, value, table),
            Kind::Variant(tags) => self.snap_variant(&mut cx, &tags, value, table),
            Kind::List(item) => self.snap_list(&mut cx, ty, &item, value, table),
            _ => unreachable!("only heap values have a snapshot body"),
        };
        self.define(id, cx, vec![(value, mty), (table, n)], n, body);
        id
    }

    /// Snapshot `value` of type `ty` into `steps`, returning the node's local
    /// and threading `table` through.
    fn snap_value(
        &mut self,
        cx: &mut FnCx,
        steps: &mut Vec<(Local, Expr)>,
        ty: &Ty,
        value: Local,
        table: &mut Local,
    ) -> Local {
        let node = cx.fresh(self.node_ty);
        let built = match kind(ty) {
            Kind::Int => self.node(INT, vec![local(value)]),
            Kind::Float => self.node(FLOAT, vec![local(value)]),
            Kind::Bool => self.node(BOOL, vec![local(value)]),
            Kind::Unit => self.node(UNIT, Vec::new()),
            Kind::Str => self.node(STR, vec![Expr::KeepStr(value)]),
            Kind::Func => {
                let key = cx.fresh(MTy::Ptr(HeapKind::Str));
                steps.push((key, Expr::MethodKey(value)));
                self.node(METHOD, vec![Expr::KeepStr(key)])
            }
            Kind::Record(_) | Kind::Variant(_) | Kind::List(_) => {
                let f = self.snap_fn(ty);
                let (pair, next) = (cx.fresh(self.node_ty), cx.fresh(self.node_ty));
                steps.push((pair, Expr::CallDirect(f, vec![local(value), local(*table)])));
                steps.push((next, Expr::Payload(pair, PAIR, 1)));
                *table = next;
                Expr::Payload(pair, PAIR, 0)
            }
        };
        steps.push((node, built));
        node
    }

    fn snap_record(
        &mut self,
        cx: &mut FnCx,
        fields: &[(String, Ty)],
        value: Local,
        table: Local,
    ) -> Expr {
        let mut steps = Vec::new();
        let loaded: Vec<Local> = fields
            .iter()
            .enumerate()
            .map(|(slot, (_, ty))| {
                let mty = self.m.lower_ty(ty);
                let held = cx.fresh(mty);
                steps.push((held, Expr::Field(value, slot)));
                held
            })
            .collect();
        let mut table = table;
        let mut chain = Vec::new();
        for ((label, ty), held) in fields.iter().zip(loaded) {
            let node = self.snap_value(cx, &mut steps, ty, held, &mut table);
            chain.push((label.clone(), node));
        }
        let fields = self.field_chain(chain);
        let record = self.node(REC, vec![fields]);
        lets(steps, self.node(PAIR, vec![record, local(table)]))
    }

    /// The fields' nodes as a chain of `Field` nodes.
    fn field_chain(&mut self, fields: Vec<(String, Local)>) -> Expr {
        fields
            .into_iter()
            .rev()
            .fold(self.nil(), |rest, (label, node)| {
                let name = self.lit(&label);
                let field = self.node(FIELD, vec![name, local(node)]);
                self.cons(field, rest)
            })
    }

    fn snap_variant(
        &mut self,
        cx: &mut FnCx,
        tags: &[(String, Ty)],
        value: Local,
        table: Local,
    ) -> Expr {
        let mut arms = Vec::new();
        for (label, payload) in tags {
            let tag = self.m.tags[label];
            let mut steps = Vec::new();
            let slots = payload_fields(payload);
            let loaded: Vec<Local> = slots
                .iter()
                .enumerate()
                .map(|(slot, ty)| {
                    let held = cx.fresh(self.m.lower_ty(ty));
                    steps.push((held, Expr::Payload(value, tag, slot)));
                    held
                })
                .collect();
            let mut table = table;
            let mut nodes = Vec::new();
            for (ty, held) in slots.iter().zip(loaded) {
                nodes.push(self.snap_value(cx, &mut steps, ty, held, &mut table));
            }
            let chain = nodes
                .into_iter()
                .rev()
                .fold(self.nil(), |rest, node| self.cons(local(node), rest));
            let name = self.lit(label);
            let variant = self.node(VAR, vec![name, chain]);
            arms.push((
                tag,
                lets(steps, self.node(PAIR, vec![variant, local(table)])),
            ));
        }
        let (_, default) = arms.pop().expect("a variant type has a tag");
        Expr::Switch(value, arms, boxed(default))
    }

    fn snap_list(
        &mut self,
        cx: &mut FnCx,
        list_ty: &Ty,
        item: &Ty,
        value: Local,
        table: Local,
    ) -> Expr {
        let n = self.node_ty;
        let list = self.m.lower_ty(list_ty);
        let link = self.m.tags["Link"];
        let walk = self.reserve();
        let mut wcx = FnCx::new(Subst::new());
        let (l, acc, wtable) = (wcx.fresh(list), wcx.fresh(n), wcx.fresh(n));
        let item_mty = self.m.lower_ty(item);
        let (head, rest) = (wcx.fresh(item_mty), wcx.fresh(list));
        let mut steps = vec![
            (head, Expr::Payload(l, link, 0)),
            (rest, Expr::Payload(l, link, 1)),
        ];
        let mut next_table = wtable;
        let node = self.snap_value(&mut wcx, &mut steps, item, head, &mut next_table);
        let step = lets(
            steps,
            Expr::TailCall(
                Callee::Direct(walk),
                vec![
                    local(rest),
                    self.cons(local(node), local(acc)),
                    local(next_table),
                ],
            ),
        );
        let done = self.node(PAIR, vec![local(acc), local(wtable)]);
        let walked = Self::switch(l, vec![(link, step)], done);
        self.define(walk, wcx, vec![(l, list), (acc, n), (wtable, n)], n, walked);

        let (pair, acc, table_out, chain) = (cx.fresh(n), cx.fresh(n), cx.fresh(n), cx.fresh(n));
        let steps = vec![
            (
                pair,
                Expr::CallDirect(walk, vec![local(value), self.nil(), local(table)]),
            ),
            (acc, Expr::Payload(pair, PAIR, 0)),
            (table_out, Expr::Payload(pair, PAIR, 1)),
            (
                chain,
                Expr::CallDirect(self.reverse_nodes, vec![local(acc), self.nil()]),
            ),
        ];
        let image = self.node(LIST, vec![local(chain)]);
        lets(steps, self.node(PAIR, vec![image, local(table_out)]))
    }

    // ---- refresh ----

    /// `(image, fresh, sites) -> outcome`, and the outcome's layout.
    fn refresh(&mut self, model: &Ty) -> (FuncId, LayoutId) {
        let n = self.node_ty;
        let model_mty = self.m.lower_ty(model);
        let inner = self.rf_fn(model, true);
        let outcome = self.result(model_mty);
        let id = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let (image, fresh, sites) = (cx.fresh(n), cx.fresh(model_mty), cx.fresh(self.sites_ty));
        let body = Expr::CallDirect(
            inner,
            vec![local(image), local(fresh), self.nil(), local(sites)],
        );
        let params = vec![(image, n), (fresh, model_mty), (sites, self.sites_ty)];
        self.define(id, cx, params, MTy::Ptr(HeapKind::Variant(outcome)), body);
        (id, outcome)
    }

    fn result_ty(&mut self, ty: MTy) -> MTy {
        MTy::Ptr(HeapKind::Variant(self.result(ty)))
    }

    /// `(image, [fresh], table, sites) -> result`: unwraps `Def` and `Ref`, and
    /// leaves the rest to the body.
    fn rf_fn(&mut self, ty: &Ty, fresh_ok: bool) -> FuncId {
        let ty = &canonical(ty);
        let with_fresh = fresh_ok && matches!(kind(ty), Kind::Record(_));
        if let Some(&id) = self.refreshes.get(&(ty.clone(), with_fresh)) {
            return id;
        }
        let n = self.node_ty;
        let mty = self.m.lower_ty(ty);
        let id = self.reserve();
        self.refreshes.insert((ty.clone(), with_fresh), id);
        let body = self.rf_body(ty, with_fresh);
        let ret = self.result_ty(mty);
        let type_id = self.type_id(ty);
        let mut cx = FnCx::new(Subst::new());
        let image = cx.fresh(n);
        let fresh = with_fresh.then(|| cx.fresh(mty));
        let (table, sites) = (cx.fresh(n), cx.fresh(self.sites_ty));
        let mut params = vec![(image, n)];
        params.extend(fresh.map(|f| (f, mty)));
        params.extend([(table, n), (sites, self.sites_ty)]);
        let call = |image: Local, table: Local| {
            let mut args = vec![local(image)];
            args.extend(fresh.map(local));
            args.extend([local(table), local(sites)]);
            Expr::CallDirect(body, args)
        };

        let (ident, address) = (cx.fresh(MTy::Int), cx.fresh(MTy::Int));
        let reshaped = self.reshaped(&mut cx, mty);
        let found = {
            let value = Expr::Retain(address, mty);
            let ok = self.ok(mty, value, local(table));
            lets(
                vec![
                    (ident, Expr::Payload(image, REF, 0)),
                    (
                        address,
                        Expr::CallDirect(
                            self.lookup,
                            vec![local(table), local(ident), int(type_id)],
                        ),
                    ),
                ],
                Self::if_(
                    Expr::Cmp(CmpOp::Ge, boxed(local(address)), boxed(int(0))),
                    ok,
                    reshaped,
                ),
            )
        };
        let (def_id, inner, result, value, table2, at, entry) = (
            cx.fresh(MTy::Int),
            cx.fresh(n),
            cx.fresh(ret),
            cx.fresh(mty),
            cx.fresh(n),
            cx.fresh(MTy::Int),
            cx.fresh(n),
        );
        let entered = {
            let entry_node = self.node(ENTRY, vec![local(def_id), local(at), int(type_id)]);
            let table_out = self.cons(local(entry), local(table2));
            let ok = self.ok(mty, local(value), table_out);
            let failed = self.forward(mty, result);
            let rebuilt = lets(
                vec![
                    (value, Expr::Payload(result, REFRESHED, 0)),
                    (table2, Expr::Payload(result, REFRESHED, 1)),
                    (at, Expr::Addr(value)),
                    (entry, entry_node),
                ],
                ok,
            );
            lets(
                vec![
                    (def_id, Expr::Payload(image, DEF, 0)),
                    (inner, Expr::Payload(image, DEF, 1)),
                    (result, call(inner, table)),
                ],
                Self::switch(result, vec![(REFRESHED, rebuilt)], failed),
            )
        };
        let out = Self::switch(
            image,
            vec![(REF, found), (DEF, entered)],
            call(image, table),
        );
        self.define(id, cx, params, ret, out);
        id
    }

    /// `Fail` with the reason `reshaped`.
    fn reshaped(&mut self, cx: &mut FnCx, ty: MTy) -> Expr {
        let reason = self.reason(cx, &[Part::Text("reshaped")]);
        self.fail(ty, reason)
    }

    fn rf_body(&mut self, ty: &Ty, with_fresh: bool) -> FuncId {
        let ty = &canonical(ty);
        if let Some(&id) = self.rf_bodies.get(&(ty.clone(), with_fresh)) {
            return id;
        }
        let n = self.node_ty;
        let mty = self.m.lower_ty(ty);
        let id = self.reserve();
        self.rf_bodies.insert((ty.clone(), with_fresh), id);
        let ret = self.result_ty(mty);
        let mut cx = FnCx::new(Subst::new());
        let image = cx.fresh(n);
        let fresh = with_fresh.then(|| cx.fresh(mty));
        let (table, sites) = (cx.fresh(n), cx.fresh(self.sites_ty));
        let mut params = vec![(image, n)];
        params.extend(fresh.map(|f| (f, mty)));
        params.extend([(table, n), (sites, self.sites_ty)]);
        let frame = Frame {
            image,
            fresh,
            table,
            sites,
        };
        let body = match kind(ty) {
            Kind::Record(fields) => self.rf_record(&mut cx, ty, &fields, &frame),
            Kind::Variant(tags) => self.rf_variant(&mut cx, ty, &tags, &frame),
            Kind::List(item) => self.rf_list(&mut cx, ty, &item, &frame),
            _ => unreachable!("only heap values have a refresh body"),
        };
        self.define(id, cx, params, ret, body);
        id
    }

    fn rf_record(
        &mut self,
        cx: &mut FnCx,
        ty: &Ty,
        fields: &[(String, Ty)],
        frame: &Frame,
    ) -> Expr {
        let n = self.node_ty;
        let mty = self.m.lower_ty(ty);
        let MTy::Ptr(HeapKind::Record(layout)) = mty else {
            unreachable!("a record lowers to a record layout");
        };
        let chain = cx.fresh(n);
        let lost = self.lost_methods(fields);
        let verdict = cx.fresh(n);
        let record = RecordCx {
            mty,
            layout,
            fields,
            chain,
            frame,
        };
        let continued = self.rf_fields(cx, &record, 0, Vec::new(), frame.table);
        let failed_methods = self.fail(mty, local(verdict));
        let checked = lets(
            vec![(verdict, Expr::CallDirect(lost, vec![local(chain)]))],
            Self::switch(verdict, vec![(NIL, continued)], failed_methods),
        );
        let reshaped = self.reshaped(cx, mty);
        Self::switch(
            frame.image,
            vec![(
                REC,
                lets(vec![(chain, Expr::Payload(frame.image, REC, 0))], checked),
            )],
            reshaped,
        )
    }

    /// `(fields) -> reason or Nil`: names the first method the image has that
    /// the record's type does not.
    fn lost_methods(&mut self, fields: &[(String, Ty)]) -> FuncId {
        let (n, string) = (self.node_ty, MTy::Ptr(HeapKind::Str));
        let id = self.reserve();
        let mut cx = FnCx::new(Subst::new());
        let chain = cx.fresh(n);
        let (field, rest, name, value) = (cx.fresh(n), cx.fresh(n), cx.fresh(string), cx.fresh(n));
        let again = || Expr::TailCall(Callee::Direct(id), vec![local(rest)]);
        let mut known = Expr::Const(Const::Bool(false));
        for (label, _) in fields {
            let text = cx.fresh(string);
            let lit = self.lit(label);
            known = Expr::Let(
                text,
                boxed(lit),
                boxed(Self::if_(
                    Expr::StrEq(name, text),
                    Expr::Const(Const::Bool(true)),
                    known,
                )),
            );
        }
        let gone = self.reason(&mut cx, &[Part::Text("method_lost"), Part::Image(name)]);
        let judged = Self::switch(
            value,
            vec![(METHOD, Self::if_(known, again(), gone))],
            again(),
        );
        let step = lets(
            vec![
                (field, Expr::Payload(chain, CONS, 0)),
                (rest, Expr::Payload(chain, CONS, 1)),
                (name, Expr::Payload(field, FIELD, 0)),
                (value, Expr::Payload(field, FIELD, 1)),
            ],
            judged,
        );
        let body = Self::switch(chain, vec![(CONS, step)], self.nil());
        self.define(id, cx, vec![(chain, n)], n, body);
        id
    }

    /// The record built from field `i` on, `values` holding the earlier ones.
    fn rf_fields(
        &mut self,
        cx: &mut FnCx,
        record: &RecordCx,
        i: usize,
        mut values: Vec<Expr>,
        table: Local,
    ) -> Expr {
        let mty = record.mty;
        if i == record.fields.len() {
            let built = Expr::AllocRecord(record.layout, values);
            return self.ok(mty, built, local(table));
        }
        let (label, ty) = &record.fields[i];
        if matches!(kind(ty), Kind::Unit) {
            values.push(Expr::Const(Const::Unit));
            return self.rf_fields(cx, record, i + 1, values, table);
        }
        let n = self.node_ty;
        let field_mty = self.m.lower_ty(ty);
        let field_result = self.result_ty(field_mty);
        let (node, result) = (cx.fresh(n), cx.fresh(field_result));
        let fresh_field = record.frame.fresh.map(|f| Expr::Field(f, i));
        let looked = self.value_res(
            cx,
            &Value {
                node,
                ty,
                label: Some(label),
                fresh: fresh_field,
                table,
                sites: record.frame.sites,
            },
        );
        let (value, table2) = (cx.fresh(field_mty), cx.fresh(n));
        values.push(local(value));
        let rest = self.rf_fields(cx, record, i + 1, values, table2);
        let name = self.lit(label);
        let failed = self.forward(mty, result);
        lets(
            vec![
                (
                    node,
                    Expr::CallDirect(self.find_field, vec![local(record.chain), name]),
                ),
                (result, looked),
            ],
            Self::switch(
                result,
                vec![(
                    REFRESHED,
                    lets(
                        vec![
                            (value, Expr::Payload(result, REFRESHED, 0)),
                            (table2, Expr::Payload(result, REFRESHED, 1)),
                        ],
                        rest,
                    ),
                )],
                failed,
            ),
        )
    }

    /// The result of refreshing the image `node` into a value of type `ty`:
    /// `Ok(value, table)` or `Fail(reason)`.
    fn value_res(&mut self, cx: &mut FnCx, v: &Value) -> Expr {
        let ty_mty = self.m.lower_ty(v.ty);
        let (node, table) = (v.node, v.table);
        let accepted: &[u32] = match kind(v.ty) {
            Kind::Int => &[INT],
            Kind::Float => &[FLOAT],
            Kind::Bool => &[BOOL],
            Kind::Str => &[STR],
            Kind::Func => &[METHOD],
            Kind::Record(_) => &[REC, DEF, REF],
            Kind::Variant(_) => &[VAR, DEF, REF],
            Kind::List(_) => &[LIST, DEF, REF],
            Kind::Unit => unreachable!("a Unit slot takes nothing from the image"),
        };
        let mut arms = Vec::new();
        for tag in (0..TAGS).filter(|t| !accepted.contains(t)) {
            let arm = match (tag, v.label) {
                (NIL, _) => self.missing(cx, v, ty_mty),
                (METHOD, Some(label)) => {
                    let reason = self.reason(cx, &[Part::Text("method_lost"), Part::Text(label)]);
                    self.fail(ty_mty, reason)
                }
                _ => self.mismatch(cx, v, ty_mty),
            };
            arms.push((tag, arm));
        }
        let accept = match kind(v.ty) {
            Kind::Int => self.payload_ok(ty_mty, node, INT, table),
            Kind::Float => self.payload_ok(ty_mty, node, FLOAT, table),
            Kind::Bool => self.payload_ok(ty_mty, node, BOOL, table),
            Kind::Str => self.payload_ok(ty_mty, node, STR, table),
            Kind::Func => self.rebind(cx, v, ty_mty),
            Kind::Record(_) | Kind::Variant(_) | Kind::List(_) => {
                let fresh = v
                    .fresh
                    .clone()
                    .filter(|_| matches!(kind(v.ty), Kind::Record(_)));
                let child = self.rf_fn(v.ty, fresh.is_some());
                let mut args = vec![local(node)];
                args.extend(fresh);
                args.extend([local(table), local(v.sites)]);
                Expr::CallDirect(child, args)
            }
            Kind::Unit => unreachable!("handled above"),
        };
        Self::switch(node, arms, accept)
    }

    fn payload_ok(&mut self, ty: MTy, node: Local, tag: u32, table: Local) -> Expr {
        self.ok(ty, Expr::Payload(node, tag, 0), local(table))
    }

    /// What a field the image lacks becomes: `fresh`'s value if the record has
    /// a fresh counterpart, else a reason to reset.
    fn missing(&mut self, cx: &mut FnCx, v: &Value, ty: MTy) -> Expr {
        match (v.label, &v.fresh) {
            (Some(label), _) if matches!(kind(v.ty), Kind::Func) => {
                let reason = self.reason(cx, &[Part::Text("method_added"), Part::Text(label)]);
                self.fail(ty, reason)
            }
            (Some(_), Some(fresh)) => self.ok(ty, fresh.clone(), local(v.table)),
            (Some(label), None) => {
                let reason = self.reason(cx, &[Part::Text("field_added"), Part::Text(label)]);
                self.fail(ty, reason)
            }
            (None, _) => self.reshaped(cx, ty),
        }
    }

    fn mismatch(&mut self, cx: &mut FnCx, v: &Value, ty: MTy) -> Expr {
        let Some(label) = v.label else {
            return self.reshaped(cx, ty);
        };
        let old = cx.fresh(MTy::Ptr(HeapKind::Str));
        let reason = self.reason(
            cx,
            &[
                Part::Text("type_changed"),
                Part::Text(label),
                Part::Local(old),
                Part::Text(type_name(v.ty)),
            ],
        );
        let failed = self.fail(ty, reason);
        Expr::Let(
            old,
            boxed(Expr::CallDirect(self.kind_name, vec![local(v.node)])),
            boxed(failed),
        )
    }

    /// A method the image holds, rebound to the new program's closure for its
    /// site, if the key is unique and the closure captures only top-level names.
    fn rebind(&mut self, cx: &mut FnCx, v: &Value, ty: MTy) -> Expr {
        let label = v.label.expect("a method is a record field");
        let string = MTy::Ptr(HeapKind::Str);
        let binding = cx.fresh(string);
        let names = self.names;
        let mut bindings: Vec<&str> = Vec::new();
        for site in &names.sites {
            if site.label == label && !bindings.contains(&site.binding.as_str()) {
                bindings.push(&site.binding);
            }
        }
        let mut out = {
            let known = Expr::CallDirect(self.known_binding, vec![local(binding)]);
            let lost = self.reason(cx, &[Part::Text("method_lost"), Part::Text(label)]);
            let lost = self.fail(ty, lost);
            let gone = self.reason(cx, &[Part::Text("binding_gone"), Part::Image(binding)]);
            let gone = self.fail(ty, gone);
            Self::if_(known, lost, gone)
        };
        for name in bindings.into_iter().rev() {
            let sites: Vec<&Site> = names
                .sites
                .iter()
                .filter(|s| s.binding == name && s.label == label)
                .collect();
            let action = match sites.as_slice() {
                [only] => match &only.captured {
                    Some(captured) => {
                        let reason = self.reason(
                            cx,
                            &[
                                Part::Text("method_captures"),
                                Part::Text(label),
                                Part::Text(captured),
                            ],
                        );
                        Some(self.fail(ty, reason))
                    }
                    None => self.fits(only, v.ty).then(|| {
                        let slot = self.site_slot(only.expr, v.ty);
                        let closure = Expr::Field(v.sites, slot);
                        self.ok(ty, closure, local(v.table))
                    }),
                },
                _ => {
                    let reason =
                        self.reason(cx, &[Part::Text("ambiguous_site"), Part::Text(label)]);
                    Some(self.fail(ty, reason))
                }
            };
            if let Some(action) = action {
                let text = cx.fresh(string);
                let lit = self.lit(name);
                out = Expr::Let(
                    text,
                    boxed(lit),
                    boxed(Self::if_(Expr::StrEq(binding, text), action, out)),
                );
            }
        }
        Expr::Let(binding, boxed(Expr::Payload(v.node, METHOD, 0)), boxed(out))
    }

    /// Whether `site`'s literal, specialized, has the type `ty`.
    fn fits(&mut self, site: &Site, ty: &Ty) -> bool {
        let lambda_ty = self.m.lambdas[&Target::Anon(site.expr)].ty;
        let ty = canonical(ty);
        if !agrees(lambda_ty, &ty, &mut HashMap::new(), &mut HashSet::new()) {
            return false;
        }
        let mut subst = Subst::new();
        match_ty(lambda_ty, &ty, &mut subst);
        self.m.ground(lambda_ty, &subst) == ty
    }

    fn site_slot(&mut self, site: ExprId, ty: &Ty) -> usize {
        let key = (site, canonical(ty));
        if let Some(at) = self.site_slots.iter().position(|s| *s == key) {
            return at;
        }
        self.site_slots.push(key);
        self.site_slots.len() - 1
    }

    fn rf_variant(&mut self, cx: &mut FnCx, ty: &Ty, tags: &[(String, Ty)], frame: &Frame) -> Expr {
        let n = self.node_ty;
        let string = MTy::Ptr(HeapKind::Str);
        let mty = self.m.lower_ty(ty);
        let MTy::Ptr(HeapKind::Variant(layout)) = mty else {
            unreachable!("a variant lowers to a variant layout");
        };
        let (name, payload) = (cx.fresh(string), cx.fresh(n));
        let mut out = self.reshaped(cx, mty);
        for (label, payload_ty) in tags.iter().rev() {
            let tag = self.m.tags[label];
            let slots = payload_fields(payload_ty);
            let target = Payload {
                mty,
                layout,
                tag,
                slots: &slots,
                frame,
            };
            let arm = self.rf_payload(cx, &target, payload, 0, Vec::new(), frame.table);
            let text = cx.fresh(string);
            let lit = self.lit(label);
            out = Expr::Let(
                text,
                boxed(lit),
                boxed(Self::if_(Expr::StrEq(name, text), arm, out)),
            );
        }
        let reshaped = self.reshaped(cx, mty);
        Self::switch(
            frame.image,
            vec![(
                VAR,
                lets(
                    vec![
                        (name, Expr::Payload(frame.image, VAR, 0)),
                        (payload, Expr::Payload(frame.image, VAR, 1)),
                    ],
                    out,
                ),
            )],
            reshaped,
        )
    }

    /// The variant built from payload slot `i` on of the image chain.
    fn rf_payload(
        &mut self,
        cx: &mut FnCx,
        target: &Payload,
        chain: Local,
        i: usize,
        mut values: Vec<Expr>,
        table: Local,
    ) -> Expr {
        let mty = target.mty;
        if i == target.slots.len() {
            let built = Expr::AllocVariant(target.layout, target.tag, values);
            return self.ok(mty, built, local(table));
        }
        let n = self.node_ty;
        let ty = &target.slots[i];
        let (head, rest) = (cx.fresh(n), cx.fresh(n));
        let reshaped = self.reshaped(cx, mty);
        let loads = vec![
            (head, Expr::Payload(chain, CONS, 0)),
            (rest, Expr::Payload(chain, CONS, 1)),
        ];
        let inner = if matches!(kind(ty), Kind::Unit) {
            values.push(Expr::Const(Const::Unit));
            self.rf_payload(cx, target, rest, i + 1, values, table)
        } else {
            let slot_mty = self.m.lower_ty(ty);
            let slot_result = self.result_ty(slot_mty);
            let result = cx.fresh(slot_result);
            let looked = self.value_res(
                cx,
                &Value {
                    node: head,
                    ty,
                    label: None,
                    fresh: None,
                    table,
                    sites: target.frame.sites,
                },
            );
            let (value, table2) = (cx.fresh(slot_mty), cx.fresh(n));
            values.push(local(value));
            let next = self.rf_payload(cx, target, rest, i + 1, values, table2);
            let failed = self.forward(mty, result);
            lets(
                vec![(result, looked)],
                Self::switch(
                    result,
                    vec![(
                        REFRESHED,
                        lets(
                            vec![
                                (value, Expr::Payload(result, REFRESHED, 0)),
                                (table2, Expr::Payload(result, REFRESHED, 1)),
                            ],
                            next,
                        ),
                    )],
                    failed,
                ),
            )
        };
        Self::switch(chain, vec![(CONS, lets(loads, inner))], reshaped)
    }

    fn rf_list(&mut self, cx: &mut FnCx, list_ty: &Ty, item: &Ty, frame: &Frame) -> Expr {
        let n = self.node_ty;
        let list = self.m.lower_ty(list_ty);
        let MTy::Ptr(HeapKind::Variant(layout)) = list else {
            unreachable!("a list lowers to a variant layout");
        };
        let (link, empty) = (self.m.tags["Link"], self.m.tags["Empty"]);
        let reverse = self.reverse_list(list_ty, layout, link);
        let item_mty = self.m.lower_ty(item);
        let ret = self.result_ty(list);
        let walk = self.reserve();
        let mut wcx = FnCx::new(Subst::new());
        let (chain, racc, table) = (wcx.fresh(n), wcx.fresh(list), wcx.fresh(n));
        let sites = wcx.fresh(self.sites_ty);
        let (head, rest) = (wcx.fresh(n), wcx.fresh(n));
        let consed =
            |value: Expr, racc: Local| Expr::AllocVariant(layout, link, vec![value, local(racc)]);
        let step = if matches!(kind(item), Kind::Unit) {
            Expr::TailCall(
                Callee::Direct(walk),
                vec![
                    local(rest),
                    consed(Expr::Const(Const::Unit), racc),
                    local(table),
                    local(sites),
                ],
            )
        } else {
            let item_result = self.result_ty(item_mty);
            let result = wcx.fresh(item_result);
            let looked = self.value_res(
                &mut wcx,
                &Value {
                    node: head,
                    ty: item,
                    label: None,
                    fresh: None,
                    table,
                    sites,
                },
            );
            let (value, table2) = (wcx.fresh(item_mty), wcx.fresh(n));
            let failed = self.forward(list, result);
            lets(
                vec![(result, looked)],
                Self::switch(
                    result,
                    vec![(
                        REFRESHED,
                        lets(
                            vec![
                                (value, Expr::Payload(result, REFRESHED, 0)),
                                (table2, Expr::Payload(result, REFRESHED, 1)),
                            ],
                            Expr::TailCall(
                                Callee::Direct(walk),
                                vec![
                                    local(rest),
                                    consed(local(value), racc),
                                    local(table2),
                                    local(sites),
                                ],
                            ),
                        ),
                    )],
                    failed,
                ),
            )
        };
        let finished = {
            let done = Expr::CallDirect(
                reverse,
                vec![local(racc), Expr::AllocVariant(layout, empty, Vec::new())],
            );
            self.ok(list, done, local(table))
        };
        let walked = Self::switch(
            chain,
            vec![(
                CONS,
                lets(
                    vec![
                        (head, Expr::Payload(chain, CONS, 0)),
                        (rest, Expr::Payload(chain, CONS, 1)),
                    ],
                    step,
                ),
            )],
            finished,
        );
        self.define(
            walk,
            wcx,
            vec![(chain, n), (racc, list), (table, n), (sites, self.sites_ty)],
            ret,
            walked,
        );

        let start = cx.fresh(n);
        let begin = Expr::CallDirect(
            walk,
            vec![
                local(start),
                Expr::AllocVariant(layout, empty, Vec::new()),
                local(frame.table),
                local(frame.sites),
            ],
        );
        let reshaped = self.reshaped(cx, list);
        Self::switch(
            frame.image,
            vec![(
                LIST,
                lets(vec![(start, Expr::Payload(frame.image, LIST, 0))], begin),
            )],
            reshaped,
        )
    }

    /// `(list, acc) -> list`: the cells of `list` pushed onto `acc` one by one.
    fn reverse_list(&mut self, ty: &Ty, layout: LayoutId, link: u32) -> FuncId {
        if let Some(&id) = self.reversals.get(ty) {
            return id;
        }
        let list = self.m.lower_ty(ty);
        let id = self.reserve();
        self.reversals.insert(ty.clone(), id);
        let Kind::List(item) = kind(ty) else {
            unreachable!("a list type");
        };
        let item_mty = self.m.lower_ty(&item);
        let mut cx = FnCx::new(Subst::new());
        let (l, acc, head, rest) = (
            cx.fresh(list),
            cx.fresh(list),
            cx.fresh(item_mty),
            cx.fresh(list),
        );
        let step = lets(
            vec![
                (head, Expr::Payload(l, link, 0)),
                (rest, Expr::Payload(l, link, 1)),
            ],
            Expr::TailCall(
                Callee::Direct(id),
                vec![
                    local(rest),
                    Expr::AllocVariant(layout, link, vec![local(head), local(acc)]),
                ],
            ),
        );
        let body = Self::switch(l, vec![(link, step)], local(acc));
        self.define(id, cx, vec![(l, list), (acc, list)], list, body);
        id
    }

    /// The closure `setup` builds for each rebinding target: the literal's
    /// specialization over the top-level values it captures.
    fn site_closures(&mut self, root: &mut FnCx) -> Vec<Expr> {
        let mut out = Vec::new();
        for (expr, ty) in self.site_slots.clone() {
            let span = self
                .names
                .sites
                .iter()
                .find(|s| s.expr == expr)
                .map_or(Span::new(0, 0), |s| s.span);
            let target = Target::Anon(expr);
            let (func, ty) = self.m.specialize_at(&root.subst, target, ty, span);
            let captures = self.m.lambdas[&target].captures.clone();
            out.push(if captures.is_empty() {
                self.m.closure_of(func, &ty)
            } else {
                let values = captures
                    .into_iter()
                    .map(|c: Symbol| self.m.variable_value(root, c))
                    .collect();
                Expr::MakeClosure(func, values)
            });
        }
        out
    }
}

/// Whether `match_ty` could instantiate `template` to `actual`: it checks
/// without the assertions `match_ty` makes, since a site's literal is tried
/// against every method field of its name, whatever type that field has.
fn agrees(
    template: &Ty,
    actual: &Ty,
    bound: &mut HashMap<TypeVar, Ty>,
    seen: &mut HashSet<(Ty, Ty)>,
) -> bool {
    match (template, actual) {
        (Ty::Var(v), t) => {
            let t = canonical(t);
            bound.get(v).is_none_or(|prev| *prev == t) && {
                bound.insert(*v, t);
                true
            }
        }
        (Ty::Rec(..), _) | (_, Ty::Rec(..)) => {
            !seen.insert((template.clone(), actual.clone()))
                || agrees(&template.unfold_head(), &actual.unfold_head(), bound, seen)
        }
        (Ty::Func(ta, tr), Ty::Func(aa, ar)) => {
            ta.len() == aa.len()
                && ta.iter().zip(aa).all(|(t, a)| agrees(t, a, bound, seen))
                && agrees(tr, ar, bound, seen)
        }
        (Ty::Record(t), Ty::Record(a)) | (Ty::Variant(t), Ty::Variant(a)) => {
            rows_agree(t, a, bound, seen)
        }
        (t, a) => t == a,
    }
}

fn rows_agree(
    template: &Row,
    actual: &Row,
    bound: &mut HashMap<TypeVar, Ty>,
    seen: &mut HashSet<(Ty, Ty)>,
) -> bool {
    let mut rest: Vec<_> = ground_fields(actual).collect();
    let mut row = template;
    loop {
        match row {
            Row::Extend {
                label,
                field,
                rest: next,
                ..
            } => {
                let Some(at) = rest.iter().position(|(l, _)| *l == label) else {
                    return false;
                };
                if !agrees(field, rest.remove(at).1, bound, seen) {
                    return false;
                }
                row = next;
            }
            Row::Maybe {
                label,
                field,
                rest: next,
                ..
            } => {
                if let Some(at) = rest.iter().position(|(l, _)| *l == label)
                    && !agrees(field, rest.remove(at).1, bound, seen)
                {
                    return false;
                }
                row = next;
            }
            Row::Var(_) => return true,
            Row::Empty => return rest.is_empty(),
        }
    }
}

/// The locals a refresh function starts with.
struct Frame {
    image: Local,
    fresh: Option<Local>,
    table: Local,
    sites: Local,
}

struct RecordCx<'r> {
    mty: MTy,
    layout: LayoutId,
    fields: &'r [(String, Ty)],
    chain: Local,
    frame: &'r Frame,
}

/// The variant tag a payload is being rebuilt into.
struct Payload<'r> {
    mty: MTy,
    layout: LayoutId,
    tag: u32,
    slots: &'r [Ty],
    frame: &'r Frame,
}

/// One value to refresh: the image `node`, the type it must become, the field
/// it is (for the reason a reset gives), and what stands in if it is missing.
struct Value<'v> {
    node: Local,
    ty: &'v Ty,
    label: Option<&'v str>,
    fresh: Option<Expr>,
    table: Local,
    sites: Local,
}

/// The method literals of `checked` and the top-level names around them.
pub(super) fn names(checked: &Checked, lambdas: &HashMap<Target, Lambda<'_>>) -> Names {
    let mut roots = HashSet::new();
    let mut bindings = Vec::new();
    let mut found: Vec<(String, String, ExprId, Span)> = Vec::new();
    let mut spelled: HashMap<Symbol, String> = HashMap::new();
    let mut cursor = Some(&checked.root);
    while let Some(ExprKind::Let {
        symbol,
        name,
        value,
        rest,
    }) = cursor.map(|e| &e.kind)
    {
        roots.insert(*symbol);
        if !bindings.contains(name) {
            bindings.push(name.clone());
        }
        for_each_node(value, &mut |e| match &e.kind {
            ExprKind::Record { fields } | ExprKind::Spread { fields, .. } => {
                for (label, field) in fields {
                    if is_method(field) {
                        found.push((name.clone(), label.clone(), field.id, field.span));
                    }
                }
            }
            ExprKind::Var { symbol, name } => {
                spelled.insert(*symbol, name.clone());
            }
            _ => {}
        });
        cursor = rest.as_deref();
    }
    let sites = found
        .iter()
        .map(|(binding, label, expr, span)| Site {
            binding: binding.clone(),
            label: label.clone(),
            expr: *expr,
            span: *span,
            captured: lambdas.get(&Target::Anon(*expr)).and_then(|lambda| {
                lambda
                    .captures
                    .iter()
                    .find(|c| !roots.contains(c))
                    .map(|c| spelled.get(c).cloned().unwrap_or_else(|| "a value".into()))
            }),
        })
        .collect();
    Names { sites, bindings }
}

fn is_method(e: &hir::Expr) -> bool {
    matches!(&e.kind, ExprKind::Func { params, .. } if params.first().is_some_and(|p| p.name == SELF_NAME))
}

/// `body`, a chain of `Let`s ending in the root record, with one more slot on
/// that record: `sites`, built where every top-level name is still in scope.
pub(super) fn extend_root(
    body: Expr,
    cx: &mut FnCx,
    old: MTy,
    sites_ty: MTy,
    layout: LayoutId,
    slots: usize,
    sites: Expr,
) -> Expr {
    let mut spine = Vec::new();
    let mut tail = body;
    while let Expr::Let(bound, value, rest) = tail {
        spine.push((bound, *value));
        tail = *rest;
    }
    let (record, held) = (cx.fresh(old), cx.fresh(sites_ty));
    let fields = (0..slots)
        .map(|slot| Expr::Field(record, slot))
        .chain([local(held)])
        .collect();
    let extended = lets(
        vec![(record, tail), (held, sites)],
        Expr::AllocRecord(layout, fields),
    );
    lets(spine, extended)
}
