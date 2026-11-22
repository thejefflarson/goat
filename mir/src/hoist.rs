//! Field loads moved up to where their record is bound, so the record dies
//! there. A record that is only read through `Field`, always on the straight
//! line below its binding, is loaded into one local per field read; the RC pass
//! then drops the record right after the loads rather than at the last read.
//! A record that nothing else holds is freed at that point, which leaves each
//! pointer field it held with one reference, and a callee given that field can
//! reuse its cell (`ReuseRecord`). Without the move, the record outlives the
//! call and every field read out of it is shared.
//!
//! Records are immutable and a load has no effect, so moving it earlier
//! changes no value and no order that `effects` sees. A record read inside a
//! branch is left alone: its loads would run on paths that never read them.
//! So is a record whose fields are all scalars, which has no reference to
//! hand over.

use std::collections::{BTreeMap, BTreeSet};

use crate::mir::*;
use crate::rc::max_local;

/// Hoist the field reads of every eligible record in `program`.
pub(crate) fn hoist_fields(program: &mut Program) {
    let layouts = &program.layouts;
    for func in &mut program.funcs {
        let plan = plan(func, layouts);
        if !plan.is_empty() {
            apply(func, &plan);
        }
    }
}

/// For each record to hoist, the fields it reads, each with the local that
/// will hold it and its type.
type Plan = BTreeMap<Local, Vec<(usize, Local, MTy)>>;

fn record_fields(layouts: &[Layout], ty: Option<MTy>) -> Option<&[MTy]> {
    match ty? {
        MTy::Ptr(HeapKind::Record(layout)) => match layouts.get(layout.0 as usize)? {
            Layout::Record(fields) => Some(fields),
            Layout::Variant(_) => None,
        },
        _ => None,
    }
}

fn plan(func: &Func, layouts: &[Layout]) -> Plan {
    let record = |x: Local| record_fields(layouts, func.local_ty(x));
    // The branch depth each record is bound at, and what is read from it there.
    let mut bound: BTreeMap<Local, usize> = BTreeMap::new();
    let mut reads: BTreeMap<Local, BTreeSet<usize>> = BTreeMap::new();
    let mut spoiled: BTreeSet<Local> = BTreeSet::new();
    for &(param, _) in &func.params {
        if record(param).is_some() {
            bound.insert(param, 0);
        }
    }

    let mut stack = vec![(&func.body, 0usize)];
    while let Some((e, depth)) = stack.pop() {
        match e {
            Expr::Let(x, ..) if record(*x).is_some() => {
                bound.insert(*x, depth);
            }
            Expr::Field(x, i) if bound.get(x) == Some(&depth) => {
                reads.entry(*x).or_default().insert(*i);
            }
            _ => mentioned(e, &mut |x| {
                spoiled.insert(x);
            }),
        }
        let in_arms = matches!(e, Expr::Switch(..) | Expr::Unpack(..));
        let mut index = 0;
        e.for_each_child(&mut |child| {
            let inside = in_arms || (matches!(e, Expr::If(..)) && index > 0);
            stack.push((child, depth + usize::from(inside)));
            index += 1;
        });
    }

    let mut next = max_local(func) + 1;
    let mut plan = Plan::new();
    for (x, fields) in reads {
        let types = record(x).expect("a bound record has a record type");
        if spoiled.contains(&x) || !fields.iter().any(|&i| types[i].is_ptr()) {
            continue;
        }
        let loads = fields
            .into_iter()
            .map(|i| {
                next += 1;
                (i, Local(next - 1), types[i])
            })
            .collect();
        plan.insert(x, loads);
    }
    plan
}

fn apply(func: &mut Func, plan: &Plan) {
    let held: BTreeMap<(Local, usize), Local> = plan
        .iter()
        .flat_map(|(&x, loads)| loads.iter().map(move |&(i, held, _)| ((x, i), held)))
        .collect();
    for loads in plan.values() {
        for &(_, held, ty) in loads {
            func.locals.insert(held, ty);
        }
    }
    func.body.for_each_node_mut(&mut |e| {
        if let Expr::Field(x, i) = e
            && let Some(&held) = held.get(&(*x, *i))
        {
            *e = Expr::Local(held);
        }
    });

    let load_first = |x: Local, loads: &[(usize, Local, MTy)], body: Expr| {
        loads.iter().rev().fold(body, |body, &(i, held, _)| {
            Expr::Let(held, Box::new(Expr::Field(x, i)), Box::new(body))
        })
    };
    func.body.for_each_node_mut(&mut |e| {
        if let Expr::Let(x, _, body) = e
            && let Some(loads) = plan.get(x)
        {
            let inner = std::mem::replace(&mut **body, Expr::Const(Const::Unit));
            **body = load_first(*x, loads, inner);
        }
    });
    for &(param, _) in &func.params {
        if let Some(loads) = plan.get(&param) {
            let inner = std::mem::replace(&mut func.body, Expr::Const(Const::Unit));
            func.body = load_first(param, loads, inner);
        }
    }
}

/// Calls `f` with each local the node itself names, not its subexpressions'.
fn mentioned(e: &Expr, f: &mut impl FnMut(Local)) {
    match e {
        Expr::Local(x)
        | Expr::Field(x, _)
        | Expr::Payload(x, ..)
        | Expr::Free(x)
        | Expr::StrLen(x)
        | Expr::StrChars(x)
        | Expr::Addr(x)
        | Expr::Shared(x)
        | Expr::Retain(x, _)
        | Expr::KeepStr(x)
        | Expr::MethodKey(x)
        | Expr::Write(Write::Str(x))
        | Expr::Dup(x)
        | Expr::Drop(x)
        | Expr::Switch(x, ..)
        | Expr::Unpack(x, ..)
        | Expr::ReuseVariant(x, ..)
        | Expr::ReuseRecord(x, ..) => f(*x),
        Expr::StrEq(a, b) | Expr::StrByte(a, b) | Expr::StrChar(a, b) => {
            f(*a);
            f(*b);
        }
        Expr::CallForeign(_, args) => args.iter().for_each(|x| f(*x)),
        Expr::Const(_)
        | Expr::Let(..)
        | Expr::BinInt(..)
        | Expr::BinFloat(..)
        | Expr::IntToFloat(_)
        | Expr::FloatFn(..)
        | Expr::Cmp(..)
        | Expr::If(..)
        | Expr::CallDirect(..)
        | Expr::CallClosure(..)
        | Expr::TailCall(..)
        | Expr::MakeClosure(..)
        | Expr::Capture(_)
        | Expr::AllocRecord(..)
        | Expr::AllocVariant(..)
        | Expr::StrLit(_)
        | Expr::Write(Write::Number(_) | Write::Lit(_) | Write::End)
        | Expr::Trap(_)
        | Expr::Site(..) => {}
    }
}
