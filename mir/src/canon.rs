//! Canonical forms of ground types, for use as mono keys.
//!
//! Mono keys specializations and variant layouts on types, but `Ty`'s derived
//! `Eq` and `Hash` are structural. Two recursive types that denote the same
//! infinite tree can differ in binder ids, in how often they are unrolled, or
//! in a redundant nested `μ`. [`canonical`] maps all of them to one
//! representative: the minimal automaton of the type's tree, written back as a
//! `μ`-term with binders numbered by nesting depth. Two ground types are
//! equal as recursive types exactly when their canonical forms are `==`.
//!
//! Termination: a closed type has finitely many distinct subtrees (each is a
//! subterm with enclosing binders replaced by the enclosing `μ`-terms), so the
//! graph is finite, and partition refinement and the cycle-cutting emit walk
//! it finitely.

use goat_checker::ty::{PLAIN, Row, Ty, TypeVar};
use std::collections::HashMap;

/// Canonical binders count up from here. A ground type has no free variables,
/// so these ids cannot collide with a variable.
const BINDER_BASE: TypeVar = 1 << 30;

/// The `(label, type)` pairs of a closed row, in order.
pub fn ground_fields(row: &Row) -> impl Iterator<Item = (&String, &Ty)> {
    let mut next = Some(row);
    std::iter::from_fn(move || match next? {
        Row::Extend {
            label, field, rest, ..
        } => {
            next = Some(rest);
            Some((label, &**field))
        }
        Row::Empty | Row::Var(_) | Row::Maybe { .. } => None,
    })
}

pub(crate) fn row_from(fields: Vec<(String, Ty)>) -> Row {
    fields
        .into_iter()
        .rev()
        .fold(Row::Empty, |rest, (label, field)| Row::Extend {
            label,
            field: Box::new(field),
            method: Box::new(PLAIN),
            rest: Box::new(rest),
        })
}

/// Whether `binder` is reachable in `ty` without crossing a variant.
fn loops_without_variant(binder: TypeVar, ty: &Ty) -> bool {
    match ty {
        Ty::Var(v) => *v == binder,
        Ty::Func(args, ret) => {
            args.iter().any(|a| loops_without_variant(binder, a))
                || loops_without_variant(binder, ret)
        }
        Ty::Record(row) => ground_fields(row).any(|(_, t)| loops_without_variant(binder, t)),
        Ty::Rec(_, body) => loops_without_variant(binder, body),
        _ => false,
    }
}

/// Whether `ty` holds a `μ` over a function or record, a cycle no variant cuts.
pub fn has_structural_rec(ty: &Ty) -> bool {
    match ty {
        Ty::Rec(binder, body) => loops_without_variant(*binder, body) || has_structural_rec(body),
        Ty::Func(args, ret) => args.iter().any(has_structural_rec) || has_structural_rec(ret),
        Ty::Record(row) | Ty::Variant(row) => {
            ground_fields(row).any(|(_, t)| has_structural_rec(t))
        }
        _ => false,
    }
}

fn has_rec(ty: &Ty) -> bool {
    match ty {
        Ty::Rec(..) => true,
        Ty::Func(args, ret) => args.iter().any(has_rec) || has_rec(ret),
        Ty::Record(row) | Ty::Variant(row) => ground_fields(row).any(|(_, t)| has_rec(t)),
        Ty::Var(_) | Ty::Int | Ty::Float | Ty::Str | Ty::Bool | Ty::Unit => false,
    }
}

/// `ty` with every `μ` binder renamed to `BINDER_BASE` plus its nesting depth,
/// so α-equivalent types become equal.
fn rename_binders(ty: &Ty, scope: &mut Vec<(TypeVar, TypeVar)>) -> Ty {
    match ty {
        Ty::Var(v) => scope
            .iter()
            .rev()
            .find(|(old, _)| old == v)
            .map_or_else(|| ty.clone(), |(_, new)| Ty::Var(*new)),
        Ty::Rec(binder, body) => {
            let renamed = BINDER_BASE + scope.len() as TypeVar;
            scope.push((*binder, renamed));
            let body = rename_binders(body, scope);
            scope.pop();
            Ty::Rec(renamed, Box::new(body))
        }
        Ty::Func(args, ret) => Ty::Func(
            args.iter().map(|a| rename_binders(a, scope)).collect(),
            Box::new(rename_binders(ret, scope)),
        ),
        Ty::Record(row) => Ty::Record(rename_row(row, scope)),
        Ty::Variant(row) => Ty::Variant(rename_row(row, scope)),
        Ty::Int | Ty::Float | Ty::Str | Ty::Bool | Ty::Unit => ty.clone(),
    }
}

fn rename_row(row: &Row, scope: &mut Vec<(TypeVar, TypeVar)>) -> Row {
    match row {
        Row::Extend {
            label, field, rest, ..
        } => Row::Extend {
            label: label.clone(),
            field: Box::new(rename_binders(field, scope)),
            method: Box::new(PLAIN),
            rest: Box::new(rename_row(rest, scope)),
        },
        other => other.clone(),
    }
}

/// What a node of the type's tree is, apart from its children.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Shape {
    Int,
    Float,
    Str,
    Bool,
    Unit,
    Func(usize),
    Record(Vec<String>),
    Variant(Vec<String>),
}

fn split(ty: &Ty) -> (Shape, Vec<Ty>) {
    let sorted = |row: &Row| {
        let mut fields: Vec<(String, Ty)> = ground_fields(row)
            .map(|(l, t)| (l.clone(), t.clone()))
            .collect();
        fields.sort_by(|a, b| a.0.cmp(&b.0));
        fields.into_iter().unzip::<_, _, Vec<_>, Vec<_>>()
    };
    match ty {
        Ty::Int => (Shape::Int, Vec::new()),
        Ty::Float => (Shape::Float, Vec::new()),
        Ty::Str => (Shape::Str, Vec::new()),
        Ty::Bool => (Shape::Bool, Vec::new()),
        Ty::Func(args, ret) => (
            Shape::Func(args.len()),
            args.iter()
                .chain(std::iter::once(&**ret))
                .cloned()
                .collect(),
        ),
        Ty::Record(row) => {
            let (labels, kids) = sorted(row);
            (Shape::Record(labels), kids)
        }
        Ty::Variant(row) => {
            let (labels, kids) = sorted(row);
            (Shape::Variant(labels), kids)
        }
        // A free variable or a vacuous `μ` carries no structure.
        Ty::Unit | Ty::Var(_) | Ty::Rec(..) => (Shape::Unit, Vec::new()),
    }
}

fn build(shape: &Shape, kids: Vec<Ty>) -> Ty {
    match shape {
        Shape::Int => Ty::Int,
        Shape::Float => Ty::Float,
        Shape::Str => Ty::Str,
        Shape::Bool => Ty::Bool,
        Shape::Unit => Ty::Unit,
        Shape::Func(n) => {
            let mut args = kids;
            let ret = args.split_off(*n);
            Ty::Func(args, Box::new(ret.into_iter().next().unwrap_or(Ty::Unit)))
        }
        Shape::Record(labels) => Ty::Record(row_from(labels.iter().cloned().zip(kids).collect())),
        Shape::Variant(labels) => Ty::Variant(row_from(labels.iter().cloned().zip(kids).collect())),
    }
}

/// The type's tree as a finite graph: one node per distinct subtree, with
/// children as node indices, so a recursive type is a graph with a cycle.
#[derive(Default)]
struct Graph {
    nodes: Vec<(Shape, Vec<usize>)>,
    index: HashMap<Ty, usize>,
}

impl Graph {
    fn node(&mut self, ty: &Ty) -> usize {
        // Unfolding exposes a constructor; renaming makes the node's identity
        // independent of how it was reached.
        let ty = rename_binders(&ty.unfold_head(), &mut Vec::new());
        if let Some(&i) = self.index.get(&ty) {
            return i;
        }
        let i = self.nodes.len();
        self.nodes.push((Shape::Unit, Vec::new()));
        self.index.insert(ty.clone(), i);
        let (shape, parts) = split(&ty);
        let kids = parts.iter().map(|p| self.node(p)).collect();
        self.nodes[i] = (shape, kids);
        i
    }

    /// Coarsest partition of the nodes in which two nodes share a class only if
    /// they have the same shape and their children share classes (Moore's
    /// algorithm). Nodes in one class denote the same tree.
    fn classes(&self) -> Vec<usize> {
        let mut shapes: HashMap<&Shape, usize> = HashMap::new();
        let mut class: Vec<usize> = self
            .nodes
            .iter()
            .map(|(shape, _)| {
                let next = shapes.len();
                *shapes.entry(shape).or_insert(next)
            })
            .collect();
        let mut count = shapes.len();
        loop {
            let mut sigs: HashMap<(usize, Vec<usize>), usize> = HashMap::new();
            let refined: Vec<usize> = self
                .nodes
                .iter()
                .enumerate()
                .map(|(i, (_, kids))| {
                    let sig = (class[i], kids.iter().map(|k| class[*k]).collect());
                    let next = sigs.len();
                    *sigs.entry(sig).or_insert(next)
                })
                .collect();
            if sigs.len() == count {
                return refined;
            }
            count = sigs.len();
            class = refined;
        }
    }

    /// Write class `class` back as a type. A class met again on the current
    /// path is a back edge, written as a variable bound by a `μ` around the
    /// class it names.
    fn emit(
        &self,
        class: usize,
        classes: &[usize],
        rep: &HashMap<usize, usize>,
        path: &mut Vec<(usize, bool)>,
    ) -> Ty {
        if let Some(depth) = path.iter().position(|(c, _)| *c == class) {
            path[depth].1 = true;
            return Ty::Var(BINDER_BASE + depth as TypeVar);
        }
        let (shape, kids) = &self.nodes[rep[&class]];
        path.push((class, false));
        let kids = kids
            .iter()
            .map(|k| self.emit(classes[*k], classes, rep, path))
            .collect();
        let ty = build(shape, kids);
        let (_, looped) = path.pop().expect("pushed above");
        if looped {
            Ty::Rec(BINDER_BASE + path.len() as TypeVar, Box::new(ty))
        } else {
            ty
        }
    }
}

/// The canonical representative of the ground type `ty`.
pub fn canonical(ty: &Ty) -> Ty {
    if !has_rec(ty) {
        return ty.clone();
    }
    let mut graph = Graph::default();
    let root = graph.node(ty);
    let classes = graph.classes();
    let mut rep = HashMap::new();
    for (node, class) in classes.iter().enumerate() {
        rep.entry(*class).or_insert(node);
    }
    let emitted = graph.emit(classes[root], &classes, &rep, &mut Vec::new());
    rename_binders(&emitted, &mut Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn variant(tags: Vec<(&str, Ty)>) -> Ty {
        Ty::Variant(row_from(
            tags.into_iter().map(|(l, t)| (l.to_string(), t)).collect(),
        ))
    }

    fn link(head: Ty, rest: Ty) -> Ty {
        Ty::Record(row_from(vec![("0".into(), head), ("1".into(), rest)]))
    }

    /// `μb. [Empty, Link: {0: head, 1: b}]`
    fn list(binder: TypeVar, head: Ty) -> Ty {
        let body = variant(vec![
            ("Empty", Ty::Unit),
            ("Link", link(head, Ty::Var(binder))),
        ]);
        Ty::Rec(binder, Box::new(body))
    }

    #[test]
    fn types_without_recursion_are_left_alone() {
        let plain = Ty::func(vec![variant(vec![("A", Ty::Int)])], Ty::Bool);
        assert_eq!(canonical(&plain), plain);
    }

    #[test]
    fn alpha_equivalent_types_get_one_form() {
        assert_ne!(list(7, Ty::Int), list(8, Ty::Int));
        assert_eq!(canonical(&list(7, Ty::Int)), canonical(&list(8, Ty::Int)));
    }

    #[test]
    fn a_type_and_its_unfolding_get_one_form() {
        let folded = list(3, Ty::Int);
        assert_eq!(canonical(&folded.unfold()), canonical(&folded));
        assert_eq!(canonical(&folded.unfold().unfold()), canonical(&folded));
    }

    #[test]
    fn a_two_period_unrolling_is_the_same_type_as_the_one_period_form() {
        let one = list(1, Ty::Int);
        let inner = variant(vec![
            ("Empty", Ty::Unit),
            ("Link", link(Ty::Int, Ty::Var(2))),
        ]);
        let two = Ty::Rec(
            2,
            Box::new(variant(vec![
                ("Empty", Ty::Unit),
                ("Link", link(Ty::Int, inner)),
            ])),
        );
        assert_ne!(one, two);
        assert_eq!(canonical(&one), canonical(&two));
    }

    #[test]
    fn different_element_types_stay_different() {
        assert_ne!(canonical(&list(1, Ty::Int)), canonical(&list(1, Ty::Bool)));
    }

    #[test]
    fn nested_binders_are_numbered_by_depth() {
        let inner = list(5, Ty::Int);
        let outer = Ty::Rec(
            9,
            Box::new(variant(vec![
                ("Nil", Ty::Unit),
                ("Cons", link(inner, Ty::Var(9))),
            ])),
        );
        let again = Ty::Rec(
            4,
            Box::new(variant(vec![
                ("Nil", Ty::Unit),
                ("Cons", link(list(6, Ty::Int), Ty::Var(4))),
            ])),
        );
        assert_eq!(canonical(&outer), canonical(&again));
    }

    #[test]
    fn canonicalizing_is_idempotent() {
        let once = canonical(&list(11, Ty::Int));
        assert_eq!(canonical(&once), once);
    }

    #[test]
    fn a_vacuous_binder_is_dropped() {
        let vacuous = Ty::Rec(1, Box::new(variant(vec![("A", Ty::Int)])));
        assert_eq!(canonical(&vacuous), variant(vec![("A", Ty::Int)]));
    }
}
