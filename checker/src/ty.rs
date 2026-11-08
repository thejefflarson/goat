//! The type language: monomorphic types, rows for records, and type schemes
//! for let-polymorphism.

use crate::hir::Boundary;
use crate::infer::subst_vars;
use std::collections::{BTreeSet, HashMap};
use std::fmt;

/// A unification variable. The same numbering space is shared by type variables
/// and row variables; any given id is only ever used in one role.
pub type TypeVar = u32;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    /// An as-yet-unknown type, to be filled in by unification.
    Var(TypeVar),
    /// A whole number: `i64` on desktop and web (ADR 0017).
    Int,
    /// A number with a fraction: `f64` on desktop and web.
    Float,
    Str,
    Bool,
    /// The type of an expression that yields no value (an empty program, a
    /// side-effecting conditional with no else branch).
    Unit,
    /// A function from positional argument types to a result type. Goat's
    /// `program(a, b) do ... done`.
    Func(Vec<Ty>, Box<Ty>),
    /// A record: a collection of labeled fields, represented as a [`Row`]. This
    /// is the scoped-labels foundation — a record literal is a closed row, and
    /// field access unifies against an open one.
    Record(Row),
    /// A variant: the dual of a record. Each label is a tag and its field type
    /// is the payload (`Unit` for a bare tag). Constructing an undeclared tag
    /// yields an open row, which `match` closes; a tag of a [`Group`] yields the
    /// group's closed row.
    Variant(Row),
    /// A recursive type `μv. body`: `Var(v)` inside `body` stands for the whole
    /// type. The binder is a fresh id that is never bound by unification, and
    /// every path from the binder to an occurrence crosses a variant payload,
    /// so unfolding always exposes a constructor.
    Rec(TypeVar, Box<Ty>),
}

impl From<Boundary> for Ty {
    fn from(boundary: Boundary) -> Ty {
        match boundary {
            Boundary::Number => Ty::Float,
            Boundary::Int => Ty::Int,
            Boundary::Bool => Ty::Bool,
            Boundary::Unit => Ty::Unit,
            Boundary::Str => Ty::Str,
        }
    }
}

/// A row of record fields or variant tags. Either closed ([`Row::Empty`] tail), open on a row
/// variable ([`Row::Var`]), or a field prepended to a smaller row.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Row {
    Empty,
    Var(TypeVar),
    Extend {
        label: String,
        field: Box<Ty>,
        rest: Box<Row>,
    },
}

/// The tags of one `tag` declaration: a closed variant type. A payload that
/// mentions the group itself holds `Ty::Var(Group::SELF)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Group {
    pub tags: Vec<(String, Ty)>,
    pub recursive: bool,
}

impl Group {
    pub const SELF: TypeVar = TypeVar::MAX;

    /// The group as a type, closed over `binder` when it is recursive.
    pub fn instantiate(&self, binder: TypeVar) -> Ty {
        let mapping = HashMap::from([(Self::SELF, binder)]);
        let row = Row::of(
            self.tags
                .iter()
                .map(|(label, payload)| (label.clone(), subst_vars(payload, &mapping))),
        );
        let body = Ty::Variant(row);
        if self.recursive {
            Ty::Rec(binder, Box::new(body))
        } else {
            body
        }
    }
}

impl Row {
    /// A closed row of `fields`, in order.
    pub fn of(
        fields: impl IntoIterator<Item = (String, Ty), IntoIter: DoubleEndedIterator>,
    ) -> Row {
        fields
            .into_iter()
            .rev()
            .fold(Row::Empty, |rest, (label, field)| Row::Extend {
                label,
                field: Box::new(field),
                rest: Box::new(rest),
            })
    }
}

impl Ty {
    pub fn func(args: Vec<Ty>, ret: Ty) -> Ty {
        Ty::Func(args, Box::new(ret))
    }

    /// The free variables of this type (type and row variables alike), in
    /// ascending order.
    pub fn free_vars(&self, out: &mut BTreeSet<TypeVar>) {
        match self {
            Ty::Var(v) => {
                out.insert(*v);
            }
            Ty::Int | Ty::Float | Ty::Str | Ty::Bool | Ty::Unit => {}
            Ty::Func(args, ret) => {
                for a in args {
                    a.free_vars(out);
                }
                ret.free_vars(out);
            }
            Ty::Record(row) | Ty::Variant(row) => row.free_vars(out),
            Ty::Rec(binder, body) => {
                let mut inner = BTreeSet::new();
                body.free_vars(&mut inner);
                inner.remove(binder);
                out.extend(inner);
            }
        }
    }

    /// The binders of every `Rec` in this type.
    pub fn rec_binders(&self, out: &mut Vec<TypeVar>) {
        if let Ty::Rec(binder, _) = self {
            out.push(*binder);
        }
        for child in self.children() {
            child.rec_binders(out);
        }
    }

    /// The types directly inside this one.
    fn children(&self) -> Vec<&Ty> {
        match self {
            Ty::Func(args, ret) => args.iter().chain(std::iter::once(&**ret)).collect(),
            Ty::Record(row) | Ty::Variant(row) => row.fields().collect(),
            Ty::Rec(_, body) => vec![body],
            Ty::Var(_) | Ty::Int | Ty::Float | Ty::Str | Ty::Bool | Ty::Unit => Vec::new(),
        }
    }

    fn map_children(&self, f: &impl Fn(&Ty) -> Ty) -> Ty {
        match self {
            Ty::Func(args, ret) => Ty::Func(args.iter().map(f).collect(), Box::new(f(ret))),
            Ty::Record(row) => Ty::Record(row.map_fields(f)),
            Ty::Variant(row) => Ty::Variant(row.map_fields(f)),
            Ty::Rec(binder, body) => Ty::Rec(*binder, Box::new(f(body))),
            Ty::Var(_) | Ty::Int | Ty::Float | Ty::Str | Ty::Bool | Ty::Unit => self.clone(),
        }
    }

    /// Replace the free occurrences of `Var(var)` with `with`.
    pub fn substitute(&self, var: TypeVar, with: &Ty) -> Ty {
        match self {
            Ty::Var(v) if *v == var => with.clone(),
            Ty::Rec(binder, _) if *binder == var => self.clone(),
            _ => self.map_children(&|t| t.substitute(var, with)),
        }
    }

    /// One unfolding of a recursive type: `μv. B` becomes `B[v := μv. B]`.
    pub fn unfold(&self) -> Ty {
        match self {
            Ty::Rec(binder, body) => body.substitute(*binder, self),
            other => other.clone(),
        }
    }

    /// Unfold until the head is a constructor. A contractive type needs one
    /// unfolding per binder stacked at its head; a `Rec` still at the head after
    /// that is vacuous (`μv. v`) and stays folded.
    pub fn unfold_head(&self) -> Ty {
        let mut stacked = 0;
        let mut cursor = self;
        while let Ty::Rec(_, body) = cursor {
            stacked += 1;
            cursor = body;
        }
        let mut ty = self.clone();
        for _ in 0..=stacked {
            if !matches!(ty, Ty::Rec(..)) {
                break;
            }
            ty = ty.unfold();
        }
        ty
    }

    /// Re-fold every type that is the unfolding of a recursive type inside it,
    /// so a type reads `μl. [Empty, Link: {0: a, 1: l}]` rather than that
    /// unfolded once with the `μ` one level down.
    pub fn fold_rec(&self) -> Ty {
        let folded = self.map_children(&Ty::fold_rec);
        if !matches!(folded, Ty::Rec(..))
            && let Some(rec) = folded.find_unfolding_to(&folded)
        {
            return rec;
        }
        folded
    }

    /// A `Rec` among this type's sub-terms whose unfolding is `target`.
    fn find_unfolding_to(&self, target: &Ty) -> Option<Ty> {
        for child in self.children() {
            if matches!(child, Ty::Rec(..)) && child.unfold() == *target {
                return Some(child.clone());
            }
            if let Some(found) = child.find_unfolding_to(target) {
                return Some(found);
            }
        }
        None
    }
}

impl Row {
    pub fn free_vars(&self, out: &mut BTreeSet<TypeVar>) {
        match self {
            Row::Empty => {}
            Row::Var(v) => {
                out.insert(*v);
            }
            Row::Extend { field, rest, .. } => {
                field.free_vars(out);
                rest.free_vars(out);
            }
        }
    }

    fn fields(&self) -> impl Iterator<Item = &Ty> {
        let mut cursor = Some(self);
        std::iter::from_fn(move || match cursor? {
            Row::Extend { field, rest, .. } => {
                cursor = Some(rest);
                Some(&**field)
            }
            Row::Empty | Row::Var(_) => None,
        })
    }

    fn map_fields(&self, f: &impl Fn(&Ty) -> Ty) -> Row {
        match self {
            Row::Extend { label, field, rest } => Row::Extend {
                label: label.clone(),
                field: Box::new(f(field)),
                rest: Box::new(rest.map_fields(f)),
            },
            other => other.clone(),
        }
    }
}

/// A type as written for a reader. `Display` calls both numeric types
/// `Number`, the kid-facing name; [`Ty::exact`] says `Int` or `Float`.
struct Shown<'a> {
    ty: &'a Ty,
    exact: bool,
}

impl Ty {
    pub fn exact(&self) -> impl fmt::Display + '_ {
        Shown {
            ty: self,
            exact: true,
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Shown {
            ty: self,
            exact: false,
        }
        .fmt(f)
    }
}

impl fmt::Display for Shown<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let show = |ty| Shown {
            ty,
            exact: self.exact,
        };
        match self.ty {
            Ty::Var(v) => write!(f, "{}", name_of(*v)),
            Ty::Int if self.exact => write!(f, "Int"),
            Ty::Float if self.exact => write!(f, "Float"),
            Ty::Int | Ty::Float => write!(f, "Number"),
            Ty::Str => write!(f, "String"),
            Ty::Bool => write!(f, "Bool"),
            Ty::Unit => write!(f, "Unit"),
            Ty::Func(args, ret) => {
                write!(f, "(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", show(a))?;
                }
                write!(f, ") -> {}", show(ret))
            }
            Ty::Record(row) => {
                write!(f, "{{")?;
                row.fmt_fields(f, true, false, self.exact)?;
                write!(f, "}}")
            }
            Ty::Variant(row) => {
                write!(f, "[")?;
                row.fmt_fields(f, true, true, self.exact)?;
                write!(f, "]")
            }
            Ty::Rec(binder, body) => write!(f, "μ{}. {}", name_of(*binder), show(body)),
        }
    }
}

impl Row {
    /// Format the fields of a row inside its enclosing brackets. `first` tracks
    /// whether a separator is needed before the next field; `bare_unit` prints
    /// a `Unit` payload as just the tag name.
    fn fmt_fields(
        &self,
        f: &mut fmt::Formatter<'_>,
        first: bool,
        bare_unit: bool,
        exact: bool,
    ) -> fmt::Result {
        match self {
            Row::Empty => Ok(()),
            Row::Var(v) => {
                if first {
                    write!(f, "{}", name_of(*v))
                } else {
                    write!(f, " | {}", name_of(*v))
                }
            }
            Row::Extend { label, field, rest } => {
                if !first {
                    write!(f, ", ")?;
                }
                if bare_unit && **field == Ty::Unit {
                    write!(f, "{label}")?;
                } else {
                    write!(f, "{label}: {}", Shown { ty: field, exact })?;
                }
                rest.fmt_fields(f, false, bare_unit, exact)
            }
        }
    }
}

/// Render a type variable as a short name (`t0`, `t1`, ...) so error messages
/// and inferred-type output stay readable.
fn name_of(v: TypeVar) -> String {
    format!("t{v}")
}

/// A type scheme `forall vars. ty` — a polymorphic type produced by
/// generalizing a declaration's type. Instantiated with fresh variables at
/// each use site, which is what gives `let`-bound names polymorphism.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Scheme {
    pub vars: Vec<TypeVar>,
    pub ty: Ty,
}

impl Scheme {
    /// A monomorphic scheme: no quantified variables.
    pub fn mono(ty: Ty) -> Scheme {
        Scheme {
            vars: Vec::new(),
            ty,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn variant(tags: &[(&str, Ty)], tail: Row) -> Ty {
        let row = tags
            .iter()
            .rev()
            .fold(tail, |rest, (label, field)| Row::Extend {
                label: label.to_string(),
                field: Box::new(field.clone()),
                rest: Box::new(rest),
            });
        Ty::Variant(row)
    }

    fn list(binder: TypeVar) -> Ty {
        let link = Ty::Record(Row::Extend {
            label: "0".into(),
            field: Box::new(Ty::Int),
            rest: Box::new(Row::Extend {
                label: "1".into(),
                field: Box::new(Ty::Var(binder)),
                rest: Box::new(Row::Empty),
            }),
        });
        let body = variant(&[("Empty", Ty::Unit), ("Link", link)], Row::Empty);
        Ty::Rec(binder, Box::new(body))
    }

    fn free(ty: &Ty) -> Vec<TypeVar> {
        let mut out = BTreeSet::new();
        ty.free_vars(&mut out);
        out.into_iter().collect()
    }

    #[test]
    fn a_recursive_type_prints_its_binder() {
        assert_eq!(
            list(7).to_string(),
            "μt7. [Empty, Link: {0: Number, 1: t7}]"
        );
        let func = Ty::func(vec![list(7)], list(8));
        assert_eq!(
            func.to_string(),
            "(μt7. [Empty, Link: {0: Number, 1: t7}]) -> μt8. [Empty, Link: {0: Number, 1: t8}]"
        );
    }

    #[test]
    fn degenerate_recursive_types_print_and_unfold_without_looping() {
        let vacuous = Ty::Rec(0, Box::new(Ty::Int));
        assert_eq!(vacuous.to_string(), "μt0. Number");
        assert_eq!(vacuous.unfold_head(), Ty::Int);

        let empty = Ty::Rec(0, Box::new(Ty::Variant(Row::Empty)));
        assert_eq!(empty.to_string(), "μt0. []");
        assert_eq!(empty.unfold_head(), Ty::Variant(Row::Empty));

        let bare = Ty::Rec(0, Box::new(Ty::Var(0)));
        assert_eq!(bare.to_string(), "μt0. t0");
        assert_eq!(bare.unfold_head(), bare);

        let stacked = Ty::Rec(0, Box::new(Ty::Rec(1, Box::new(Ty::Var(0)))));
        assert!(matches!(stacked.unfold_head(), Ty::Rec(..)));
        assert_eq!(stacked.fold_rec().to_string(), stacked.to_string());
    }

    #[test]
    fn unfolding_exposes_the_constructor_and_keeps_the_back_edge() {
        let unfolded = list(3).unfold_head();
        assert_eq!(
            unfolded.to_string(),
            "[Empty, Link: {0: Number, 1: μt3. [Empty, Link: {0: Number, 1: t3}]}]"
        );
        assert_eq!(unfolded.fold_rec(), list(3));
    }

    #[test]
    fn folding_leaves_a_type_with_nothing_to_fold_alone() {
        let plain = Ty::func(vec![Ty::Int], variant(&[("A", Ty::Unit)], Row::Var(1)));
        assert_eq!(plain.fold_rec(), plain);
        assert_eq!(list(3).fold_rec(), list(3));
    }

    #[test]
    fn the_binder_is_not_a_free_variable() {
        assert_eq!(free(&list(5)), Vec::<TypeVar>::new());
        let open = Ty::Rec(5, Box::new(variant(&[("Link", Ty::Var(5))], Row::Var(9))));
        assert_eq!(free(&open), vec![9]);
        let outside = Ty::func(vec![Ty::Var(5)], list(5));
        assert_eq!(free(&outside), vec![5]);
    }

    #[test]
    fn substitution_stops_at_a_rebinding() {
        let inner = list(5);
        assert_eq!(inner.substitute(5, &Ty::Bool), inner);
        let outside = Ty::func(vec![Ty::Var(5)], list(5));
        assert_eq!(
            outside.substitute(5, &Ty::Bool),
            Ty::func(vec![Ty::Bool], list(5))
        );
    }

    #[test]
    fn binders_are_collected_through_nesting() {
        let nested = Ty::func(vec![list(1)], list(2));
        let mut binders = Vec::new();
        nested.rec_binders(&mut binders);
        assert_eq!(binders, vec![1, 2]);
    }
}
