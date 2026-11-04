//! The type language: monomorphic types, rows for records, and type schemes
//! for let-polymorphism.

use std::collections::BTreeSet;
use std::fmt;

/// A unification variable. The same numbering space is shared by type variables
/// and row variables; any given id is only ever used in one role.
pub type TypeVar = u32;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    /// An as-yet-unknown type, to be filled in by unification.
    Var(TypeVar),
    Number,
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
    /// is the payload (`Unit` for a bare tag). Constructing a tag yields an open
    /// row; `match` closes it.
    Variant(Row),
}

/// A row of record fields or variant tags. Either closed ([`Row::Empty`] tail), open on a row
/// variable ([`Row::Var`]), or a field prepended to a smaller row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Row {
    Empty,
    Var(TypeVar),
    Extend {
        label: String,
        field: Box<Ty>,
        rest: Box<Row>,
    },
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
            Ty::Number | Ty::Str | Ty::Bool | Ty::Unit => {}
            Ty::Func(args, ret) => {
                for a in args {
                    a.free_vars(out);
                }
                ret.free_vars(out);
            }
            Ty::Record(row) | Ty::Variant(row) => row.free_vars(out),
        }
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
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Var(v) => write!(f, "{}", name_of(*v)),
            Ty::Number => write!(f, "Number"),
            Ty::Str => write!(f, "String"),
            Ty::Bool => write!(f, "Bool"),
            Ty::Unit => write!(f, "Unit"),
            Ty::Func(args, ret) => {
                write!(f, "(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{a}")?;
                }
                write!(f, ") -> {ret}")
            }
            Ty::Record(row) => {
                write!(f, "{{")?;
                row.fmt_fields(f, true, false)?;
                write!(f, "}}")
            }
            Ty::Variant(row) => {
                write!(f, "[")?;
                row.fmt_fields(f, true, true)?;
                write!(f, "]")
            }
        }
    }
}

impl Row {
    /// Format the fields of a row inside its enclosing brackets. `first` tracks
    /// whether a separator is needed before the next field; `bare_unit` prints
    /// a `Unit` payload as just the tag name.
    fn fmt_fields(&self, f: &mut fmt::Formatter<'_>, first: bool, bare_unit: bool) -> fmt::Result {
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
                    write!(f, "{label}: {field}")?;
                }
                rest.fmt_fields(f, false, bare_unit)
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
