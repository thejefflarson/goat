//! The type language: monomorphic types, and type schemes for let-polymorphism.

use std::collections::BTreeSet;
use std::fmt;

/// A unification variable. Resolved to a concrete type by the inferer's
/// substitution.
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
}

impl Ty {
    pub fn func(args: Vec<Ty>, ret: Ty) -> Ty {
        Ty::Func(args, Box::new(ret))
    }

    /// The free type variables of this type, in ascending order.
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
        }
    }
}

/// Render a type variable as a short greek-ish name (`t0`, `t1`, ...) so error
/// messages and inferred-type output stay readable.
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
