//! The built-in constraints a type variable can carry, Elm-style. A user never
//! writes one: `==` puts `Eq` on its operands, `+ - *` put `Numeric`, `<` and
//! `/` put `Ordered`, and unification checks each against the type the
//! variable is bound to.

use crate::ty::Ty;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// Any type with no function inside it.
    Eq,
    /// `String`, or a list.
    Appendable,
    /// `Int` or `Float`, or a record whose fields are all `Numeric`.
    Numeric,
    /// `Int` or `Float`.
    Ordered,
    /// The type of a whole-number literal: `Ordered`, and `Int` unless the
    /// context makes it `Float` (ADR 0017).
    Literal,
}

/// The set of constraints on one variable. `Numeric`, `Ordered` and `Literal`
/// each exclude `Appendable`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Kinds {
    eq: bool,
    appendable: bool,
    numeric: bool,
    ordered: bool,
    literal: bool,
}

impl Kinds {
    pub fn of(kind: Kind) -> Kinds {
        Kinds::default().with(kind)
    }

    pub fn with(mut self, kind: Kind) -> Kinds {
        match kind {
            Kind::Eq => self.eq = true,
            Kind::Appendable => self.appendable = true,
            Kind::Numeric => self.numeric = true,
            Kind::Ordered => self.ordered = true,
            Kind::Literal => self.literal = true,
        }
        self
    }

    pub fn iter(self) -> impl Iterator<Item = Kind> {
        [
            (self.eq, Kind::Eq),
            (self.appendable, Kind::Appendable),
            (self.numeric, Kind::Numeric),
            (self.ordered, Kind::Ordered),
            (self.literal, Kind::Literal),
        ]
        .into_iter()
        .filter_map(|(set, kind)| set.then_some(kind))
    }

    pub fn conflicts(self) -> bool {
        (self.numeric || self.ordered || self.literal) && self.appendable
    }

    /// Whether the variable is a whole-number literal's type, which falls back
    /// to `Int` if nothing makes it `Float`.
    pub fn is_literal(self) -> bool {
        self.literal
    }

    /// Whether the variable can only be an `Int` or a `Float`, so a clash with
    /// anything else reads as a mismatch with `Number`.
    pub fn is_scalar(self) -> bool {
        self.literal || self.ordered
    }

    pub fn appendable(self) -> bool {
        self.appendable
    }

    /// What a field of a record or tag payload must satisfy when the whole
    /// does: everything but `Appendable`, which is about the whole's shape.
    pub fn for_fields(self) -> Kinds {
        Kinds {
            appendable: false,
            ..self
        }
    }
}

/// The tags a list is built from.
pub fn is_list_tag(label: &str) -> bool {
    matches!(label, "Empty" | "Link")
}

/// A type that cannot satisfy `kind`: either the part of it that offends, or
/// the variable that would have to be both a number and a string or list.
#[derive(Clone, Debug, PartialEq)]
pub struct Violation {
    pub kind: Kind,
    pub offender: Offender,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Offender {
    Type(Ty),
    Both,
}

impl Violation {
    /// The plain-language message for a type that failed `kind`. `whole` is the
    /// type the constraint was applied to; `op` is the operator that applied
    /// it, when the failure is found at the operator rather than later.
    pub fn message(&self, whole: &Ty, op: Option<&str>) -> String {
        if self.offender == Offender::Both {
            return "this would have to be both a number and a string or list".into();
        }
        match self.kind {
            Kind::Eq => {
                let op = op.unwrap_or("==");
                if matches!(whole, Ty::Func(..)) {
                    format!("can't compare functions with `{op}`")
                } else {
                    format!("can't compare `{whole}` with `{op}`: it has a function inside")
                }
            }
            Kind::Numeric => {
                let op = op.map_or_else(|| "arithmetic".to_string(), |op| format!("`{op}`"));
                format!("{op} needs numbers or records of numbers, but this is `{whole}`")
            }
            Kind::Ordered | Kind::Literal => match op {
                Some("/") => {
                    format!("`/` needs numbers or records of numbers, but this is `{whole}`")
                }
                _ => format!("type mismatch: expected `Number`, found `{whole}`"),
            },
            Kind::Appendable => {
                format!("`join` needs strings or lists, but this is `{whole}`")
            }
        }
    }
}
