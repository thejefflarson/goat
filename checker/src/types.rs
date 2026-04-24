/// Maximum nesting depth for types; unification must check this to prevent
/// infinite loops on self-referential constraints (occurs-check guard).
pub const MAX_TYPE_DEPTH: usize = 128;

#[derive(Eq, PartialEq, Debug)]
pub enum Ty {
    None,
    Number,
    String,
    Bool,
    Union,
    Record(Box<Ty>),
    Array(Box<Ty>),
    Function(Box<Vec<Ty>>, Box<Ty>),
    Variable(String),
}

impl Ty {
    /// Returns the structural nesting depth of this type.
    /// Unification implementations must call this and return an error if the
    /// result exceeds [`MAX_TYPE_DEPTH`], preventing infinite loops.
    pub fn depth(&self) -> usize {
        match self {
            Ty::Record(inner) | Ty::Array(inner) => 1 + inner.depth(),
            Ty::Function(params, ret) => {
                let param_depth = params.iter().map(|p| p.depth()).max().unwrap_or(0);
                1 + param_depth.max(ret.depth())
            }
            _ => 0,
        }
    }
}
