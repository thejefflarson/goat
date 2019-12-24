#[derive(Hash, Eq, PartialEq, Debug, Clone)]
pub enum Ty {
    None,
    Number,
    String,
    Bool,
    Record,
    Array,
    Function(Box<Ty>, Box<Ty>),
    Variable(String),
}
