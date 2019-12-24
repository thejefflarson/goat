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
