#[derive(Hash, Eq, PartialEq, Debug)]
pub enum Ty {
    None,
    Number,
    String,
    Bool,
    Function(Vec<Box<Ty>>),
    Variable(String),
}
