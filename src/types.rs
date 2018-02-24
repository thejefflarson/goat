pub enum Ty {
    None,
    Number,
    String,
    Bool,
    Function(Vec<Box<Ty>>),
    Variable(String),
}
