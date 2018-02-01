use types::Ty;

pub struct Identifier {
    name: String,
    internal: Option<String>,
    ty: Option<Ty>
}

pub struct Argument {
    identifier: Identifier,
    expression: Option<Box<Expr>>
}

enum Op {
    Plus,
    Minus,
    Mult,
    Div,
    Lte,
    Gte,
    Lt,
    Gt,
}

enum Expr {
    Empty,
    Number(f64),
    Identifier(Identifier),
    Str(String),
    Label(String),
    Argument(Argument),
    Program(Box<Expr>),
    Function(Vec<Argument>),
    Application(Identifier, Vec<Box<Expr>>),
    Conditional(Box<Expr>, Box<Expr>),
    Operation(Box<Expr>, Op, Box<Expr>),
    Declaration(Identifier, Box<Expr>),
}
