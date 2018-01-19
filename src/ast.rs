enum Expr {
    Empty,
    Number(f64),
    Identifier(String),
    Str(String),
    Label(String),
    Argument(Identifier, Option<Box<Expr>>),
    Program(Box<Expr>),
    Function(Vec<Argument>),
    Application(Identifier, Vec<Box<Expr>>),
    Conditional(Program, Program),
    Operation(Box<Expr>, Op, Box<Expr>),
    Declaration(Identifier, Box<Expr>),
}
