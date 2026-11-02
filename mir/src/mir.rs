macro_rules! id {
    ($($name:ident),*) => {$(
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);
    )*};
}

id!(Local, FuncId, LayoutId, SigId, DataId);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeapKind {
    Record(LayoutId),
    Variant(LayoutId),
    Str,
    Closure(SigId),
    List(LayoutId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MTy {
    Int,
    Float,
    Bool,
    Unit,
    Ptr(HeapKind),
}

impl MTy {
    pub fn is_ptr(self) -> bool {
        matches!(self, MTy::Ptr(_))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Layout {
    Record(Vec<MTy>),
    /// Payload field types, indexed by tag.
    Variant(Vec<Vec<MTy>>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Sig {
    pub params: Vec<MTy>,
    pub ret: MTy,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub funcs: Vec<Func>,
    pub entry: FuncId,
    pub layouts: Vec<Layout>,
    pub sigs: Vec<Sig>,
    pub data: Vec<Vec<u8>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Env {
    pub local: Local,
    pub sig: SigId,
    pub captures: Vec<MTy>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Func {
    pub params: Vec<(Local, MTy)>,
    pub env: Option<Env>,
    pub ret: MTy,
    pub body: Block,
}

pub type Block = Expr;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Const {
    Int(i64),
    Float(f64),
    Bool(bool),
    Unit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloatOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Callee {
    Direct(FuncId),
    Closure(Box<Expr>),
}

/// Using a pointer-typed `Local` moves it; `Field`, `Payload`, `Capture` and
/// `Switch` borrow their operand, and a pointer they load is a fresh owned
/// reference (an implicit `Dup`).
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Const(Const),
    Local(Local),
    Let(Local, Box<Expr>, Box<Expr>),
    BinInt(IntOp, Box<Expr>, Box<Expr>),
    BinFloat(FloatOp, Box<Expr>, Box<Expr>),
    Cmp(CmpOp, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Block>, Box<Block>),
    Switch(Local, Vec<(u32, Block)>, Box<Block>),
    CallDirect(FuncId, Vec<Expr>),
    CallClosure(Box<Expr>, Vec<Expr>),
    TailCall(Callee, Vec<Expr>),
    MakeClosure(FuncId, Vec<Expr>),
    Capture(usize),
    AllocRecord(LayoutId, Vec<Expr>),
    Field(Local, usize),
    AllocVariant(LayoutId, u32, Vec<Expr>),
    Payload(Local, u32, usize),
    StrLit(DataId),
    Dup(Local),
    Drop(Local),
    Trap(String),
}
