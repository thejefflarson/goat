use std::collections::BTreeMap;

macro_rules! id {
    ($($name:ident),*) => {$(
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);
    )*};
}

id!(Local, FuncId, LayoutId, SigId, DataId, ForeignId);

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

    /// Whether an entry that returns this type has its value dropped after it
    /// is computed. A string root is handed to the host instead.
    pub fn is_discarded_root(self) -> bool {
        matches!(self, MTy::Ptr(kind) if kind != HeapKind::Str)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Layout {
    Record(Vec<MTy>),
    /// Payload field types of each tag the layout's family uses; any other
    /// tag is absent.
    Variant(BTreeMap<u32, Vec<MTy>>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Sig {
    pub params: Vec<MTy>,
    pub ret: MTy,
}

/// The target a program is lowered for: the widths of `Int` and `Float`
/// (ADR 0001, ADR 0017). Pointers are 4 bytes on every profile (wasm32).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Profile {
    /// `Int` is `i64` and `Float` is `f64`.
    #[default]
    Desktop,
    /// `Int` is `i32` and `Float` is `f32`, for MCUs without an FPU or a
    /// 64-bit word.
    Embedded,
}

impl Profile {
    pub fn fits_int(self, n: i64) -> bool {
        match self {
            Profile::Desktop => true,
            Profile::Embedded => i32::try_from(n).is_ok(),
        }
    }

    /// `x` as the profile's `Float` holds it: rounded to the nearest `f32` on
    /// the embedded profile. Rounding the `f64` result of one `+ - * /` gives
    /// the correctly rounded `f32` result, so the interpreter models `f32`
    /// arithmetic with it.
    pub fn round_float(self, x: f64) -> f64 {
        match self {
            Profile::Desktop => x,
            Profile::Embedded => f64::from(x as f32),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub profile: Profile,
    pub funcs: Vec<Func>,
    pub entry: FuncId,
    pub layouts: Vec<Layout>,
    pub sigs: Vec<Sig>,
    pub data: Vec<Vec<u8>>,
    /// The host functions the program calls: one wasm import each.
    pub foreign: Vec<ForeignFn>,
    /// Set for an interactive program (ADR 0015).
    pub interactive: Option<Interactive>,
}

/// What a host needs to drive `init`/`update`/`draw`. The entry function
/// returns a record holding the three values, and a host never sees it: the
/// slots say where `setup` finds each.
#[derive(Debug, Clone, PartialEq)]
pub struct Interactive {
    pub draw_slot: usize,
    pub init_slot: usize,
    pub update_slot: usize,
    /// `(closure, model, event) -> model`: calls the `update` closure.
    pub update: FuncId,
    /// `(closure, model) -> Unit`: calls the `draw` closure and streams the
    /// shapes it returns through the `scene.*` imports.
    pub draw: FuncId,
    /// One constructor per event tag `update` handles. The host is subscribed
    /// to exactly these.
    pub events: Vec<EventCtor>,
    /// The type of the model `init` returns and `update` and `draw` take.
    pub model: MTy,
}

/// `(payload...) -> event`: builds the event `label` from what the host sends
/// (`Tick` a number, a pointer event its `x` and `y`, a key event the
/// `KeyboardEvent.key` string, which it consumes) and returns it owned.
#[derive(Debug, Clone, PartialEq)]
pub struct EventCtor {
    pub label: String,
    pub func: FuncId,
}

/// A host function, identified by the import `module` and `name`. Parameters
/// and result are the boundary types: `Float` (Number), `Bool`, `Unit`, and
/// `Ptr(Str)`.
#[derive(Debug, Clone, PartialEq)]
pub struct ForeignFn {
    pub module: String,
    pub name: String,
    pub params: Vec<MTy>,
    pub ret: MTy,
}

impl ForeignFn {
    /// The `math` and `text` functions the compiler implements itself rather
    /// than importing from the host.
    pub fn intrinsic(&self) -> Option<Intrinsic> {
        match (
            self.module.as_str(),
            self.name.as_str(),
            &self.params[..],
            self.ret,
        ) {
            ("math", "sqrt", [MTy::Float], MTy::Float) => Some(Intrinsic::Float(FloatFn::Sqrt)),
            ("math", "truncate", [MTy::Float], MTy::Int) => {
                Some(Intrinsic::Float(FloatFn::Truncate))
            }
            ("text", "byte_length", [STR], MTy::Int) => Some(Intrinsic::ByteLength),
            ("text", "byte_at", [STR, MTy::Int], MTy::Int) => Some(Intrinsic::ByteAt),
            ("text", "char_count", [STR], MTy::Int) => Some(Intrinsic::CharCount),
            ("text", "char_at", [STR, MTy::Int], STR) => Some(Intrinsic::CharAt),
            _ => None,
        }
    }
}

const STR: MTy = MTy::Ptr(HeapKind::Str);

/// A foreign binding the compiler lowers to a MIR node of its own.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Intrinsic {
    Float(FloatFn),
    ByteLength,
    ByteAt,
    CharCount,
    CharAt,
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
    /// The type of every `Let` and `Unpack` binder in `body`. Parameters and
    /// `env` are typed by their own declarations.
    pub locals: BTreeMap<Local, MTy>,
}

impl Func {
    pub fn local_ty(&self, x: Local) -> Option<MTy> {
        let param = self.params.iter().find(|(l, _)| *l == x).map(|(_, t)| *t);
        let env = self
            .env
            .as_ref()
            .filter(|env| env.local == x)
            .map(|env| MTy::Ptr(HeapKind::Closure(env.sig)));
        param.or(env).or_else(|| self.locals.get(&x).copied())
    }
}

pub type Block = Expr;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Const {
    Int(i64),
    Float(f64),
    Bool(bool),
    Unit,
}

/// What an `Int` operation that overflows traps with, what a division or
/// remainder by zero traps with, and what turning a `Float` that has no `Int`
/// (NaN, infinity, out of range) into one traps with (ADR 0017): never a
/// wrapped or saturated result.
pub const INT_OVERFLOW: &str = "this number got too big";
pub const DIVISION_BY_ZERO: &str = "division by zero";
pub const NOT_A_WHOLE_NUMBER: &str = "this number can't be made a whole number";

/// What `StrByte` and `StrChar` trap with when their position is not inside
/// the string.
pub const BYTE_OUT_OF_RANGE: &str = "this position is outside the string";

/// Integer arithmetic traps on overflow rather than wrapping. `Div` rounds
/// toward zero; `FloorDiv` and `Mod` round toward negative infinity, so
/// `a == FloorDiv(a, b) * b + Mod(a, b)` and `Mod` takes the divisor's sign.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntOp {
    Add,
    Sub,
    Mul,
    Div,
    FloorDiv,
    Mod,
}

/// A one-operand `Float` function: the primitives the prelude's math builds
/// on. `Sqrt` is a `Float`; `Truncate` drops the fraction and is an `Int`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloatFn {
    Sqrt,
    Truncate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

/// Text for the host's current output line: `Number` writes a number, `Str`
/// the bytes of a string, `Lit` the bytes of a data-segment string, and `End`
/// finishes the line. Each yields `Unit`, and none may be dropped or reordered.
/// `Str` borrows its operand like `Field` does.
#[derive(Debug, Clone, PartialEq)]
pub enum Write {
    Number(Box<Expr>),
    Str(Local),
    Lit(DataId),
    End,
}

/// What a `CallForeign` and a `Write` do to the world outside the program.
/// Passes that rewrite a function must leave its `effects` unchanged, which
/// `insert_rc` asserts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Effect {
    Foreign(ForeignId),
    Write,
}

/// Using a pointer-typed `Local` moves it; `Field`, `Payload`, `Capture` and
/// `Switch` borrow their operand, and a pointer they load is a fresh owned
/// reference (an implicit `Dup`).
///
/// `Unpack` is the consuming destructure: it moves the fields out of a cell
/// the local solely owns, leaving the local as a reuse token that exactly one
/// of `ReuseVariant` or `Free` must consume.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Const(Const),
    Local(Local),
    Let(Local, Box<Expr>, Box<Expr>),
    BinInt(IntOp, Box<Expr>, Box<Expr>),
    BinFloat(FloatOp, Box<Expr>, Box<Expr>),
    /// An `Int` widened to the `Float` nearest it.
    IntToFloat(Box<Expr>),
    /// A `Float` primitive; see [`FloatFn`] for the type each gives.
    FloatFn(FloatFn, Box<Expr>),
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
    Unpack(Local, u32, Vec<Local>, Box<Expr>),
    ReuseVariant(Local, LayoutId, u32, Vec<Expr>),
    /// A record of the same layout as the local, built from the field values:
    /// the local's cell is overwritten and returned when it is the sole
    /// reference (`rc == 1`), and a fresh cell is allocated otherwise. It moves
    /// the local after evaluating the fields, which may still borrow it.
    ReuseRecord(Local, LayoutId, Vec<Expr>),
    Free(Local),
    StrLit(DataId),
    /// Whether two strings hold the same bytes; borrows both operands.
    StrEq(Local, Local),
    /// The number of UTF-8 bytes in a string; borrows it.
    StrLen(Local),
    /// The byte (`0..=255`) of a string at a 1-based position held in an `Int`
    /// local; borrows the string. A position outside `1..=StrLen` traps with
    /// `BYTE_OUT_OF_RANGE`.
    StrByte(Local, Local),
    /// The number of code points in a string, counted as the bytes that are
    /// not UTF-8 continuation bytes; borrows it.
    StrChars(Local),
    /// A new one-code-point string (`rc = 1`) from the code point at a 1-based
    /// position held in an `Int` local; borrows the string. A position outside
    /// `1..=StrChars` traps with `BYTE_OUT_OF_RANGE`. A code point is a lead
    /// byte and the continuation bytes after it, so the copy never leaves the
    /// string even when it is not valid UTF-8.
    StrChar(Local, Local),
    Write(Write),
    /// A call to a host function. Effectful even when it returns `Unit`: it is
    /// never dropped, duplicated, or reordered (see `effects`). Arguments are
    /// locals so that a pointer passed to the host is borrowed for the call,
    /// as `Write::Str` borrows, and the caller keeps its reference. A returned
    /// string is a fresh owned reference.
    CallForeign(ForeignId, Vec<Local>),
    Dup(Local),
    Drop(Local),
    Trap(String),
    /// Names the source range `start..end` as the user code now running a
    /// call into the prelude, so a trap inside it can be blamed on that call.
    Site(usize, usize),
}

impl Expr {
    /// Calls `f` on each direct subexpression, in evaluation order.
    pub fn for_each_child<'a>(&'a self, f: &mut impl FnMut(&'a Expr)) {
        match self {
            Expr::Const(_)
            | Expr::Local(_)
            | Expr::Capture(_)
            | Expr::Field(..)
            | Expr::Payload(..)
            | Expr::Free(_)
            | Expr::StrLit(_)
            | Expr::StrEq(..)
            | Expr::StrLen(_)
            | Expr::StrByte(..)
            | Expr::StrChars(_)
            | Expr::StrChar(..)
            | Expr::CallForeign(..)
            | Expr::Write(Write::Str(_) | Write::Lit(_) | Write::End)
            | Expr::Dup(_)
            | Expr::Drop(_)
            | Expr::Trap(_)
            | Expr::Site(..) => {}
            Expr::Let(_, a, b)
            | Expr::BinInt(_, a, b)
            | Expr::BinFloat(_, a, b)
            | Expr::Cmp(_, a, b) => {
                f(a);
                f(b);
            }
            Expr::If(c, t, o) => {
                f(c);
                f(t);
                f(o);
            }
            Expr::Switch(_, arms, default) => {
                arms.iter().for_each(|(_, b)| f(b));
                f(default);
            }
            Expr::CallDirect(_, args)
            | Expr::MakeClosure(_, args)
            | Expr::AllocRecord(_, args)
            | Expr::AllocVariant(_, _, args)
            | Expr::ReuseVariant(_, _, _, args)
            | Expr::ReuseRecord(_, _, args) => args.iter().for_each(f),
            Expr::CallClosure(c, args) => {
                f(c);
                args.iter().for_each(f);
            }
            Expr::TailCall(callee, args) => {
                if let Callee::Closure(c) = callee {
                    f(c);
                }
                args.iter().for_each(f);
            }
            Expr::Unpack(_, _, _, body) => f(body),
            Expr::IntToFloat(value)
            | Expr::FloatFn(_, value)
            | Expr::Write(Write::Number(value)) => f(value),
        }
    }

    /// The subexpression a `Let` or operator node evaluates first: a `Let`'s
    /// right-hand side, the left side of a binary operator or comparison, the
    /// value under a conversion, the condition of an `If`. A left-associative
    /// chain (`a + b + c`, `a and b and c`) nests down these, so walking them
    /// with an explicit stack costs no call stack per link.
    pub fn leading_operand(&self) -> Option<&Expr> {
        match self {
            Expr::Let(_, a, _)
            | Expr::BinInt(_, a, _)
            | Expr::BinFloat(_, a, _)
            | Expr::Cmp(_, a, _)
            | Expr::IntToFloat(a)
            | Expr::FloatFn(_, a)
            | Expr::If(a, _, _) => Some(a),
            _ => None,
        }
    }

    /// An `IntToFloat` or `FloatFn` node over `operand` in place of its own.
    pub fn with_operand(&self, operand: Expr) -> Expr {
        let operand = Box::new(operand);
        match self {
            Expr::FloatFn(function, _) => Expr::FloatFn(*function, operand),
            _ => Expr::IntToFloat(operand),
        }
    }

    /// Calls `f` on `self` and everything under it, each node before its
    /// children, with no stack proportional to the tree's depth: a long block
    /// is a long chain of `Let`s.
    pub fn for_each_node<'a>(&'a self, f: &mut impl FnMut(&'a Expr)) {
        let mut pending = vec![self];
        while let Some(e) = pending.pop() {
            f(e);
            let at = pending.len();
            e.for_each_child(&mut |c| pending.push(c));
            pending[at..].reverse();
        }
    }
}

/// A node a walk over a chain of operators has started and is holding until an
/// operand has a result of type `T`: `Value` for the interpreter, the lowered
/// type for the wasm lowering.
pub enum OperandWait<'e, T> {
    /// The node's leading operand (see [`Expr::leading_operand`]).
    First(&'e Expr),
    /// The right operand of a binary node, given the left operand's result.
    Second(&'e Expr, T),
}

/// What a waiting node does once its operand has a result.
pub enum OperandStep<'e, T> {
    /// The expression to walk next in place of the node.
    Next(&'e Expr),
    /// The node still needs this right operand.
    Right(OperandWait<'e, T>, &'e Expr),
    /// The node's own result.
    Done(T),
}

/// The effects `e` performs, in evaluation order.
pub fn effects(e: &Expr) -> Vec<Effect> {
    let mut out = Vec::new();
    e.for_each_node(&mut |e| match e {
        Expr::CallForeign(f, _) => out.push(Effect::Foreign(*f)),
        Expr::Write(_) => out.push(Effect::Write),
        _ => {}
    });
    out
}
