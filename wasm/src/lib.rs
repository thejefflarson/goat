use std::collections::HashMap;
use std::fmt;

use goat_mir::*;
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, DataSection, EntityType, ExportKind, ExportSection,
    Function, FunctionSection, GlobalSection, GlobalType, ImportSection, Instruction,
    MemorySection, MemoryType, Module, TypeSection, ValType,
};

const DATA_BASE: u32 = 8;
const IMPORTS: u32 = 2;
const PRINT_NUMBER: u32 = 0;
const PRINT_BOOL: u32 = 1;

#[derive(Debug, Clone, PartialEq)]
pub enum EmitError {
    Unsupported(&'static str),
    UnknownFunc(FuncId),
    UnboundLocal(Local),
    Malformed(&'static str),
}

impl fmt::Display for EmitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EmitError::Unsupported(what) => write!(f, "unsupported by the wasm backend: {what}"),
            EmitError::UnknownFunc(id) => write!(f, "unknown function {}", id.0),
            EmitError::UnboundLocal(l) => write!(f, "unbound local {}", l.0),
            EmitError::Malformed(what) => write!(f, "malformed MIR: {what}"),
        }
    }
}

impl std::error::Error for EmitError {}

type Code = Vec<Instruction<'static>>;

/// `None` is a diverging expression (a trap), which has every type.
type Ty = Option<MTy>;

/// `Int` is i32 on wasm32 and `Float` is f64 (ADR 0001); `Unit` is erased.
fn val_type(ty: MTy) -> Option<ValType> {
    match ty {
        MTy::Int | MTy::Bool | MTy::Ptr(_) => Some(ValType::I32),
        MTy::Float => Some(ValType::F64),
        MTy::Unit => None,
    }
}

fn val_types(tys: impl IntoIterator<Item = MTy>) -> Vec<ValType> {
    tys.into_iter().filter_map(val_type).collect()
}

pub fn emit(program: &Program) -> Result<Vec<u8>, EmitError> {
    let mut types = Types::default();
    let print_number = types.intern(vec![ValType::F64], vec![]);
    let print_bool = types.intern(vec![ValType::I32], vec![]);
    let entry_ty = types.intern(vec![], vec![]);

    let mut bodies = Vec::new();
    let mut func_types = Vec::new();
    for func in &program.funcs {
        let params = val_types(func.params.iter().map(|&(_, ty)| ty));
        func_types.push(types.intern(params, val_types([func.ret])));
        bodies.push(lower_func(program, func)?);
    }
    bodies.push(entry_wrapper(program)?);
    func_types.push(entry_ty);

    let data: Vec<u8> = program.data.concat();
    let heap_start = (DATA_BASE + data.len() as u32).next_multiple_of(8);

    let mut module = Module::new();
    module.section(&types.section());

    let mut imports = ImportSection::new();
    imports.import("goat", "print_number", EntityType::Function(print_number));
    imports.import("goat", "print_bool", EntityType::Function(print_bool));
    module.section(&imports);

    let mut functions = FunctionSection::new();
    for ty in &func_types {
        functions.function(*ty);
    }
    module.section(&functions);

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    module.section(&memory);

    let mut globals = GlobalSection::new();
    globals.global(
        GlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        },
        &ConstExpr::i32_const(heap_start as i32),
    );
    module.section(&globals);

    let mut exports = ExportSection::new();
    exports.export("memory", ExportKind::Memory, 0);
    exports.export(
        "goat_entry",
        ExportKind::Func,
        IMPORTS + program.funcs.len() as u32,
    );
    module.section(&exports);

    let mut code = CodeSection::new();
    for body in &bodies {
        code.function(body);
    }
    module.section(&code);

    let mut segments = DataSection::new();
    segments.active(0, &ConstExpr::i32_const(DATA_BASE as i32), data);
    module.section(&segments);

    Ok(module.finish())
}

#[derive(Default)]
struct Types(Vec<(Vec<ValType>, Vec<ValType>)>);

impl Types {
    fn intern(&mut self, params: Vec<ValType>, results: Vec<ValType>) -> u32 {
        let sig = (params, results);
        let index = self.0.iter().position(|s| *s == sig).unwrap_or_else(|| {
            self.0.push(sig);
            self.0.len() - 1
        });
        index as u32
    }

    fn section(&self) -> TypeSection {
        let mut section = TypeSection::new();
        for (params, results) in &self.0 {
            section
                .ty()
                .function(params.iter().copied(), results.iter().copied());
        }
        section
    }
}

/// An `Int` root prints through `print_number`, since both are numbers.
fn entry_wrapper(program: &Program) -> Result<Function, EmitError> {
    let root = program
        .funcs
        .get(program.entry.0 as usize)
        .ok_or(EmitError::UnknownFunc(program.entry))?;
    if !root.params.is_empty() {
        return Err(EmitError::Malformed("entry function takes parameters"));
    }
    let mut f = Function::new([]);
    f.instruction(&Instruction::Call(IMPORTS + program.entry.0));
    match root.ret {
        MTy::Float => {
            f.instruction(&Instruction::Call(PRINT_NUMBER));
        }
        MTy::Int => {
            f.instruction(&Instruction::F64ConvertI32S);
            f.instruction(&Instruction::Call(PRINT_NUMBER));
        }
        MTy::Bool => {
            f.instruction(&Instruction::Call(PRINT_BOOL));
        }
        MTy::Unit => {}
        MTy::Ptr(_) => return Err(EmitError::Unsupported("heap-valued root")),
    }
    f.instruction(&Instruction::End);
    Ok(f)
}

fn lower_func(program: &Program, func: &Func) -> Result<Function, EmitError> {
    if func.env.is_some() {
        return Err(EmitError::Unsupported("closure bodies"));
    }
    let mut cx = FuncCx {
        program,
        scope: HashMap::new(),
        next_local: 0,
        declared: Vec::new(),
    };
    for &(local, ty) in &func.params {
        cx.bind(local, ty);
    }
    cx.declared.clear();
    let mut code = Code::new();
    cx.lower(&func.body, &mut code)?;
    let mut f = Function::new_with_locals_types(cx.declared);
    for instr in &code {
        f.instruction(instr);
    }
    f.instruction(&Instruction::End);
    Ok(f)
}

struct FuncCx<'a> {
    program: &'a Program,
    scope: HashMap<Local, (Option<u32>, MTy)>,
    next_local: u32,
    /// Wasm locals beyond the parameters; parameters are declared by the signature.
    declared: Vec<ValType>,
}

impl FuncCx<'_> {
    fn bind(&mut self, local: Local, ty: MTy) -> Option<u32> {
        let index = val_type(ty).map(|vt| {
            let index = self.next_local;
            self.next_local += 1;
            self.declared.push(vt);
            index
        });
        self.scope.insert(local, (index, ty));
        index
    }

    fn lower(&mut self, expr: &Expr, out: &mut Code) -> Result<Ty, EmitError> {
        match expr {
            Expr::Const(c) => Ok(Some(match *c {
                Const::Int(n) => {
                    out.push(Instruction::I32Const(n as i32));
                    MTy::Int
                }
                Const::Float(x) => {
                    out.push(Instruction::F64Const(x.into()));
                    MTy::Float
                }
                Const::Bool(b) => {
                    out.push(Instruction::I32Const(b as i32));
                    MTy::Bool
                }
                Const::Unit => MTy::Unit,
            })),
            Expr::Local(l) => {
                let &(index, ty) = self.scope.get(l).ok_or(EmitError::UnboundLocal(*l))?;
                if let Some(index) = index {
                    out.push(Instruction::LocalGet(index));
                }
                Ok(Some(ty))
            }
            Expr::Let(l, rhs, body) => {
                let Some(ty) = self.lower(rhs, out)? else {
                    return Ok(None);
                };
                if let Some(index) = self.bind(*l, ty) {
                    out.push(Instruction::LocalSet(index));
                }
                self.lower(body, out)
            }
            Expr::BinInt(op, a, b) => {
                self.operands(a, b, MTy::Int, out)?;
                out.push(match op {
                    IntOp::Add => Instruction::I32Add,
                    IntOp::Sub => Instruction::I32Sub,
                    IntOp::Mul => Instruction::I32Mul,
                    IntOp::Div => Instruction::I32DivS,
                });
                Ok(Some(MTy::Int))
            }
            Expr::BinFloat(op, a, b) => {
                self.operands(a, b, MTy::Float, out)?;
                out.push(match op {
                    FloatOp::Add => Instruction::F64Add,
                    FloatOp::Sub => Instruction::F64Sub,
                    FloatOp::Mul => Instruction::F64Mul,
                    FloatOp::Div => Instruction::F64Div,
                });
                Ok(Some(MTy::Float))
            }
            Expr::Cmp(op, a, b) => {
                let ta = self.lower(a, out)?;
                let tb = self.lower(b, out)?;
                if ta.zip(tb).is_some_and(|(x, y)| x != y) {
                    return Err(EmitError::Malformed("comparison operand types differ"));
                }
                let instr = match (ta.or(tb), op) {
                    (Some(MTy::Int), CmpOp::Eq) => Instruction::I32Eq,
                    (Some(MTy::Int), CmpOp::Ne) => Instruction::I32Ne,
                    (Some(MTy::Int), CmpOp::Lt) => Instruction::I32LtS,
                    (Some(MTy::Int), CmpOp::Le) => Instruction::I32LeS,
                    (Some(MTy::Int), CmpOp::Gt) => Instruction::I32GtS,
                    (Some(MTy::Int), CmpOp::Ge) => Instruction::I32GeS,
                    (Some(MTy::Float), CmpOp::Eq) => Instruction::F64Eq,
                    (Some(MTy::Float), CmpOp::Ne) => Instruction::F64Ne,
                    (Some(MTy::Float), CmpOp::Lt) => Instruction::F64Lt,
                    (Some(MTy::Float), CmpOp::Le) => Instruction::F64Le,
                    (Some(MTy::Float), CmpOp::Gt) => Instruction::F64Gt,
                    (Some(MTy::Float), CmpOp::Ge) => Instruction::F64Ge,
                    _ => return Err(EmitError::Malformed("comparison operands")),
                };
                out.push(instr);
                Ok(Some(MTy::Bool))
            }
            Expr::If(cond, then, els) => {
                self.lower(cond, out)?;
                let mut then_code = Code::new();
                let mut else_code = Code::new();
                let then_ty = self.lower(then, &mut then_code)?;
                let else_ty = self.lower(els, &mut else_code)?;
                let ty = then_ty.or(else_ty);
                let block = match ty.and_then(val_type) {
                    Some(vt) => BlockType::Result(vt),
                    None => BlockType::Empty,
                };
                out.push(Instruction::If(block));
                out.extend(then_code);
                out.push(Instruction::Else);
                out.extend(else_code);
                out.push(Instruction::End);
                if ty.is_none() {
                    out.push(Instruction::Unreachable);
                }
                Ok(ty)
            }
            Expr::CallDirect(f, args) => {
                let callee = self
                    .program
                    .funcs
                    .get(f.0 as usize)
                    .ok_or(EmitError::UnknownFunc(*f))?;
                if callee.params.len() != args.len() {
                    return Err(EmitError::Malformed("call arity"));
                }
                for arg in args {
                    self.lower(arg, out)?;
                }
                out.push(Instruction::Call(IMPORTS + f.0));
                Ok(Some(callee.ret))
            }
            Expr::Trap(_) => {
                out.push(Instruction::Unreachable);
                Ok(None)
            }
            Expr::Switch(..) => Err(EmitError::Unsupported("switch")),
            Expr::CallClosure(..)
            | Expr::TailCall(..)
            | Expr::MakeClosure(..)
            | Expr::Capture(_) => Err(EmitError::Unsupported("closures")),
            Expr::AllocRecord(..)
            | Expr::Field(..)
            | Expr::AllocVariant(..)
            | Expr::Payload(..)
            | Expr::Unpack(..)
            | Expr::ReuseVariant(..)
            | Expr::Free(_)
            | Expr::StrLit(_)
            | Expr::Dup(_)
            | Expr::Drop(_) => Err(EmitError::Unsupported("heap objects")),
        }
    }

    fn operands(&mut self, a: &Expr, b: &Expr, want: MTy, out: &mut Code) -> Result<(), EmitError> {
        for operand in [a, b] {
            if self.lower(operand, out)?.is_some_and(|t| t != want) {
                return Err(EmitError::Malformed("operand type"));
            }
        }
        Ok(())
    }
}
