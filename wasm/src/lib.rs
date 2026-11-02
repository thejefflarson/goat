use std::collections::HashMap;
use std::fmt;

use goat_mir::*;
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, DataSection, ElementSection, Elements, EntityType,
    ExportKind, ExportSection, Function, FunctionSection, GlobalSection, GlobalType, ImportSection,
    Instruction, MemArg, MemArgTarget, MemorySection, MemoryType, Module, RefType, TableSection,
    TableType, TypeSection, ValType,
};

const DATA_BASE: u32 = 8;
const IMPORTS: u32 = 2;
const PRINT_NUMBER: u32 = 0;
const PRINT_BOOL: u32 = 1;
const HEAP_GLOBAL: u32 = 0;
const IMMORTAL: i32 = -1;

/// wasm32 object layout (`docs/mir.md`); every offset below derives from these.
mod layout {
    const POINTER: u32 = 4;
    pub const SLOT: u32 = 8;
    pub const RC: u32 = 0;
    pub const HEADER: u32 = 8;
    pub const DROP_FN: u32 = HEADER;
    pub const CODE: u32 = DROP_FN + POINTER;
    pub const CAPTURES: u32 = (CODE + POINTER).next_multiple_of(SLOT);
    pub const STATIC_CLOSURE: u32 = CAPTURES;

    pub fn slot(base: u32, index: usize) -> u32 {
        base + SLOT * index as u32
    }

    pub fn object_size(base: u32, slots: usize) -> u32 {
        slot(base, slots).next_multiple_of(8)
    }
}

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

    let mut func_types = Vec::new();
    for func in &program.funcs {
        let (params, results) = func_signature(func);
        func_types.push(types.intern(params, results));
    }
    func_types.push(entry_ty);

    let data_len = program.data.concat().len() as u32;
    let static_base = (DATA_BASE + data_len).next_multiple_of(8);
    let helper_base = IMPORTS + program.funcs.len() as u32 + 1;
    let mut shared = Shared {
        program,
        types,
        helpers: Vec::new(),
        helper_base,
        table: Vec::new(),
        statics: Vec::new(),
        static_base,
        indirect: false,
    };

    let mut bodies = Vec::new();
    for func in &program.funcs {
        bodies.push(lower_func(&mut shared, func)?);
    }
    bodies.push(entry_wrapper(program)?);

    let drop_ty = shared.drop_type();
    let mut next_helper = 0;
    while next_helper < shared.helpers.len() {
        let helper = shared.helpers[next_helper];
        bodies.push(helper_body(&mut shared, helper)?);
        func_types.push(drop_ty);
        next_helper += 1;
    }

    let mut data: Vec<u8> = program.data.concat();
    data.resize((static_base - DATA_BASE) as usize, 0);
    if !shared.statics.is_empty() {
        let noop = shared.noop_slot();
        for f in shared.statics.clone() {
            let code = shared.table_slot(IMPORTS + f.0);
            for word in [IMMORTAL as u32, 0, noop, code] {
                data.extend(word.to_le_bytes());
            }
        }
    }
    let heap_start = (DATA_BASE + data.len() as u32).next_multiple_of(8);

    let mut module = Module::new();
    module.section(&shared.types.section());

    let mut imports = ImportSection::new();
    imports.import("goat", "print_number", EntityType::Function(print_number));
    imports.import("goat", "print_bool", EntityType::Function(print_bool));
    module.section(&imports);

    let mut functions = FunctionSection::new();
    for ty in &func_types {
        functions.function(*ty);
    }
    module.section(&functions);

    let table_len = shared.table.len() as u64;
    if shared.indirect || table_len > 0 {
        let mut tables = TableSection::new();
        tables.table(TableType {
            element_type: RefType::FUNCREF,
            table64: false,
            minimum: table_len,
            maximum: Some(table_len),
            shared: false,
        });
        module.section(&tables);
    }

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

    if table_len > 0 {
        let mut elements = ElementSection::new();
        elements.active(
            Some(0),
            &ConstExpr::i32_const(0),
            Elements::Functions(shared.table.clone().into()),
        );
        module.section(&elements);
    }

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

/// A closure body takes its environment as an extra leading `i32` parameter.
fn func_signature(func: &Func) -> (Vec<ValType>, Vec<ValType>) {
    let mut params = Vec::new();
    if func.env.is_some() {
        params.push(ValType::I32);
    }
    params.extend(val_types(func.params.iter().map(|&(_, ty)| ty)));
    (params, val_types([func.ret]))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Helper {
    /// The `drop_fn` of a closure that owns nothing.
    Noop,
    ClosureDrop(FuncId),
    RecordDrop(LayoutId),
}

struct Shared<'a> {
    program: &'a Program,
    types: Types,
    helpers: Vec<Helper>,
    helper_base: u32,
    /// Function indices, in table order.
    table: Vec<u32>,
    statics: Vec<FuncId>,
    static_base: u32,
    indirect: bool,
}

fn intern<T: PartialEq>(items: &mut Vec<T>, item: T) -> usize {
    items.iter().position(|i| *i == item).unwrap_or_else(|| {
        items.push(item);
        items.len() - 1
    })
}

impl Shared<'_> {
    fn helper(&mut self, helper: Helper) -> u32 {
        self.helper_base + intern(&mut self.helpers, helper) as u32
    }

    fn table_slot(&mut self, func_index: u32) -> u32 {
        intern(&mut self.table, func_index) as u32
    }

    fn noop_slot(&mut self) -> u32 {
        let noop = self.helper(Helper::Noop);
        self.table_slot(noop)
    }

    fn static_closure(&mut self, f: FuncId) -> u32 {
        let index = intern(&mut self.statics, f);
        self.helper(Helper::Noop);
        self.static_base + index as u32 * layout::STATIC_CLOSURE
    }

    fn closure_type(&mut self, sig: SigId) -> Result<(u32, MTy), EmitError> {
        let sig = self
            .program
            .sigs
            .get(sig.0 as usize)
            .ok_or(EmitError::Malformed("unknown signature"))?;
        let mut params = vec![ValType::I32];
        params.extend(val_types(sig.params.iter().copied()));
        self.indirect = true;
        Ok((self.types.intern(params, val_types([sig.ret])), sig.ret))
    }

    fn drop_type(&mut self) -> u32 {
        self.types.intern(vec![ValType::I32], vec![])
    }
}

fn helper_body(shared: &mut Shared, helper: Helper) -> Result<Function, EmitError> {
    let slots: Vec<(MTy, u32)> = match helper {
        Helper::Noop => Vec::new(),
        Helper::ClosureDrop(f) => {
            let env = shared.program.funcs[f.0 as usize].env.as_ref();
            let captures = env.map_or(&[][..], |e| &e.captures[..]);
            captures
                .iter()
                .enumerate()
                .map(|(i, &ty)| (ty, layout::slot(layout::CAPTURES, i)))
                .collect()
        }
        Helper::RecordDrop(l) => match shared.program.layouts.get(l.0 as usize) {
            Some(Layout::Record(fields)) => fields
                .iter()
                .enumerate()
                .map(|(i, &ty)| (ty, layout::slot(layout::HEADER, i)))
                .collect(),
            _ => return Err(EmitError::Malformed("record layout")),
        },
    };
    let mut f = Function::new([(1, ValType::I32)]);
    let mut code = Code::new();
    for (ty, offset) in slots {
        if let MTy::Ptr(kind) = ty {
            code.push(Instruction::LocalGet(0));
            code.extend(load(ty, offset));
            code.push(Instruction::LocalSet(1));
            release(shared, 1, kind, &mut code)?;
        }
    }
    for instr in &code {
        f.instruction(instr);
    }
    f.instruction(&Instruction::End);
    Ok(f)
}

fn memarg(offset: u32, align: u32) -> MemArg {
    MemArg {
        offset: offset.into(),
        align,
        target: MemArgTarget::Memory(0),
        ordering: None,
    }
}

fn load(ty: MTy, offset: u32) -> Option<Instruction<'static>> {
    match ty {
        MTy::Float => Some(Instruction::F64Load(memarg(offset, 3))),
        MTy::Unit => None,
        MTy::Int | MTy::Bool | MTy::Ptr(_) => Some(Instruction::I32Load(memarg(offset, 2))),
    }
}

fn store(ty: MTy, offset: u32) -> Option<Instruction<'static>> {
    match ty {
        MTy::Float => Some(Instruction::F64Store(memarg(offset, 3))),
        MTy::Unit => None,
        MTy::Int | MTy::Bool | MTy::Ptr(_) => Some(Instruction::I32Store(memarg(offset, 2))),
    }
}

fn rc_load() -> Instruction<'static> {
    Instruction::I32Load(memarg(layout::RC, 2))
}

fn rc_store() -> Instruction<'static> {
    Instruction::I32Store(memarg(layout::RC, 2))
}

/// Opens an `if` that adds `delta` to the count of the object in wasm local
/// `p`, skipping immortal objects; the caller closes it.
fn adjust_rc(p: u32, delta: Instruction<'static>, out: &mut Code) {
    out.extend([
        Instruction::LocalGet(p),
        rc_load(),
        Instruction::I32Const(IMMORTAL),
        Instruction::I32Ne,
        Instruction::If(BlockType::Empty),
        Instruction::LocalGet(p),
        Instruction::LocalGet(p),
        rc_load(),
        Instruction::I32Const(1),
        delta,
        rc_store(),
    ]);
}

fn retain(p: u32, out: &mut Code) {
    adjust_rc(p, Instruction::I32Add, out);
    out.push(Instruction::End);
}

/// Memory is never reclaimed yet: a count that reaches zero runs the object's
/// drop function, which releases its children.
fn release(shared: &mut Shared, p: u32, kind: HeapKind, out: &mut Code) -> Result<(), EmitError> {
    let dropper = match kind {
        HeapKind::Closure(_) => None,
        HeapKind::Record(l) => Some(shared.helper(Helper::RecordDrop(l))),
        _ => return Err(EmitError::Unsupported("dropping this heap object")),
    };
    adjust_rc(p, Instruction::I32Sub, out);
    out.extend([
        Instruction::LocalGet(p),
        rc_load(),
        Instruction::I32Eqz,
        Instruction::If(BlockType::Empty),
        Instruction::LocalGet(p),
    ]);
    match dropper {
        Some(index) => out.push(Instruction::Call(index)),
        None => {
            let type_index = shared.drop_type();
            shared.indirect = true;
            out.extend([
                Instruction::LocalGet(p),
                Instruction::I32Load(memarg(layout::DROP_FN, 2)),
                Instruction::CallIndirect {
                    type_index,
                    table_index: 0,
                },
            ]);
        }
    }
    out.extend([Instruction::End, Instruction::End]);
    Ok(())
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

fn lower_func(shared: &mut Shared, func: &Func) -> Result<Function, EmitError> {
    let mut cx = FuncCx {
        program: shared.program,
        shared,
        scope: HashMap::new(),
        next_local: 0,
        declared: Vec::new(),
        env: None,
    };
    if let Some(env) = &func.env {
        let index = cx.bind(env.local, MTy::Ptr(HeapKind::Closure(env.sig)));
        cx.env = index.map(|i| (i, env.captures.clone()));
    }
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

struct FuncCx<'a, 'p> {
    program: &'p Program,
    shared: &'a mut Shared<'p>,
    scope: HashMap<Local, (Option<u32>, MTy)>,
    next_local: u32,
    /// Wasm locals beyond the parameters; parameters are declared by the signature.
    declared: Vec<ValType>,
    /// The wasm local holding `env`, and the types of its captures.
    env: Option<(u32, Vec<MTy>)>,
}

type Temps = Option<Vec<Option<u32>>>;

impl FuncCx<'_, '_> {
    fn scratch(&mut self, vt: ValType) -> u32 {
        let index = self.next_local;
        self.next_local += 1;
        self.declared.push(vt);
        index
    }

    fn bind(&mut self, local: Local, ty: MTy) -> Option<u32> {
        let index = val_type(ty).map(|vt| self.scratch(vt));
        self.scope.insert(local, (index, ty));
        index
    }

    fn pointer(&self, local: Local) -> Result<(u32, HeapKind), EmitError> {
        match self.scope.get(&local) {
            Some(&(Some(index), MTy::Ptr(kind))) => Ok((index, kind)),
            Some(_) => Err(EmitError::Malformed("expected a pointer")),
            None => Err(EmitError::UnboundLocal(local)),
        }
    }

    /// Lowers each operand into a wasm local so a later allocation cannot interleave with them.
    fn evaluate(&mut self, exprs: &[Expr], out: &mut Code) -> Result<Temps, EmitError> {
        let mut temps = Vec::new();
        for expr in exprs {
            let Some(ty) = self.lower(expr, out)? else {
                return Ok(None);
            };
            let temp = val_type(ty).map(|vt| self.scratch(vt));
            if let Some(temp) = temp {
                out.push(Instruction::LocalSet(temp));
            }
            temps.push(temp);
        }
        Ok(Some(temps))
    }

    /// Bump-allocates an object with `rc = 1` and returns the local holding it.
    fn allocate(&mut self, size: u32, out: &mut Code) -> u32 {
        let ptr = self.scratch(ValType::I32);
        out.extend([
            Instruction::GlobalGet(HEAP_GLOBAL),
            Instruction::LocalTee(ptr),
            Instruction::I32Const(size as i32),
            Instruction::I32Add,
            Instruction::GlobalSet(HEAP_GLOBAL),
            Instruction::LocalGet(ptr),
            Instruction::I32Const(1),
            rc_store(),
        ]);
        ptr
    }

    fn fill(&self, ptr: u32, slots: &[(MTy, Option<u32>)], base: u32, out: &mut Code) {
        for (i, &(ty, temp)) in slots.iter().enumerate() {
            if let (Some(temp), Some(store)) = (temp, store(ty, layout::slot(base, i))) {
                out.extend([
                    Instruction::LocalGet(ptr),
                    Instruction::LocalGet(temp),
                    store,
                ]);
            }
        }
    }

    /// Loads a slot, leaving a fresh owned reference when it holds a pointer.
    fn load_slot(&mut self, ptr: u32, ty: MTy, offset: u32, out: &mut Code) {
        let Some(load) = load(ty, offset) else {
            return;
        };
        out.extend([Instruction::LocalGet(ptr), load]);
        if ty.is_ptr() {
            let temp = self.scratch(ValType::I32);
            out.push(Instruction::LocalTee(temp));
            retain(temp, out);
        }
    }

    fn make_closure(
        &mut self,
        f: FuncId,
        captures: &[Expr],
        out: &mut Code,
    ) -> Result<Ty, EmitError> {
        let env = self
            .program
            .funcs
            .get(f.0 as usize)
            .ok_or(EmitError::UnknownFunc(f))?
            .env
            .as_ref()
            .ok_or(EmitError::Malformed("closure target has no env"))?;
        if env.captures.len() != captures.len() {
            return Err(EmitError::Malformed("capture count"));
        }
        let ty = MTy::Ptr(HeapKind::Closure(env.sig));
        if captures.is_empty() {
            out.push(Instruction::I32Const(self.shared.static_closure(f) as i32));
            return Ok(Some(ty));
        }
        let Some(temps) = self.evaluate(captures, out)? else {
            return Ok(None);
        };
        let ptr = self.allocate(layout::object_size(layout::CAPTURES, captures.len()), out);
        let drop_fn = if env.captures.iter().any(|c| c.is_ptr()) {
            self.shared.helper(Helper::ClosureDrop(f))
        } else {
            self.shared.helper(Helper::Noop)
        };
        let drop_slot = self.shared.table_slot(drop_fn);
        let code_slot = self.shared.table_slot(IMPORTS + f.0);
        for (offset, slot) in [(layout::DROP_FN, drop_slot), (layout::CODE, code_slot)] {
            out.extend([
                Instruction::LocalGet(ptr),
                Instruction::I32Const(slot as i32),
                Instruction::I32Store(memarg(offset, 2)),
            ]);
        }
        let slots: Vec<_> = env.captures.iter().copied().zip(temps).collect();
        self.fill(ptr, &slots, layout::CAPTURES, out);
        out.push(Instruction::LocalGet(ptr));
        Ok(Some(ty))
    }

    /// Pushes `env`, the arguments, then the code index; returns the callee's wasm type and return type.
    fn closure_call(
        &mut self,
        closure: &Expr,
        args: &[Expr],
        out: &mut Code,
    ) -> Result<Option<(u32, MTy)>, EmitError> {
        let Some(callee) = self.lower(closure, out)? else {
            return Ok(None);
        };
        let MTy::Ptr(HeapKind::Closure(sig)) = callee else {
            return Err(EmitError::Malformed("callee is not a closure"));
        };
        if self
            .program
            .sigs
            .get(sig.0 as usize)
            .map(|s| s.params.len())
            != Some(args.len())
        {
            return Err(EmitError::Malformed("closure call arity"));
        }
        let env = self.scratch(ValType::I32);
        out.extend([Instruction::LocalSet(env), Instruction::LocalGet(env)]);
        for arg in args {
            self.lower(arg, out)?;
        }
        out.extend([
            Instruction::LocalGet(env),
            Instruction::I32Load(memarg(layout::CODE, 2)),
        ]);
        self.shared.closure_type(sig).map(Some)
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
                self.direct_args(*f, args, out)?;
                out.push(Instruction::Call(IMPORTS + f.0));
                Ok(Some(callee.ret))
            }
            Expr::CallClosure(closure, args) => {
                let Some((type_index, ret)) = self.closure_call(closure, args, out)? else {
                    return Ok(None);
                };
                out.push(Instruction::CallIndirect {
                    type_index,
                    table_index: 0,
                });
                Ok(Some(ret))
            }
            Expr::TailCall(Callee::Direct(f), args) => {
                self.direct_args(*f, args, out)?;
                out.push(Instruction::ReturnCall(IMPORTS + f.0));
                Ok(None)
            }
            Expr::TailCall(Callee::Closure(closure), args) => {
                if let Some((type_index, _)) = self.closure_call(closure, args, out)? {
                    out.push(Instruction::ReturnCallIndirect {
                        type_index,
                        table_index: 0,
                    });
                }
                Ok(None)
            }
            Expr::MakeClosure(f, captures) => self.make_closure(*f, captures, out),
            Expr::Capture(i) => {
                let (env, captures) = self
                    .env
                    .clone()
                    .ok_or(EmitError::Malformed("capture outside a closure"))?;
                let ty = *captures
                    .get(*i)
                    .ok_or(EmitError::Malformed("capture index"))?;
                self.load_slot(env, ty, layout::slot(layout::CAPTURES, *i), out);
                Ok(Some(ty))
            }
            Expr::AllocRecord(l, fields) => {
                let Some(Layout::Record(types)) = self.program.layouts.get(l.0 as usize) else {
                    return Err(EmitError::Malformed("record layout"));
                };
                if types.len() != fields.len() {
                    return Err(EmitError::Malformed("record field count"));
                }
                let Some(temps) = self.evaluate(fields, out)? else {
                    return Ok(None);
                };
                let ptr = self.allocate(layout::object_size(layout::HEADER, fields.len()), out);
                let slots: Vec<_> = types.iter().copied().zip(temps).collect();
                self.fill(ptr, &slots, layout::HEADER, out);
                out.push(Instruction::LocalGet(ptr));
                Ok(Some(MTy::Ptr(HeapKind::Record(*l))))
            }
            Expr::Field(x, i) => {
                let (ptr, kind) = self.pointer(*x)?;
                let HeapKind::Record(l) = kind else {
                    return Err(EmitError::Malformed("field of a non-record"));
                };
                let Some(Layout::Record(types)) = self.program.layouts.get(l.0 as usize) else {
                    return Err(EmitError::Malformed("record layout"));
                };
                let ty = *types.get(*i).ok_or(EmitError::Malformed("field index"))?;
                self.load_slot(ptr, ty, layout::slot(layout::HEADER, *i), out);
                Ok(Some(ty))
            }
            Expr::Dup(x) => {
                let (ptr, _) = self.pointer(*x)?;
                retain(ptr, out);
                Ok(Some(MTy::Unit))
            }
            Expr::Drop(x) => {
                let (ptr, kind) = self.pointer(*x)?;
                release(self.shared, ptr, kind, out)?;
                Ok(Some(MTy::Unit))
            }
            Expr::Trap(_) => {
                out.push(Instruction::Unreachable);
                Ok(None)
            }
            Expr::Switch(..) => Err(EmitError::Unsupported("switch")),
            Expr::AllocVariant(..)
            | Expr::Payload(..)
            | Expr::Unpack(..)
            | Expr::ReuseVariant(..)
            | Expr::Free(_)
            | Expr::StrLit(_) => Err(EmitError::Unsupported("heap objects")),
        }
    }

    fn direct_args(&mut self, f: FuncId, args: &[Expr], out: &mut Code) -> Result<(), EmitError> {
        let callee = self
            .program
            .funcs
            .get(f.0 as usize)
            .ok_or(EmitError::UnknownFunc(f))?;
        if callee.params.len() != args.len() || callee.env.is_some() {
            return Err(EmitError::Malformed("call arity"));
        }
        for arg in args {
            self.lower(arg, out)?;
        }
        Ok(())
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
