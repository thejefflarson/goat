use std::collections::HashMap;
use std::fmt;

use goat_mir::*;
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, CustomSection, DataSection, ElementSection, Elements,
    EntityType, ExportKind, ExportSection, Function, FunctionSection, GlobalSection, GlobalType,
    ImportSection, Instruction, MemArg, MemArgTarget, MemorySection, MemoryType, Module, RefType,
    TableSection, TableType, TypeSection, ValType,
};

mod allocator;

use allocator::FreeList;

const DATA_BASE: u32 = 8;
const PAGE_BYTES: u32 = 65536;
const PRINT_NUMBER: u32 = 0;
const PRINT_BOOL: u32 = 1;
const PRINT_STRING: u32 = 2;
/// The imports `Write` needs, after `print_number`, `print_bool` and (for a
/// string root) `print_string`: `write_number`, `write_string`, `write_end`.
const WRITE_IMPORTS: u32 = 3;
const IMMORTAL: i32 = -1;
/// The fuel every function entry spends one unit of, after the heap pointer and
/// the allocator's live count. It is exported as `goat_fuel` so a host can
/// refill it; a call that finds none left traps (ADR 0015).
const FUEL_GLOBAL: u32 = 2;
/// Enough that a run-once program never notices, and the value a host that
/// never refills starts from.
const FUEL_START: i32 = i32::MAX;
/// The global a call into the prelude sets to its site number (1-based, 0 for
/// none), and the custom section that maps each number to a source range. A
/// host reads both when `goat.trap` fires to blame the user's call.
const SITE_GLOBAL: u32 = 3;
const SITES_SECTION: &str = "goat.sites";
/// The module globals that hold an interactive program's `update` and `draw`
/// closures, after the site.
const UPDATE_GLOBAL: u32 = 4;
const DRAW_GLOBAL: u32 = 5;

/// wasm32 object layout (`docs/mir.md`); every offset below derives from these.
mod layout {
    const POINTER: u32 = 4;
    pub const SLOT: u32 = 8;
    pub const RC: u32 = 0;
    pub const CLASS: u32 = 4;
    pub const HEADER: u32 = 8;
    pub const LINK: u32 = HEADER;
    pub const DROP_FN: u32 = HEADER;
    pub const CODE: u32 = DROP_FN + POINTER;
    pub const CAPTURES: u32 = (CODE + POINTER).next_multiple_of(SLOT);
    pub const STATIC_CLOSURE: u32 = CAPTURES;
    pub const STR_LEN: u32 = HEADER;
    pub const STR_BYTES: u32 = STR_LEN + 4;
    pub const TAG: u32 = HEADER;
    pub const PAYLOAD: u32 = (TAG + 4).next_multiple_of(SLOT);

    pub fn slot(base: u32, index: usize) -> u32 {
        base + SLOT * index as u32
    }

    pub fn object_size(base: u32, slots: usize) -> u32 {
        slot(base, slots).next_multiple_of(8)
    }
}

#[cfg(kani)]
mod proofs {
    use super::layout::{HEADER, SLOT, object_size, slot};

    /// Largest slot count for which `object_size(HEADER, n)` fits in a `u32`
    /// after rounding up to 8 bytes.
    const MAX_SLOTS: usize = ((u32::MAX - HEADER) / SLOT) as usize;

    #[kani::proof]
    fn slot_never_overflows() {
        let index: usize = kani::any();
        kani::assume(index <= MAX_SLOTS);
        let offset = slot(HEADER, index);
        assert!(offset >= HEADER);
        assert_eq!(offset % SLOT, 0);
    }

    #[kani::proof]
    fn object_size_is_aligned_and_covers_slots() {
        let slots: usize = kani::any();
        kani::assume(slots <= MAX_SLOTS);
        let size = object_size(HEADER, slots);
        assert_eq!(size % 8, 0);
        assert!(size >= HEADER);
        assert!(size >= slot(HEADER, slots));
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

/// `Int` is i64 and `Float` is f64 on this target (ADR 0017); `Unit` is erased.
fn val_type(ty: MTy) -> Option<ValType> {
    match ty {
        MTy::Bool | MTy::Ptr(_) => Some(ValType::I32),
        MTy::Int => Some(ValType::I64),
        MTy::Float => Some(ValType::F64),
        MTy::Unit => None,
    }
}

fn val_types(tys: impl IntoIterator<Item = MTy>) -> Vec<ValType> {
    tys.into_iter().filter_map(val_type).collect()
}

pub fn emit(program: &Program) -> Result<Vec<u8>, EmitError> {
    let mut uses = Uses::default();
    for func in &program.funcs {
        uses.scan(&func.body);
    }
    let needs_drop = uses.drops || program.interactive.is_some();
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
    let alloc_ty = types.intern(vec![ValType::I32], vec![ValType::I32]);
    let live_ty = types.intern(vec![], vec![ValType::I32]);
    let free_ty = types.intern(vec![ValType::I32], vec![]);
    func_types.extend([alloc_ty, free_ty, live_ty]);
    if needs_drop {
        func_types.push(types.intern(vec![ValType::I32, ValType::I32], vec![]));
    }

    let prints_string = program
        .funcs
        .get(program.entry.0 as usize)
        .is_some_and(|root| root.ret == MTy::Ptr(HeapKind::Str));
    let writes_base = if prints_string { 3 } else { 2 };
    let foreign_base = writes_base + if uses.writes { WRITE_IMPORTS } else { 0 };
    let trap_import = foreign_base + program.foreign.len() as u32;
    let imports = trap_import + !uses.traps.is_empty() as u32;
    let foreign_types: Vec<u32> = program
        .foreign
        .iter()
        .map(|f| {
            let params = val_types(f.params.iter().copied());
            types.intern(params, val_types([f.ret]))
        })
        .collect();

    let mut data = Vec::new();
    let mut strings = Vec::new();
    for bytes in &program.data {
        strings.push(DATA_BASE + data.len() as u32);
        data.extend(string_object(bytes));
    }
    let mut trap_messages = HashMap::new();
    for message in &uses.traps {
        trap_messages.insert(message.clone(), DATA_BASE + data.len() as u32);
        data.extend(string_object(message.as_bytes()));
    }
    let nullary_base = DATA_BASE + data.len() as u32;
    for &tag in &uses.nullary {
        for word in [IMMORTAL as u32, 0, tag, 0] {
            data.extend(word.to_le_bytes());
        }
    }
    let static_base = DATA_BASE + data.len() as u32;
    let runtime_base = imports + program.funcs.len() as u32 + 1;
    let runtime_len = allocator::FUNCTIONS + needs_drop as u32;
    let helper_base = runtime_base + runtime_len;
    let mut shared = Shared {
        program,
        types,
        imports,
        writes_base,
        foreign_base,
        trap_import,
        trap_messages,
        sites: uses.sites,
        strings,
        helpers: Vec::new(),
        helper_base,
        free_fn: runtime_base + 1,
        table: Vec::new(),
        statics: Vec::new(),
        static_base,
        nullary_base,
        nullary: uses.nullary,
        indirect: needs_drop,
        alloc_fn: runtime_base,
        drop_loop_fn: needs_drop.then_some(runtime_base + allocator::FUNCTIONS),
    };

    let mut bodies = Vec::new();
    for func in &program.funcs {
        bodies.push(lower_func(&mut shared, func)?);
    }
    bodies.push(entry_wrapper(program, imports)?);

    let export_bodies = match &program.interactive {
        Some(interactive) => interactive_exports(&mut shared, interactive, imports)?,
        None => Vec::new(),
    };

    let mut next_helper = 0;
    while next_helper < shared.helpers.len() {
        let helper = shared.helpers[next_helper];
        bodies.push(helper_body(&mut shared, helper)?);
        func_types.push(shared.drop_type());
        next_helper += 1;
    }

    let exports_base = runtime_base + runtime_len + shared.helpers.len() as u32;
    if !export_bodies.is_empty() {
        let (one, two) = (vec![ValType::I32], vec![ValType::I32; 2]);
        for (params, results) in [
            (vec![], one.clone()),
            (two, one.clone()),
            (one.clone(), vec![]),
            (one, vec![]),
            (vec![], vec![]),
        ] {
            func_types.push(shared.types.intern(params, results));
        }
        bodies.extend(export_bodies);
    }

    if !shared.statics.is_empty() {
        let noop = shared.noop_slot();
        for f in shared.statics.clone() {
            let code = shared.table_slot(imports + f.0);
            for word in [IMMORTAL as u32, 0, noop, code] {
                data.extend(word.to_le_bytes());
            }
        }
    }
    let free_lists = FreeList {
        table: (DATA_BASE + data.len() as u32).next_multiple_of(8),
    };
    let heap_start = free_lists.table + allocator::TABLE_BYTES;
    let mut runtime = vec![
        free_lists.alloc(),
        free_lists.free(),
        free_lists.live_allocs(),
    ];
    if needs_drop {
        runtime.push(drop_loop(&mut shared));
    }
    let entry_index = program.funcs.len();
    bodies.splice(entry_index + 1..entry_index + 1, runtime);

    let mut module = Module::new();
    module.section(&shared.types.section());

    let mut import_section = ImportSection::new();
    import_section.import("goat", "print_number", EntityType::Function(print_number));
    import_section.import("goat", "print_bool", EntityType::Function(print_bool));
    if prints_string {
        import_section.import("goat", "print_string", EntityType::Function(print_bool));
    }
    if uses.writes {
        import_section.import("goat", "write_number", EntityType::Function(print_number));
        import_section.import("goat", "write_string", EntityType::Function(print_bool));
        import_section.import("goat", "write_end", EntityType::Function(entry_ty));
    }
    for (foreign, ty) in program.foreign.iter().zip(&foreign_types) {
        import_section.import(&foreign.module, &foreign.name, EntityType::Function(*ty));
    }
    if !uses.traps.is_empty() {
        import_section.import("goat", "trap", EntityType::Function(print_bool));
    }
    module.section(&import_section);

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
        minimum: u64::from(heap_start.div_ceil(PAGE_BYTES)).max(1),
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    module.section(&memory);

    let mut globals = GlobalSection::new();
    let closure_globals = if program.interactive.is_some() { 2 } else { 0 };
    for init in [heap_start as i32, 0, FUEL_START, 0]
        .into_iter()
        .chain(std::iter::repeat_n(0, closure_globals))
    {
        globals.global(
            GlobalType {
                val_type: ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(init),
        );
    }
    module.section(&globals);

    let mut exports = ExportSection::new();
    exports.export("memory", ExportKind::Memory, 0);
    if program.interactive.is_none() {
        exports.export(
            "goat_entry",
            ExportKind::Func,
            imports + program.funcs.len() as u32,
        );
    }
    exports.export("goat_fuel", ExportKind::Global, FUEL_GLOBAL);
    exports.export("goat_site", ExportKind::Global, SITE_GLOBAL);
    exports.export("goat_alloc", ExportKind::Func, shared.alloc_fn);
    exports.export("goat_live_allocs", ExportKind::Func, shared.alloc_fn + 2);
    if let Some(interactive) = &program.interactive {
        for (name, index) in INTERACTIVE_EXPORTS.iter().zip(exports_base..) {
            exports.export(name, ExportKind::Func, index);
        }
        for event in &interactive.events {
            let name = format!("goat_event_{}", event.label);
            exports.export(&name, ExportKind::Func, imports + event.func.0);
        }
    }
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

    if !shared.sites.is_empty() {
        let table: Vec<u8> = shared
            .sites
            .iter()
            .flat_map(|&(start, end)| [start as u32, end as u32])
            .flat_map(u32::to_le_bytes)
            .collect();
        module.section(&CustomSection {
            name: SITES_SECTION.into(),
            data: table.into(),
        });
    }

    Ok(module.finish())
}

/// The exports an interactive program adds, in the order `interactive_exports`
/// builds their bodies.
const INTERACTIVE_EXPORTS: [&str; 5] = [
    "goat_setup",
    "goat_update",
    "goat_draw",
    "goat_release_model",
    "goat_shutdown",
];

/// The host-facing functions of an interactive program (ADR 0015). The host
/// owns the model (count 1 from `goat_setup`); `goat_update` consumes it and
/// the event, `goat_draw` keeps the host's reference, and the stored closures
/// stay owned by the module's globals until `goat_shutdown`.
fn interactive_exports(
    shared: &mut Shared,
    interactive: &Interactive,
    imports: u32,
) -> Result<Vec<Function>, EmitError> {
    let program = shared.program;
    let func = |id: FuncId| {
        program
            .funcs
            .get(id.0 as usize)
            .ok_or(EmitError::UnknownFunc(id))
    };
    let kind = |ty: Option<&(Local, MTy)>| match ty {
        Some((_, MTy::Ptr(kind))) => Ok(*kind),
        _ => Err(EmitError::Malformed("interactive entry takes no pointer")),
    };
    let root = func(program.entry)?;
    let (update, draw) = (func(interactive.update)?, func(interactive.draw)?);
    let root_kind = match root.ret {
        MTy::Ptr(kind) => kind,
        _ => return Err(EmitError::Malformed("interactive root is not a record")),
    };
    let (update_kind, model_kind) = (kind(update.params.first())?, kind(update.params.get(1))?);
    let draw_kind = kind(draw.params.first())?;

    let mut setup = Code::new();
    setup.extend([
        Instruction::Call(imports + program.entry.0),
        Instruction::LocalSet(0),
    ]);
    for (slot, local) in [
        (interactive.draw_slot, 1),
        (interactive.init_slot, 2),
        (interactive.update_slot, 3),
    ] {
        setup.extend([
            Instruction::LocalGet(0),
            Instruction::I32Load(memarg(layout::slot(layout::HEADER, slot), 2)),
            Instruction::LocalSet(local),
        ]);
        retain(local, &mut setup);
    }
    release(shared, 0, root_kind, &mut setup)?;
    setup.extend([
        Instruction::LocalGet(1),
        Instruction::GlobalSet(DRAW_GLOBAL),
        Instruction::LocalGet(3),
        Instruction::GlobalSet(UPDATE_GLOBAL),
        Instruction::LocalGet(2),
    ]);

    let mut update_code = Code::new();
    update_code.extend([
        Instruction::GlobalGet(UPDATE_GLOBAL),
        Instruction::LocalSet(2),
    ]);
    retain(2, &mut update_code);
    update_code.extend([
        Instruction::LocalGet(2),
        Instruction::LocalGet(0),
        Instruction::LocalGet(1),
        Instruction::Call(imports + interactive.update.0),
    ]);

    let mut draw_code = Code::new();
    retain(0, &mut draw_code);
    draw_code.extend([
        Instruction::GlobalGet(DRAW_GLOBAL),
        Instruction::LocalSet(1),
    ]);
    retain(1, &mut draw_code);
    draw_code.extend([
        Instruction::LocalGet(1),
        Instruction::LocalGet(0),
        Instruction::Call(imports + interactive.draw.0),
    ]);

    let mut release_code = Code::new();
    release(shared, 0, model_kind, &mut release_code)?;

    let mut shutdown = Code::new();
    for (global, kind) in [(UPDATE_GLOBAL, update_kind), (DRAW_GLOBAL, draw_kind)] {
        shutdown.extend([Instruction::GlobalGet(global), Instruction::LocalSet(0)]);
        release(shared, 0, kind, &mut shutdown)?;
        shutdown.extend([Instruction::I32Const(0), Instruction::GlobalSet(global)]);
    }

    Ok([
        (4, setup),
        (1, update_code),
        (1, draw_code),
        (0, release_code),
        (1, shutdown),
    ]
    .into_iter()
    .map(|(locals, code)| {
        let mut f = Function::new([(locals, ValType::I32)]);
        for instr in &code {
            f.instruction(instr);
        }
        f.instruction(&Instruction::End);
        f
    })
    .collect())
}

/// An immortal string: the count never reaches zero, so it is never freed.
fn string_object(bytes: &[u8]) -> Vec<u8> {
    let start = layout::STR_BYTES as usize;
    let mut object = vec![0; (start + bytes.len()).next_multiple_of(8)];
    let mut put =
        |offset: u32, word: &[u8]| object[offset as usize..][..word.len()].copy_from_slice(word);
    put(layout::RC, &IMMORTAL.to_le_bytes());
    put(layout::STR_LEN, &(bytes.len() as u32).to_le_bytes());
    put(layout::STR_BYTES, bytes);
    object
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
    VariantDrop(LayoutId),
}

struct Shared<'a> {
    program: &'a Program,
    types: Types,
    /// Imported functions precede the program's own in the index space.
    imports: u32,
    /// The index of the first `write_*` import, when the program has any.
    writes_base: u32,
    /// The index of the import for `ForeignId(0)`; the rest follow in order.
    foreign_base: u32,
    /// The index of the `goat.trap` import, when the program can trap.
    trap_import: u32,
    /// Absolute address of the string object holding each trap message.
    trap_messages: HashMap<String, u32>,
    /// The source range of each site, in site-number order.
    sites: Vec<(usize, usize)>,
    /// Absolute address of each `Program.data` string object.
    strings: Vec<u32>,
    helpers: Vec<Helper>,
    helper_base: u32,
    alloc_fn: u32,
    free_fn: u32,
    /// Function indices, in table order.
    table: Vec<u32>,
    statics: Vec<FuncId>,
    static_base: u32,
    /// The tags built without a payload, in the order of their immortal cells
    /// from `nullary_base`.
    nullary_base: u32,
    nullary: Vec<u32>,
    indirect: bool,
    drop_loop_fn: Option<u32>,
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

    fn nullary_cell(&self, tag: u32) -> Result<u32, EmitError> {
        let index = self.nullary.iter().position(|t| *t == tag);
        let index = index.ok_or(EmitError::Malformed("unscanned nullary tag"))?;
        Ok(self.nullary_base + index as u32 * layout::object_size(layout::PAYLOAD, 0))
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

    /// The type of a drop function: `(object, pending) -> pending`.
    fn drop_type(&mut self) -> u32 {
        self.types
            .intern(vec![ValType::I32, ValType::I32], vec![ValType::I32])
    }

    /// The funcref-table slot of the drop function for objects of `kind`; a
    /// closure carries its own, so it has none.
    fn dropper_slot(&mut self, kind: HeapKind) -> Option<u32> {
        let helper = match kind {
            HeapKind::Closure(_) => return None,
            HeapKind::Record(l) => Helper::RecordDrop(l),
            HeapKind::Variant(l) | HeapKind::List(l) => Helper::VariantDrop(l),
            HeapKind::Str => Helper::Noop,
        };
        let function = self.helper(helper);
        Some(self.table_slot(function))
    }
}

/// What the program's code needs the module to carry, found before lowering
/// because it fixes the function and data layout.
#[derive(Default)]
struct Uses {
    /// Some `Drop` exists, so the module needs the `drop_loop` runtime.
    drops: bool,
    /// Some `Write` exists, so the module imports the host's `write_*`.
    writes: bool,
    /// Tags built without a payload, each served by one immortal cell.
    nullary: Vec<u32>,
    /// Each distinct `Trap` message, so the module imports `goat.trap`.
    traps: Vec<String>,
    /// Each distinct `Site` range, numbered from 1 in this order.
    sites: Vec<(usize, usize)>,
}

impl Uses {
    fn scan(&mut self, root: &Expr) {
        root.for_each_node(&mut |e| match e {
            Expr::Drop(_) | Expr::ReuseRecord(..) => self.drops = true,
            Expr::Write(_) => self.writes = true,
            Expr::Trap(message) => self.note_trap(message),
            Expr::BinInt(op, ..) => {
                self.note_trap(INT_OVERFLOW);
                if *op == IntOp::Div {
                    self.note_trap(DIVISION_BY_ZERO);
                }
            }
            Expr::Site(start, end) => self.note_site(*start, *end),
            Expr::AllocVariant(_, tag, fields) if fields.is_empty() => {
                if let Err(at) = self.nullary.binary_search(tag) {
                    self.nullary.insert(at, *tag);
                }
            }
            _ => {}
        });
    }

    #[inline(never)]
    fn note_trap(&mut self, message: &str) {
        intern(&mut self.traps, message.to_string());
    }

    #[inline(never)]
    fn note_site(&mut self, start: usize, end: usize) {
        intern(&mut self.sites, (start, end));
    }
}

/// A drop function releases the references an object holds and returns the
/// pending list: a child whose count reaches zero is pushed rather than
/// dropped, so no drop function recurses. See `drop_loop`.
fn helper_body(shared: &mut Shared, helper: Helper) -> Result<Function, EmitError> {
    let (object, pending) = (0, 1);
    let layout_slots = |tys: &[MTy], base| -> Vec<(MTy, u32)> {
        tys.iter()
            .enumerate()
            .map(|(i, &ty)| (ty, layout::slot(base, i)))
            .collect()
    };
    let mut code = Code::new();
    match helper {
        Helper::Noop => {}
        Helper::ClosureDrop(f) => {
            let env = shared.program.funcs[f.0 as usize].env.as_ref();
            let captures = env.map_or(&[][..], |e| &e.captures[..]);
            for (ty, offset) in layout_slots(captures, layout::CAPTURES) {
                push_child(shared, ty, offset, &mut code)?;
            }
        }
        Helper::RecordDrop(l) => {
            let Some(Layout::Record(fields)) = shared.program.layouts.get(l.0 as usize) else {
                return Err(EmitError::Malformed("record layout"));
            };
            for (ty, offset) in layout_slots(fields, layout::HEADER) {
                push_child(shared, ty, offset, &mut code)?;
            }
        }
        Helper::VariantDrop(l) => {
            let Some(Layout::Variant(tags)) = shared.program.layouts.get(l.0 as usize) else {
                return Err(EmitError::Malformed("variant layout"));
            };
            let mut arms = Vec::new();
            for (&tag, fields) in tags {
                let mut arm = Code::new();
                for (ty, offset) in layout_slots(fields, layout::PAYLOAD) {
                    push_child(shared, ty, offset, &mut arm)?;
                }
                if !arm.is_empty() {
                    arms.push((tag, arm));
                }
            }
            let tag = vec![
                Instruction::LocalGet(object),
                Instruction::I32Load(memarg(layout::TAG, 2)),
            ];
            code.extend(branch_on_tag(tag, arms, Code::new(), BlockType::Empty));
        }
    }
    code.push(Instruction::LocalGet(pending));
    // One scratch local, past the two parameters, holds the child being released.
    let mut f = Function::new([(1, ValType::I32)]);
    for instr in &code {
        f.instruction(instr);
    }
    f.instruction(&Instruction::End);
    Ok(f)
}

/// Release the field of type `ty` at `offset` of the object being dropped
/// (local 0). A pointer whose count reaches zero is pushed on the pending list
/// (local 1) instead of being dropped here: its count word, dead from now on,
/// links to the previous head, and the high bits of its `_pad` word hold the
/// table slot of its own drop function until `drop_loop` pops it.
fn push_child(shared: &mut Shared, ty: MTy, offset: u32, out: &mut Code) -> Result<(), EmitError> {
    use Instruction::*;
    let MTy::Ptr(kind) = ty else {
        return Ok(());
    };
    let (object, pending, child) = (0, 1, 2);
    out.extend([
        LocalGet(object),
        I32Load(memarg(offset, 2)),
        LocalSet(child),
    ]);
    adjust_rc(child, I32Sub, true, out);
    out.extend([
        LocalGet(child),
        rc_load(),
        I32Eqz,
        If(BlockType::Empty),
        LocalGet(child),
        LocalGet(pending),
        rc_store(),
        LocalGet(child),
        LocalGet(child),
        I32Load(memarg(layout::CLASS, 2)),
    ]);
    match shared.dropper_slot(kind) {
        Some(slot) => {
            if slot >= 1 << (32 - DROP_SLOT_SHIFT) {
                return Err(EmitError::Unsupported("more than 2^24 table entries"));
            }
            out.push(I32Const((slot << DROP_SLOT_SHIFT) as i32));
        }
        None => out.extend([
            LocalGet(child),
            I32Load(memarg(layout::DROP_FN, 2)),
            I32Const(DROP_SLOT_SHIFT as i32),
            I32Shl,
        ]),
    }
    out.extend([
        I32Or,
        I32Store(memarg(layout::CLASS, 2)),
        LocalGet(child),
        LocalSet(pending),
        End,
        End,
    ]);
    Ok(())
}

/// `_pad` keeps the allocator's size class in its low `DROP_SLOT_SHIFT` bits.
const DROP_SLOT_SHIFT: u32 = 8;

/// `drop_loop(object: i32, drop_fn: i32)`: tear down an object whose count just
/// reached zero, and everything that dies with it, in constant stack. Each
/// object's drop function pushes its dying children on a list threaded through
/// the dead objects themselves (see `push_child`); this loop frees the object,
/// pops the next, and repeats until the list is empty. Teardown of a
/// million-element chain therefore costs one call frame, not a million.
fn drop_loop(shared: &mut Shared) -> Function {
    use Instruction::*;
    let (object, drop_fn, pending) = (0, 1, 2);
    let drop_type = shared.drop_type();
    let class = memarg(layout::CLASS, 2);
    let mut f = Function::new([(1, ValType::I32)]);
    let code = [
        Block(BlockType::Empty),
        Loop(BlockType::Empty),
        LocalGet(object),
        LocalGet(pending),
        LocalGet(drop_fn),
        CallIndirect {
            type_index: drop_type,
            table_index: 0,
        },
        LocalSet(pending),
        LocalGet(object),
        Call(shared.free_fn),
        LocalGet(pending),
        I32Eqz,
        BrIf(1),
        // Pop: the dead object's count word links to the next one, and is
        // zero again once read, as `free` requires.
        LocalGet(pending),
        LocalSet(object),
        LocalGet(object),
        rc_load(),
        LocalSet(pending),
        LocalGet(object),
        I32Const(0),
        rc_store(),
        LocalGet(object),
        I32Load(class),
        I32Const(DROP_SLOT_SHIFT as i32),
        I32ShrU,
        LocalSet(drop_fn),
        LocalGet(object),
        LocalGet(object),
        I32Load(class),
        I32Const((1 << DROP_SLOT_SHIFT) - 1),
        I32And,
        I32Store(class),
        Br(0),
        End,
        End,
        End,
    ];
    for instr in &code {
        f.instruction(instr);
    }
    f
}

/// `block` leaving the value of `arms[i]`'s code, where `tag` leaves the
/// variant's tag on the stack: a `br_table` over nested blocks, arm `i`
/// outside block `i`. A tag with no arm, or one past the table, runs `default`.
fn branch_on_tag(tag: Code, arms: Vec<(u32, Code)>, default: Code, block: BlockType) -> Code {
    use Instruction::*;
    let n = arms.len() as u32;
    let mut out = vec![Block(block), Block(BlockType::Empty)];
    out.extend((0..n).map(|_| Block(BlockType::Empty)));
    out.extend(tag);
    let width = arms.iter().map(|(tag, _)| tag + 1).max().unwrap_or(0);
    let mut table = vec![n; width as usize];
    for (i, (tag, _)) in arms.iter().enumerate().rev() {
        table[*tag as usize] = i as u32;
    }
    out.push(BrTable(table.into(), n));
    for (i, (_, code)) in arms.into_iter().enumerate() {
        out.push(End);
        out.extend(code);
        out.push(Br(n - i as u32));
    }
    out.push(End);
    out.extend(default);
    out.push(End);
    out
}

pub(crate) fn memarg(offset: u32, align: u32) -> MemArg {
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
        MTy::Int => Some(Instruction::I64Load(memarg(offset, 3))),
        MTy::Unit => None,
        MTy::Bool | MTy::Ptr(_) => Some(Instruction::I32Load(memarg(offset, 2))),
    }
}

fn store(ty: MTy, offset: u32) -> Option<Instruction<'static>> {
    match ty {
        MTy::Float => Some(Instruction::F64Store(memarg(offset, 3))),
        MTy::Int => Some(Instruction::I64Store(memarg(offset, 3))),
        MTy::Unit => None,
        MTy::Bool | MTy::Ptr(_) => Some(Instruction::I32Store(memarg(offset, 2))),
    }
}

pub(crate) fn rc_load() -> Instruction<'static> {
    Instruction::I32Load(memarg(layout::RC, 2))
}

fn rc_store() -> Instruction<'static> {
    Instruction::I32Store(memarg(layout::RC, 2))
}

/// Opens an `if` that adds `delta` to the count of the object in wasm local
/// `p`, skipping immortal objects; the caller closes it. A decrement of a
/// count already at zero traps: only a freed block has `rc == 0`.
fn adjust_rc(p: u32, delta: Instruction<'static>, traps_at_zero: bool, out: &mut Code) {
    out.extend([
        Instruction::LocalGet(p),
        rc_load(),
        Instruction::I32Const(IMMORTAL),
        Instruction::I32Ne,
        Instruction::If(BlockType::Empty),
    ]);
    if traps_at_zero {
        out.extend([
            Instruction::LocalGet(p),
            rc_load(),
            Instruction::I32Eqz,
            Instruction::If(BlockType::Empty),
            Instruction::Unreachable,
            Instruction::End,
        ]);
    }
    out.extend([
        Instruction::LocalGet(p),
        Instruction::LocalGet(p),
        rc_load(),
        Instruction::I32Const(1),
        delta,
        rc_store(),
    ]);
}

fn retain(p: u32, out: &mut Code) {
    adjust_rc(p, Instruction::I32Add, false, out);
    out.push(Instruction::End);
}

/// A count that reaches zero hands the object to `drop_loop`, which releases
/// what it holds and frees it. A count already at zero is a double release and
/// traps.
fn release(shared: &mut Shared, p: u32, kind: HeapKind, out: &mut Code) -> Result<(), EmitError> {
    let drop_loop = shared
        .drop_loop_fn
        .ok_or(EmitError::Malformed("drop without a drop runtime"))?;
    let slot = shared.dropper_slot(kind);
    adjust_rc(p, Instruction::I32Sub, true, out);
    out.extend([
        Instruction::LocalGet(p),
        rc_load(),
        Instruction::I32Eqz,
        Instruction::If(BlockType::Empty),
        Instruction::LocalGet(p),
    ]);
    match slot {
        Some(slot) => out.push(Instruction::I32Const(slot as i32)),
        None => out.extend([
            Instruction::LocalGet(p),
            Instruction::I32Load(memarg(layout::DROP_FN, 2)),
        ]),
    }
    out.extend([
        Instruction::Call(drop_loop),
        Instruction::End,
        Instruction::End,
    ]);
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

/// An `Int` root prints through `print_number`, since both are numbers. The
/// host reads an f64, so an `Int` beyond 2^53 prints as the `Float` nearest it.
fn entry_wrapper(program: &Program, imports: u32) -> Result<Function, EmitError> {
    let root = program
        .funcs
        .get(program.entry.0 as usize)
        .ok_or(EmitError::UnknownFunc(program.entry))?;
    if !root.params.is_empty() {
        return Err(EmitError::Malformed("entry function takes parameters"));
    }
    let mut f = Function::new([]);
    if program.interactive.is_some() {
        f.instruction(&Instruction::End);
        return Ok(f);
    }
    f.instruction(&Instruction::Call(imports + program.entry.0));
    match root.ret {
        MTy::Float => {
            f.instruction(&Instruction::Call(PRINT_NUMBER));
        }
        MTy::Int => {
            f.instruction(&Instruction::F64ConvertI64S);
            f.instruction(&Instruction::Call(PRINT_NUMBER));
        }
        MTy::Bool => {
            f.instruction(&Instruction::Call(PRINT_BOOL));
        }
        MTy::Unit => {}
        MTy::Ptr(HeapKind::Str) => {
            f.instruction(&Instruction::Call(PRINT_STRING));
        }
        MTy::Ptr(_) => return Err(EmitError::Unsupported("heap-valued root")),
    }
    f.instruction(&Instruction::End);
    Ok(f)
}

/// `fuel -= 1; if fuel <= 0 { unreachable }`: a runaway call chain, tail calls
/// included, traps in bounded steps instead of hanging its host.
fn spend_fuel(code: &mut Code) {
    code.extend([
        Instruction::GlobalGet(FUEL_GLOBAL),
        Instruction::I32Const(1),
        Instruction::I32Sub,
        Instruction::GlobalSet(FUEL_GLOBAL),
        Instruction::GlobalGet(FUEL_GLOBAL),
        Instruction::I32Const(0),
        Instruction::I32LeS,
        Instruction::If(BlockType::Empty),
        Instruction::Unreachable,
        Instruction::End,
    ]);
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
    spend_fuel(&mut code);
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

impl<'p> FuncCx<'_, 'p> {
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

    /// Allocates an object with `rc = 1` and returns the local holding it.
    fn allocate(&mut self, size: u32, out: &mut Code) -> u32 {
        let ptr = self.scratch(ValType::I32);
        out.extend([
            Instruction::I32Const(size as i32),
            Instruction::Call(self.shared.alloc_fn),
            Instruction::LocalSet(ptr),
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

    /// Overwrites the record's cell when the count is 1, releasing the fields
    /// it held; otherwise drops this reference (the cell is shared, so the
    /// count cannot reach zero) and allocates.
    fn reuse_record(
        &mut self,
        x: Local,
        l: LayoutId,
        fields: &[Expr],
        out: &mut Code,
    ) -> Result<Ty, EmitError> {
        let Some(Layout::Record(types)) = self.program.layouts.get(l.0 as usize) else {
            return Err(EmitError::Malformed("record layout"));
        };
        if types.len() != fields.len() {
            return Err(EmitError::Malformed("record field count"));
        }
        let (base, kind) = self.pointer(x)?;
        if kind != HeapKind::Record(l) {
            return Err(EmitError::Malformed("reuse of a different layout"));
        }
        let Some(temps) = self.evaluate(fields, out)? else {
            return Ok(None);
        };
        let slots: Vec<_> = types.iter().copied().zip(temps).collect();
        let result = self.scratch(ValType::I32);
        out.extend([
            Instruction::LocalGet(base),
            rc_load(),
            Instruction::I32Const(1),
            Instruction::I32Eq,
            Instruction::If(BlockType::Empty),
        ]);
        let mut olds = Vec::new();
        for (i, &(ty, _)) in slots.iter().enumerate() {
            if let (MTy::Ptr(kind), Some(load)) = (ty, load(ty, layout::slot(layout::HEADER, i))) {
                let old = self.scratch(ValType::I32);
                out.extend([
                    Instruction::LocalGet(base),
                    load,
                    Instruction::LocalSet(old),
                ]);
                olds.push((old, kind));
            }
        }
        self.fill(base, &slots, layout::HEADER, out);
        for (old, kind) in olds {
            release(self.shared, old, kind, out)?;
        }
        out.extend([Instruction::LocalGet(base), Instruction::LocalSet(result)]);
        out.push(Instruction::Else);
        adjust_rc(base, Instruction::I32Sub, true, out);
        out.push(Instruction::End);
        let ptr = self.allocate(layout::object_size(layout::HEADER, fields.len()), out);
        self.fill(ptr, &slots, layout::HEADER, out);
        out.extend([
            Instruction::LocalGet(ptr),
            Instruction::LocalSet(result),
            Instruction::End,
            Instruction::LocalGet(result),
        ]);
        Ok(Some(MTy::Ptr(HeapKind::Record(l))))
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
        let code_slot = self.shared.table_slot(self.shared.imports + f.0);
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
        let mut expr = expr;
        while let Expr::Let(l, rhs, body) = expr {
            let Some(ty) = self.lower(rhs, out)? else {
                return Ok(None);
            };
            if let Some(index) = self.bind(*l, ty) {
                out.push(Instruction::LocalSet(index));
            }
            expr = body;
        }
        match expr {
            Expr::Const(c) => Ok(Some(match *c {
                Const::Int(n) => {
                    out.push(Instruction::I64Const(n));
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
            Expr::Let(..) => unreachable!("the loop above consumed every `Let`"),
            Expr::BinInt(op, a, b) => {
                self.operands(a, b, MTy::Int, out)?;
                self.checked_int(*op, out)?;
                Ok(Some(MTy::Int))
            }
            Expr::IntToFloat(value) => match self.lower(value, out)? {
                Some(MTy::Int) => {
                    out.push(Instruction::F64ConvertI64S);
                    Ok(Some(MTy::Float))
                }
                Some(_) => Err(EmitError::Malformed("conversion of a non-int")),
                None => Ok(None),
            },
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
                    (Some(MTy::Int), CmpOp::Eq) => Instruction::I64Eq,
                    (Some(MTy::Int), CmpOp::Ne) => Instruction::I64Ne,
                    (Some(MTy::Int), CmpOp::Lt) => Instruction::I64LtS,
                    (Some(MTy::Int), CmpOp::Le) => Instruction::I64LeS,
                    (Some(MTy::Int), CmpOp::Gt) => Instruction::I64GtS,
                    (Some(MTy::Int), CmpOp::Ge) => Instruction::I64GeS,
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
                out.push(Instruction::Call(self.shared.imports + f.0));
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
                out.push(Instruction::ReturnCall(self.shared.imports + f.0));
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
            Expr::ReuseRecord(x, l, fields) => self.reuse_record(*x, *l, fields, out),
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
            Expr::Trap(message) => self.trap(message, out),
            Expr::Site(start, end) => self.site(*start, *end, out),
            Expr::Switch(x, arms, default) => {
                let (ptr, kind) = self.pointer(*x)?;
                if !matches!(kind, HeapKind::Variant(_) | HeapKind::List(_)) {
                    return Err(EmitError::Malformed("switch on a non-variant"));
                }
                let mut ty = None;
                let mut lowered = Vec::new();
                for (tag, block) in arms {
                    let mut code = Code::new();
                    ty = ty.or(self.lower(block, &mut code)?);
                    lowered.push((*tag, code));
                }
                let mut default_code = Code::new();
                ty = ty.or(self.lower(default, &mut default_code)?);
                let block = match ty.and_then(val_type) {
                    Some(vt) => BlockType::Result(vt),
                    None => BlockType::Empty,
                };
                let tag = vec![
                    Instruction::LocalGet(ptr),
                    Instruction::I32Load(memarg(layout::TAG, 2)),
                ];
                out.extend(branch_on_tag(tag, lowered, default_code, block));
                if ty.is_none() {
                    out.push(Instruction::Unreachable);
                }
                Ok(ty)
            }
            Expr::AllocVariant(l, tag, fields) => {
                let types = self.payload_types(*l, *tag)?;
                if types.len() != fields.len() {
                    return Err(EmitError::Malformed("variant field count"));
                }
                let result = Some(MTy::Ptr(HeapKind::Variant(*l)));
                if fields.is_empty() {
                    out.push(Instruction::I32Const(self.shared.nullary_cell(*tag)? as i32));
                    return Ok(result);
                }
                let Some(temps) = self.evaluate(fields, out)? else {
                    return Ok(None);
                };
                let ptr = self.allocate(layout::object_size(layout::PAYLOAD, fields.len()), out);
                out.extend([
                    Instruction::LocalGet(ptr),
                    Instruction::I32Const(*tag as i32),
                    Instruction::I32Store(memarg(layout::TAG, 2)),
                ]);
                let slots: Vec<_> = types.iter().copied().zip(temps).collect();
                self.fill(ptr, &slots, layout::PAYLOAD, out);
                out.push(Instruction::LocalGet(ptr));
                Ok(result)
            }
            Expr::Payload(x, tag, i) => {
                let (ptr, kind) = self.pointer(*x)?;
                let (HeapKind::Variant(l) | HeapKind::List(l)) = kind else {
                    return Err(EmitError::Malformed("payload of a non-variant"));
                };
                let ty = *self
                    .payload_types(l, *tag)?
                    .get(*i)
                    .ok_or(EmitError::Malformed("payload index"))?;
                self.load_slot(ptr, ty, layout::slot(layout::PAYLOAD, *i), out);
                Ok(Some(ty))
            }
            Expr::Unpack(..) | Expr::ReuseVariant(..) | Expr::Free(_) => {
                Err(EmitError::Unsupported("in-place variant reuse"))
            }
            Expr::StrLit(d) => {
                out.push(Instruction::I32Const(self.string_address(*d)? as i32));
                Ok(Some(MTy::Ptr(HeapKind::Str)))
            }
            Expr::StrEq(a, b) => {
                let (a, b) = (self.string(*a)?, self.string(*b)?);
                self.string_equal(a, b, out);
                Ok(Some(MTy::Bool))
            }
            Expr::CallForeign(f, args) => self.call_foreign(*f, args, out),
            Expr::Write(write) => {
                let call = match write {
                    Write::Number(value) => {
                        match self.lower(value, out)? {
                            Some(MTy::Float) => {}
                            Some(MTy::Int) => out.push(Instruction::F64ConvertI64S),
                            Some(_) => return Err(EmitError::Malformed("write of a non-number")),
                            None => return Ok(None),
                        }
                        0
                    }
                    Write::Str(x) => {
                        out.push(Instruction::LocalGet(self.string(*x)?));
                        1
                    }
                    Write::Lit(d) => {
                        out.push(Instruction::I32Const(self.string_address(*d)? as i32));
                        1
                    }
                    Write::End => 2,
                };
                out.push(Instruction::Call(self.shared.writes_base + call));
                Ok(Some(MTy::Unit))
            }
        }
    }

    /// `a op b` on the two `i64`s on the stack, trapping where the result does
    /// not fit: wasm's own `i64` arithmetic would wrap, and `i64.div_s` traps
    /// with no message.
    #[inline(never)]
    fn checked_int(&mut self, op: IntOp, out: &mut Code) -> Result<(), EmitError> {
        use Instruction::{
            I32Const, I64Add, I64And, I64Const, I64DivS, I64Eq, I64Eqz, I64LtS, I64Mul, I64Ne,
            I64Sub, I64Xor, LocalGet, LocalSet,
        };
        let (a, b) = (self.scratch(ValType::I64), self.scratch(ValType::I64));
        out.extend([LocalSet(b), LocalSet(a)]);
        match op {
            IntOp::Add | IntOp::Sub => {
                let r = self.scratch(ValType::I64);
                // Add overflows when the sum's sign differs from both
                // operands'; Sub when the operands differ in sign and the
                // result's sign differs from the minuend's.
                let (arithmetic, first, second) = match op {
                    IntOp::Add => (I64Add, (a, r), (b, r)),
                    _ => (I64Sub, (a, b), (a, r)),
                };
                out.extend([
                    LocalGet(a),
                    LocalGet(b),
                    arithmetic,
                    LocalSet(r),
                    LocalGet(first.0),
                    LocalGet(first.1),
                    I64Xor,
                    LocalGet(second.0),
                    LocalGet(second.1),
                    I64Xor,
                    I64And,
                    I64Const(0),
                    I64LtS,
                ]);
                self.trap_if(INT_OVERFLOW, out)?;
                out.push(LocalGet(r));
            }
            IntOp::Mul => {
                // Overflow unless a is 0, or a is -1 and b is not the minimum,
                // or dividing the product by a gives b back.
                let flag = BlockType::Result(ValType::I32);
                out.extend([
                    LocalGet(a),
                    I64Eqz,
                    Instruction::If(flag),
                    I32Const(0),
                    Instruction::Else,
                    LocalGet(a),
                    I64Const(-1),
                    I64Eq,
                    Instruction::If(flag),
                    LocalGet(b),
                    I64Const(i64::MIN),
                    I64Eq,
                    Instruction::Else,
                    LocalGet(a),
                    LocalGet(b),
                    I64Mul,
                    LocalGet(a),
                    I64DivS,
                    LocalGet(b),
                    I64Ne,
                    Instruction::End,
                    Instruction::End,
                ]);
                self.trap_if(INT_OVERFLOW, out)?;
                out.extend([LocalGet(a), LocalGet(b), I64Mul]);
            }
            IntOp::Div => {
                out.extend([LocalGet(b), I64Eqz]);
                self.trap_if(DIVISION_BY_ZERO, out)?;
                out.extend([
                    LocalGet(a),
                    I64Const(i64::MIN),
                    I64Eq,
                    LocalGet(b),
                    I64Const(-1),
                    I64Eq,
                    Instruction::I32And,
                ]);
                self.trap_if(INT_OVERFLOW, out)?;
                out.extend([LocalGet(a), LocalGet(b), I64DivS]);
            }
        }
        Ok(())
    }

    /// Traps with `message` when the `i32` on the stack is nonzero.
    fn trap_if(&mut self, message: &str, out: &mut Code) -> Result<(), EmitError> {
        out.push(Instruction::If(BlockType::Empty));
        self.trap(message, out)?;
        out.push(Instruction::End);
        Ok(())
    }

    #[inline(never)]
    fn trap(&mut self, message: &str, out: &mut Code) -> Result<Ty, EmitError> {
        let address = *self
            .shared
            .trap_messages
            .get(message)
            .ok_or(EmitError::Malformed("trap message not collected"))?;
        out.extend([
            Instruction::I32Const(address as i32),
            Instruction::Call(self.shared.trap_import),
            Instruction::Unreachable,
        ]);
        Ok(None)
    }

    #[inline(never)]
    fn site(&mut self, start: usize, end: usize, out: &mut Code) -> Result<Ty, EmitError> {
        let number = self
            .shared
            .sites
            .iter()
            .position(|&site| site == (start, end))
            .ok_or(EmitError::Malformed("site not collected"))?;
        out.extend([
            Instruction::I32Const(number as i32 + 1),
            Instruction::GlobalSet(SITE_GLOBAL),
        ]);
        Ok(Some(MTy::Unit))
    }

    /// The arguments are borrowed locals, so the host sees each pointer as
    /// it stands and the caller still owns it afterwards. A returned string is
    /// a block the host got from `goat_alloc`, so it arrives with count 1.
    fn call_foreign(
        &mut self,
        f: ForeignId,
        args: &[Local],
        out: &mut Code,
    ) -> Result<Ty, EmitError> {
        let foreign = self
            .program
            .foreign
            .get(f.0 as usize)
            .ok_or(EmitError::Malformed("unknown foreign function"))?;
        if foreign.params.len() != args.len() {
            return Err(EmitError::Malformed("foreign call arity"));
        }
        for (&arg, &want) in args.iter().zip(&foreign.params) {
            let &(index, ty) = self.scope.get(&arg).ok_or(EmitError::UnboundLocal(arg))?;
            if ty != want {
                return Err(EmitError::Malformed("foreign argument type"));
            }
            if let Some(index) = index {
                out.push(Instruction::LocalGet(index));
            }
        }
        out.push(Instruction::Call(self.shared.foreign_base + f.0));
        Ok(Some(foreign.ret))
    }

    fn string_address(&self, data: DataId) -> Result<u32, EmitError> {
        self.shared
            .strings
            .get(data.0 as usize)
            .copied()
            .ok_or(EmitError::Malformed("unknown data"))
    }

    /// The wasm local holding the string `x`.
    fn string(&self, x: Local) -> Result<u32, EmitError> {
        match self.pointer(x)? {
            (index, HeapKind::Str) => Ok(index),
            _ => Err(EmitError::Malformed("expected a string")),
        }
    }

    /// Leaves 1 when the strings in locals `a` and `b` hold the same bytes,
    /// else 0: equal lengths first, then a byte-by-byte loop.
    fn string_equal(&mut self, a: u32, b: u32, out: &mut Code) {
        use Instruction::*;
        let (len, i) = (self.scratch(ValType::I32), self.scratch(ValType::I32));
        let len_at = memarg(layout::STR_LEN, 2);
        let byte_at = memarg(layout::STR_BYTES, 0);
        out.extend([
            LocalGet(a),
            I32Load(len_at),
            LocalTee(len),
            LocalGet(b),
            I32Load(len_at),
            I32Eq,
            If(BlockType::Result(ValType::I32)),
            I32Const(0),
            LocalSet(i),
            Block(BlockType::Result(ValType::I32)),
            Loop(BlockType::Empty),
            LocalGet(i),
            LocalGet(len),
            I32GeU,
            If(BlockType::Empty),
            I32Const(1),
            Br(2),
            End,
            LocalGet(a),
            LocalGet(i),
            I32Add,
            I32Load8U(byte_at),
            LocalGet(b),
            LocalGet(i),
            I32Add,
            I32Load8U(byte_at),
            I32Ne,
            If(BlockType::Empty),
            I32Const(0),
            Br(2),
            End,
            LocalGet(i),
            I32Const(1),
            I32Add,
            LocalSet(i),
            Br(0),
            End,
            Unreachable,
            End,
            Else,
            I32Const(0),
            End,
        ]);
    }

    fn payload_types(&self, layout: LayoutId, tag: u32) -> Result<&'p [MTy], EmitError> {
        match self.program.layouts.get(layout.0 as usize) {
            Some(Layout::Variant(tags)) => tags
                .get(&tag)
                .map(Vec::as_slice)
                .ok_or(EmitError::Malformed("variant tag")),
            _ => Err(EmitError::Malformed("variant layout")),
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
