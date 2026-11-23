//! MIR to textual LLVM IR (ADR 0042). The output names no target triple or
//! data layout, so `clang --target` supplies them, and it uses only syntax
//! LLVM 17 reads (opaque `ptr`). Every function takes the `goat_instance`
//! pointer first. The generated code keeps no global state: the heap, the
//! counters and the current site live in that instance, and the host is a
//! `goat_host` table of function pointers the instance points at.
//!
//! Both structs start with a version and only grow at the end. An export takes
//! `(host, ctx, instance)`, checks that the table and the instance are at least
//! as new as the code, and returns a nonzero status when they are not.
//!
//! Heap values (records, variants, strings) and the allocator, reference
//! counting and drop loop that serve them are in `heap`; closures are in
//! `closures`; host output and foreign calls are in `host_calls`.
//!
//! Every goat function and closure body uses LLVM's `tailcc` convention. A
//! function takes the instance first, then (for a closure body) its
//! environment, then its arguments. Tail calls are in `tail`.
//!
//! The IR never carries `nsw`, `nuw`, fast-math flags or TBAA: arithmetic that
//! can overflow goes through the `llvm.s*.with.overflow` intrinsics and
//! branches to the trap.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Write as _};

use goat_mir::*;

mod closures;
mod frames;
mod heap;
mod heap_nodes;
mod host_calls;
mod interactive;
mod tail;

use heap::{Heap, Runtime};

pub use heap::FREE_LISTS;
pub use tail::{Abi, SPILL_WORDS};

/// The function the program's entry is emitted as.
pub const ENTRY: &str = "goat_entry";

/// The export that runs a run-once program: `(host, ctx, instance) -> status`.
/// It prints the program's value through the table.
pub const MAIN: &str = "goat_main";

/// What `goat_main` returns: `STATUS_OK`, or which struct is too old.
pub const STATUS_OK: i32 = 0;
pub const STATUS_HOST_VERSION: i32 = 1;
pub const STATUS_INSTANCE_VERSION: i32 = 2;

/// The oldest `goat_host` and `goat_instance` this emitter's code runs against.
pub const HOST_VERSION: u32 = 1;
pub const INSTANCE_VERSION: u32 = 3;

/// The call depth the embedded profile allows by default, as the wasm
/// backend's `EmbeddedLimits::default()` does.
pub const DEFAULT_CALL_DEPTH: u32 = 1024;

/// Knobs on the emitted code that do not change what a program means.
#[derive(Clone, Copy, Debug)]
pub struct EmitOptions {
    /// `free` fills a released block with `0xFE`, so a compiler reference-count
    /// bug reads poison instead of stale data. It costs time on every release,
    /// so it defaults to debug builds (which include the test and fuzz
    /// profiles), as the wasm backend's option does. The reference-count checks
    /// that trap on a double release or a write to a freed block are always on.
    pub poison_freed: bool,
    /// Calls that may be waiting on a result at once on the embedded profile
    /// (ADR 0026); a desktop program has no bound and ignores it.
    pub call_depth: u32,
    /// The target's register file and tail-call support, which decide how a
    /// `tailcc` signature passes its arguments.
    pub abi: Abi,
}

impl Default for EmitOptions {
    fn default() -> Self {
        EmitOptions {
            poison_freed: cfg!(debug_assertions),
            call_depth: DEFAULT_CALL_DEPTH,
            abi: Abi::DEFAULT,
        }
    }
}

/// The `goat_host` fields after `version`, in order, each a function pointer
/// whose first argument is the `ctx` the export received. They match the wasm
/// imports one to one: `print_*`, `write_*` and `trap` are the `goat` module,
/// `scene_*` and `turtle_*` the modules of those names (`scene_frame` takes a
/// frame's bytes, `mir/src/frame.rs`, in place of one entry per shape), and
/// `foreign` is any other host function. A string argument is a pointer and a byte length.
pub const HOST_FUNCTIONS: &[&str] = &[
    "print_number",
    "print_bool",
    "print_int",
    "print_string",
    "write_number",
    "write_string",
    "write_end",
    "write_int",
    "trap",
    "scene_begin",
    "scene_end",
    "scene_frame",
    "turtle_forward",
    "turtle_back",
    "turtle_left",
    "turtle_right",
    "turtle_pen_up",
    "turtle_pen_down",
    "turtle_color",
    "foreign",
];

/// The `goat_instance` fields and their LLVM types, in order. `host` and `ctx`
/// are what the last export call received; `site_start` is `u32::MAX` while no
/// site is current. `heap` and `heap_size` are the region the host gives the
/// allocator, 8-byte aligned; `heap_top` is the bump offset into it, `allocs`
/// counts every allocation, and `free` holds the head of each size class's free
/// list. The host starts `heap_top`, `allocs` and `free` at zero.
///
/// An interactive program keeps its stored closures (`update`, `draw`,
/// `sites`) and the last failed refresh's `reason` in the instance, and the
/// frame buffer in `frame`, `frame_len` and `frame_cap`; all start null or
/// zero. `stack_limit` is the lowest address the desktop profile may run its
/// stack down to, or null for no check.
pub const INSTANCE_FIELDS: &[(&str, &str)] = &[
    ("version", "i32"),
    ("live", "i32"),
    ("depth", "i32"),
    ("site_start", "i32"),
    ("site_end", "i32"),
    ("heap", "ptr"),
    ("heap_size", "i64"),
    ("host", "ptr"),
    ("ctx", "ptr"),
    ("spill", "[8 x i64]"),
    ("heap_top", "i64"),
    ("allocs", "i64"),
    ("free", "[55 x ptr]"),
    ("update", "ptr"),
    ("draw", "ptr"),
    ("sites", "ptr"),
    ("reason", "ptr"),
    ("frame", "ptr"),
    ("frame_len", "i32"),
    ("frame_cap", "i32"),
    ("stack_limit", "ptr"),
];

/// The index of `name` among the fields of the `goat_host` type, where
/// `version` is field 0.
fn host_slot(name: &str) -> usize {
    1 + HOST_FUNCTIONS
        .iter()
        .position(|f| *f == name)
        .expect("a goat_host function")
}

fn instance_slot(name: &str) -> usize {
    INSTANCE_FIELDS
        .iter()
        .position(|(f, _)| *f == name)
        .expect("a goat_instance field")
}

fn type_definitions() -> String {
    let fields: Vec<_> = INSTANCE_FIELDS.iter().map(|(_, ty)| *ty).collect();
    let pointers = vec!["ptr"; HOST_FUNCTIONS.len()].join(", ");
    format!(
        "%goat_host = type {{ i32, {pointers} }}\n%goat_instance = type {{ {} }}\n\
         %goat_value = type {{ i32, i64, i64 }}\n",
        fields.join(", ")
    )
}

/// A module whose `goat_layout_probe(ptr out)` stores the size of `goat_host`
/// and the offset of each of its fields, then the same for `goat_instance`, as
/// `i64`s. A host compares them with its own `#[repr(C)]` mirrors.
pub fn layout_probe() -> String {
    let mut out = type_definitions();
    out.push_str("\ndefine void @goat_layout_probe(ptr %out) nounwind {\nentry:\n");
    let mut slot = 0;
    for (ty, fields) in [
        ("%goat_host", HOST_FUNCTIONS.len() + 1),
        ("%goat_instance", INSTANCE_FIELDS.len()),
    ] {
        let mut addresses = vec![format!("getelementptr ({ty}, ptr null, i32 1)")];
        addresses
            .extend((0..fields).map(|i| format!("getelementptr ({ty}, ptr null, i32 0, i32 {i})")));
        for address in addresses {
            let _ = writeln!(
                out,
                "  %p{slot} = getelementptr i64, ptr %out, i32 {slot}\n  \
                 store i64 ptrtoint (ptr {address} to i64), ptr %p{slot}"
            );
            slot += 1;
        }
    }
    out.push_str("  ret void\n}\n");
    out
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EmitError {
    Unsupported(&'static str),
    UnknownFunc(FuncId),
    UnboundLocal(Local),
    Malformed(&'static str),
    /// A resource bound, not a fault in the program: it nests deeper than the
    /// emitter's recursion allows.
    TooComplex,
}

impl fmt::Display for EmitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EmitError::Unsupported(what) => {
                write!(f, "not yet supported by the native backend: {what}")
            }
            EmitError::UnknownFunc(id) => write!(f, "unknown function {}", id.0),
            EmitError::UnboundLocal(l) => write!(f, "unbound local {}", l.0),
            EmitError::Malformed(what) => write!(f, "malformed MIR: {what}"),
            EmitError::TooComplex => write!(f, "program too complex: it nests too deeply"),
        }
    }
}

impl EmitError {
    /// Whether the program hit a resource bound rather than a fault in the compiler.
    pub fn is_resource_limit(&self) -> bool {
        matches!(self, EmitError::TooComplex)
    }
}

impl std::error::Error for EmitError {}

pub fn emit(program: &Program) -> Result<String, EmitError> {
    emit_with_options(program, EmitOptions::default())
}

pub fn emit_with_options(program: &Program, options: EmitOptions) -> Result<String, EmitError> {
    if program.interactive.is_some() && program.profile == Profile::Embedded {
        return Err(EmitError::Unsupported(
            "an interactive program on the embedded profile",
        ));
    }
    let mut module = Module::new(program, options);
    let mut functions = String::new();
    for (index, func) in program.funcs.iter().enumerate() {
        let id = FuncId(index as u32);
        let lowered = match module.plan.group_of(id) {
            Some((group, 0)) => FuncLower::new(&mut module, id, func).lower_group(group)?,
            Some(_) => continue,
            None => FuncLower::new(&mut module, id, func).lower()?,
        };
        functions.push_str(&lowered);
        functions.push('\n');
    }
    functions.push_str(&match &program.interactive {
        Some(interactive) => module.interactive_exports(interactive)?,
        None => module.main_export()?,
    });
    let (definitions, runtime) = module.heap_text()?;
    functions.push_str(&runtime);
    Ok(module.finish(&definitions, &functions))
}

/// A lowered value; `Unit` is erased and has no operand.
#[derive(Clone)]
enum Val {
    Unit,
    Op(MTy, String),
}

impl Val {
    fn ty(&self) -> MTy {
        match self {
            Val::Unit => MTy::Unit,
            Val::Op(ty, _) => *ty,
        }
    }

    fn operand(&self) -> Result<&str, EmitError> {
        match self {
            Val::Op(_, op) => Ok(op),
            Val::Unit => Err(EmitError::Malformed("a unit operand")),
        }
    }
}

/// A `Let`'s binding while its body is lowered: `height` is how many nodes
/// were waiting beneath the `Let`, so the binding ends when that many remain.
struct Scope {
    height: usize,
    local: Local,
    shadowed: Option<Val>,
}

/// How deeply `expr` may nest before the emitter gives up with a diagnostic
/// instead of overflowing the thread's stack. Chains of `Let`s and operators
/// are walked iteratively and do not count.
const MAX_NESTING: usize = 512;

/// `None` is a computation that traps: nothing after it runs.
type Lowered = Option<Val>;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Helper {
    FloorDiv,
    FloorMod,
}

impl Helper {
    fn name(self) -> &'static str {
        match self {
            Helper::FloorDiv => "@goat.float_floor_div",
            Helper::FloorMod => "@goat.float_floor_mod",
        }
    }
}

struct Module<'a> {
    program: &'a Program,
    options: EmitOptions,
    heap: Heap,
    texts: BTreeMap<String, usize>,
    helpers: BTreeSet<Helper>,
    declarations: BTreeSet<String>,
    plan: tail::Plan,
}

impl<'a> Module<'a> {
    fn new(program: &'a Program, options: EmitOptions) -> Self {
        Module {
            program,
            options,
            heap: Heap::default(),
            texts: BTreeMap::new(),
            helpers: BTreeSet::new(),
            declarations: BTreeSet::new(),
            plan: tail::Plan::new(program, program.profile == Profile::Embedded),
        }
    }

    fn narrow(&self) -> bool {
        self.program.profile == Profile::Embedded
    }

    fn int_ty(&self) -> &'static str {
        if self.narrow() { "i32" } else { "i64" }
    }

    fn float_ty(&self) -> &'static str {
        if self.narrow() { "float" } else { "double" }
    }

    fn float_suffix(&self) -> &'static str {
        if self.narrow() { "f32" } else { "f64" }
    }

    /// The LLVM type of a value, `None` for the erased `Unit`.
    fn llty(&self, ty: MTy) -> Result<Option<&'static str>, EmitError> {
        Ok(tail::llvm_type(self.narrow(), ty))
    }

    fn ret_ty(&self, ty: MTy) -> Result<&'static str, EmitError> {
        Ok(self.llty(ty)?.unwrap_or("void"))
    }

    fn func_name(&self, id: FuncId) -> String {
        if id == self.program.entry {
            format!("@{ENTRY}")
        } else {
            format!("@goat_f{}", id.0)
        }
    }

    /// The constant holding `text`, as the index of its `@goat.text.N` and its
    /// length in bytes. Trap messages and foreign names are texts.
    fn text_constant(&mut self, text: &str) -> (usize, usize) {
        let next = self.texts.len();
        let index = *self.texts.entry(text.to_string()).or_insert(next);
        (index, text.len())
    }

    /// Declares `llvm.{name}` and returns its callee name.
    fn intrinsic(&mut self, name: &str, ret: &str, params: &str) -> String {
        let callee = format!("@llvm.{name}");
        self.declarations
            .insert(format!("declare {ret} {callee}({params})\n"));
        callee
    }

    /// `goat_main`: checks the versions, records the host and context in the
    /// instance, runs the entry and prints its value through the table.
    fn main_export(&self) -> Result<String, EmitError> {
        let program = self.program;
        let root = program
            .funcs
            .get(program.entry.0 as usize)
            .ok_or(EmitError::UnknownFunc(program.entry))?;
        if !root.params.is_empty() {
            return Err(EmitError::Malformed("entry function takes parameters"));
        }
        let ret = self.ret_ty(root.ret)?;
        let (host_field, ctx_field) = (instance_slot("host"), instance_slot("ctx"));
        let mut out = format!(
            "define i32 @{MAIN}(ptr %host, ptr %ctx, ptr %inst) nounwind {{\n\
             entry:\n  \
             %host_version = load i32, ptr %host\n  \
             %host_old = icmp ult i32 %host_version, {HOST_VERSION}\n  \
             br i1 %host_old, label %bad_host, label %check_instance\n\
             bad_host:\n  ret i32 {STATUS_HOST_VERSION}\n\
             check_instance:\n  \
             %instance_version = load i32, ptr %inst\n  \
             %instance_old = icmp ult i32 %instance_version, {INSTANCE_VERSION}\n  \
             br i1 %instance_old, label %bad_instance, label %run\n\
             bad_instance:\n  ret i32 {STATUS_INSTANCE_VERSION}\n\
             run:\n  \
             %host_slot = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 {host_field}\n  \
             store ptr %host, ptr %host_slot\n  \
             %ctx_slot = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 {ctx_field}\n  \
             store ptr %ctx, ptr %ctx_slot\n"
        );
        let call = format!("call tailcc {ret} @{ENTRY}(ptr %inst)");
        let (printer, arg) = match root.ret {
            MTy::Ptr(HeapKind::Str) => {
                let (len_at, bytes_at) = (heap::STR_LEN_AT, heap::STR_BYTES_AT);
                let _ = writeln!(
                    out,
                    "  %v = {call}\n  \
                     %len_slot = getelementptr inbounds i8, ptr %v, i64 {len_at}\n  \
                     %len32 = load i32, ptr %len_slot\n  \
                     %len = zext i32 %len32 to i64\n  \
                     %bytes = getelementptr inbounds i8, ptr %v, i64 {bytes_at}"
                );
                ("print_string", "ptr %bytes, i64 %len".to_string())
            }
            MTy::Unit => {
                let _ = writeln!(out, "  {call}");
                ("", String::new())
            }
            MTy::Int if self.narrow() => {
                let _ = writeln!(out, "  %v = {call}\n  %w = sext i32 %v to i64");
                ("print_int", "i64 %w".to_string())
            }
            MTy::Int => {
                let _ = writeln!(out, "  %v = {call}");
                ("print_int", "i64 %v".to_string())
            }
            MTy::Float if self.narrow() => {
                let _ = writeln!(out, "  %v = {call}\n  %w = fpext float %v to double");
                ("print_number", "double %w".to_string())
            }
            MTy::Float => {
                let _ = writeln!(out, "  %v = {call}");
                ("print_number", "double %v".to_string())
            }
            MTy::Bool => {
                let _ = writeln!(out, "  %v = {call}\n  %w = zext i1 %v to i32");
                ("print_bool", "i32 %w".to_string())
            }
            MTy::Ptr(_) => return Err(EmitError::Unsupported("a root that is not a string")),
        };
        if !printer.is_empty() {
            let slot = host_slot(printer);
            let _ = writeln!(
                out,
                "  %print_slot = getelementptr inbounds %goat_host, ptr %host, i32 0, i32 {slot}\n  \
                 %print = load ptr, ptr %print_slot\n  \
                 call void %print(ptr %ctx, {arg}) nounwind"
            );
        }
        out.push_str("  ret i32 0\n}\n");
        Ok(out)
    }

    fn finish(self, definitions: &str, functions: &str) -> String {
        let mut out = String::from("; goat native backend: textual LLVM IR\n\n");
        out.push_str(&type_definitions());
        out.push('\n');
        for declaration in &self.declarations {
            out.push_str(declaration);
        }
        out.push('\n');
        let mut texts: Vec<_> = self.texts.iter().collect();
        texts.sort_by_key(|(_, index)| **index);
        for (text, index) in texts {
            let _ = writeln!(
                out,
                "@goat.text.{index} = private unnamed_addr constant [{} x i8] c\"{}\"",
                text.len(),
                escape_bytes(text.as_bytes())
            );
        }
        out.push('\n');
        out.push_str(definitions);
        for helper in &self.helpers {
            out.push_str(&floored(*helper, self.narrow()));
            out.push('\n');
        }
        out.push_str(functions);
        out
    }
}

fn escape_bytes(bytes: &[u8]) -> String {
    let mut out = String::new();
    for &byte in bytes {
        if byte == b' ' || (byte.is_ascii_graphic() && byte != b'"' && byte != b'\\') {
            out.push(byte as char);
        } else {
            let _ = write!(out, "\\{byte:02X}");
        }
    }
    out
}

/// Python's `x // y` or `x % y` over `Float`, built as CPython's
/// `float_divmod` builds it on `fmod` (`frem` is C's `fmod`). The embedded
/// profile widens to `double` around the call, which is exact, and rounds the
/// result back.
fn floored(helper: Helper, narrow: bool) -> String {
    let quotient = helper == Helper::FloorDiv;
    let name = helper.name();
    let mut out = String::new();
    if narrow {
        let _ = writeln!(
            out,
            "define internal float {name}(float %a, float %b) nounwind {{\n  \
             %x = fpext float %a to double\n  %y = fpext float %b to double\n  \
             %r = call double {name}.f64(double %x, double %y)\n  \
             %t = fptrunc double %r to float\n  ret float %t\n}}\n"
        );
    }
    let suffix = if narrow { ".f64" } else { "" };
    let _ = writeln!(
        out,
        "define internal double {name}{suffix}(double %x, double %y) nounwind {{\nentry:"
    );
    if quotient {
        out.push_str(
            "  %yz = fcmp oeq double %y, 0.0\n  br i1 %yz, label %zero, label %go\n\
             zero:\n  %zq = fdiv double %x, %y\n  ret double %zq\ngo:\n",
        );
    }
    out.push_str(
        "  %m0 = frem double %x, %y\n  %xm = fsub double %x, %m0\n  %d = fdiv double %xm, %y\n  \
         %mnz = fcmp une double %m0, 0.0\n  br i1 %mnz, label %nz, label %z\n\
         nz:\n  %yneg = fcmp olt double %y, 0.0\n  %mneg = fcmp olt double %m0, 0.0\n  \
         %diff = xor i1 %yneg, %mneg\n  %ma = fadd double %m0, %y\n  %da = fsub double %d, 1.0\n  \
         %m1 = select i1 %diff, double %ma, double %m0\n  \
         %d1 = select i1 %diff, double %da, double %d\n  br label %join\n\
         z:\n  %m2 = call double @llvm.copysign.f64(double 0.0, double %y)\n  br label %join\n\
         join:\n  %m = phi double [ %m1, %nz ], [ %m2, %z ]\n  \
         %dd = phi double [ %d1, %nz ], [ %d, %z ]\n  \
         %dnz = fcmp une double %dd, 0.0\n  br i1 %dnz, label %fl, label %fz\n\
         fl:\n  %f0 = call double @llvm.floor.f64(double %dd)\n  %fr = fsub double %dd, %f0\n  \
         %gt = fcmp ogt double %fr, 0.5\n  %fp = fadd double %f0, 1.0\n  \
         %f1 = select i1 %gt, double %fp, double %f0\n  br label %end\n\
         fz:\n  %xy = fdiv double %x, %y\n  \
         %f2 = call double @llvm.copysign.f64(double 0.0, double %xy)\n  br label %end\n\
         end:\n  %q = phi double [ %f1, %fl ], [ %f2, %fz ]\n",
    );
    let _ = writeln!(
        out,
        "  ret double {}\n}}",
        if quotient { "%q" } else { "%m" }
    );
    out
}

struct FuncLower<'m, 'a> {
    module: &'m mut Module<'a>,
    id: FuncId,
    func: &'a Func,
    body: String,
    next: u32,
    block: String,
    locals: BTreeMap<Local, Val>,
    /// `alloca`s, which belong in the entry block so a loop does not grow the
    /// stack.
    allocas: String,
    /// What runs on entry before the body: loads of spilled arguments.
    prologue: String,
    looped: Option<tail::Loop>,
    /// How many `expr` calls are open, bounded by `MAX_NESTING`.
    depth: usize,
}

impl<'m, 'a> FuncLower<'m, 'a> {
    fn new(module: &'m mut Module<'a>, id: FuncId, func: &'a Func) -> Self {
        FuncLower {
            module,
            id,
            func,
            body: String::new(),
            next: 0,
            block: "entry".to_string(),
            locals: BTreeMap::new(),
            allocas: String::new(),
            prologue: String::new(),
            looped: None,
            depth: 0,
        }
    }

    fn line(&mut self, text: String) {
        let _ = writeln!(self.body, "  {text}");
    }

    fn fresh(&mut self) -> String {
        self.next += 1;
        format!("%v{}", self.next)
    }

    fn label(&mut self, hint: &str) -> String {
        self.next += 1;
        format!("{hint}{}", self.next)
    }

    fn start(&mut self, label: &str) {
        let _ = writeln!(self.body, "{label}:");
        self.block = label.to_string();
    }

    fn emit(&mut self, instruction: impl fmt::Display) -> String {
        let name = self.fresh();
        self.line(format!("{name} = {instruction}"));
        name
    }

    /// Branches on `cond` to a block that traps with `message`; emission goes
    /// on in the block taken when `cond` is false.
    fn trap_if(&mut self, cond: &str, message: &str) {
        let (trap, go) = (self.label("trap"), self.label("go"));
        self.line(format!("br i1 {cond}, label %{trap}, label %{go}"));
        self.start(&trap);
        self.trap(message);
        self.start(&go);
    }

    /// The address of `field` in the instance.
    fn instance_field(&mut self, field: &str) -> String {
        let slot = instance_slot(field);
        self.emit(format!(
            "getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 {slot}"
        ))
    }

    fn trap(&mut self, message: &str) {
        let (index, len) = self.module.text_constant(message);
        let (trap, ctx) = self.host_entry("trap");
        self.line(format!(
            "call void {trap}(ptr {ctx}, ptr @goat.text.{index}, i64 {len}) noreturn nounwind"
        ));
        self.line("unreachable".to_string());
    }

    /// Lowers `expr`, failing once nesting passes `MAX_NESTING` so a deep
    /// program is a diagnostic, not a stack overflow.
    fn expr(&mut self, expr: &Expr) -> Result<Lowered, EmitError> {
        if self.depth >= MAX_NESTING {
            return Err(EmitError::TooComplex);
        }
        self.depth += 1;
        let lowered = self.walk(expr);
        self.depth -= 1;
        lowered
    }

    /// Lowers `expr` with an explicit stack of the nodes waiting on an operand,
    /// so a long chain of `Let`s or operators takes no more stack than a short
    /// one (see `Expr::leading_operand`). A `Let`'s binding stays in scope
    /// until its body's value reaches the node below it on the stack.
    fn walk(&mut self, expr: &Expr) -> Result<Lowered, EmitError> {
        let mut waiting = Vec::new();
        let mut scopes: Vec<Scope> = Vec::new();
        let mut node = expr;
        loop {
            while let Some(first) = node.leading_operand() {
                waiting.push(OperandWait::First(node));
                node = first;
            }
            let mut value = self.leaf(node)?;
            loop {
                while scopes
                    .last()
                    .is_some_and(|scope| scope.height >= waiting.len())
                {
                    let scope = scopes.pop().expect("a scope is open");
                    match scope.shadowed {
                        Some(old) => self.locals.insert(scope.local, old),
                        None => self.locals.remove(&scope.local),
                    };
                }
                let Some(wait) = waiting.pop() else {
                    return Ok(value);
                };
                match self.resume(wait, value, waiting.len(), &mut scopes)? {
                    OperandStep::Next(next) => {
                        node = next;
                        break;
                    }
                    OperandStep::Right(wait, next) => {
                        waiting.push(wait);
                        node = next;
                        break;
                    }
                    OperandStep::Done(done) => value = done,
                }
            }
        }
    }

    /// A node `walk` does not step through itself: anything but a `Let` or an
    /// operator.
    fn leaf(&mut self, expr: &Expr) -> Result<Lowered, EmitError> {
        Ok(match expr {
            Expr::Const(c) => Some(self.constant(*c)),
            Expr::Local(l) => Some(
                self.locals
                    .get(l)
                    .cloned()
                    .ok_or(EmitError::UnboundLocal(*l))?,
            ),
            Expr::CallDirect(callee, args) => self.call(*callee, args, false)?,
            Expr::Trap(message) => {
                self.trap(message);
                None
            }
            Expr::Switch(x, arms, default) => self.switch(*x, arms, default)?,
            Expr::TailCall(Callee::Direct(callee), args) => self.call(*callee, args, true)?,
            Expr::TailCall(Callee::Closure(closure), args) => {
                self.call_closure(closure, args, true)?
            }
            Expr::CallClosure(closure, args) => self.call_closure(closure, args, false)?,
            Expr::MakeClosure(f, captures) => self.make_closure(*f, captures)?,
            Expr::Capture(i) => Some(self.capture(*i)?),
            Expr::MethodKey(closure) => self.method_key(*closure)?,
            Expr::Frame(op) => self.frame_op(op)?,
            Expr::CallForeign(f, args) => self.call_foreign(*f, args)?,
            Expr::Write(write) => self.write(write)?,
            Expr::Site(start, end) => {
                let too_long = || EmitError::Unsupported("a source over 4 GiB");
                let start = u32::try_from(*start).map_err(|_| too_long())?;
                let end = u32::try_from(*end).map_err(|_| too_long())?;
                for (field, value) in [("site_start", start), ("site_end", end)] {
                    let slot = self.instance_field(field);
                    self.line(format!("store i32 {value}, ptr {slot}"));
                }
                Some(Val::Unit)
            }
            _ => return self.heap_expr(expr),
        })
    }

    /// What the node `wait` does once its operand has `value`; `height` is the
    /// number of nodes still waiting below it.
    fn resume<'e>(
        &mut self,
        wait: OperandWait<'e, Lowered>,
        value: Lowered,
        height: usize,
        scopes: &mut Vec<Scope>,
    ) -> Result<OperandStep<'e, Lowered>, EmitError> {
        let Some(value) = value else {
            return Ok(OperandStep::Done(None));
        };
        let first_operand = |first: Lowered| first.ok_or(EmitError::Malformed("a missing operand"));
        Ok(match wait {
            OperandWait::First(Expr::Let(local, _, body)) => {
                let shadowed = self.locals.insert(*local, value);
                scopes.push(Scope {
                    height,
                    local: *local,
                    shadowed,
                });
                OperandStep::Next(body)
            }
            OperandWait::First(Expr::If(_, then, els)) => {
                OperandStep::Done(self.branch(value, then, els)?)
            }
            OperandWait::First(node @ Expr::BinInt(_, _, right)) => {
                expect(&value, MTy::Int)?;
                OperandStep::Right(OperandWait::Second(node, Some(value)), right)
            }
            OperandWait::First(node @ Expr::BinFloat(_, _, right)) => {
                expect(&value, MTy::Float)?;
                OperandStep::Right(OperandWait::Second(node, Some(value)), right)
            }
            OperandWait::First(node @ Expr::Cmp(_, _, right)) => {
                OperandStep::Right(OperandWait::Second(node, Some(value)), right)
            }
            OperandWait::First(Expr::IntToFloat(_)) => {
                expect(&value, MTy::Int)?;
                let operand = value.operand()?;
                let (int, float) = (self.module.int_ty(), self.module.float_ty());
                OperandStep::Done(Some(Val::Op(
                    MTy::Float,
                    self.emit(format!("sitofp {int} {operand} to {float}")),
                )))
            }
            OperandWait::First(Expr::FloatFn(function, _)) => {
                expect(&value, MTy::Float)?;
                OperandStep::Done(Some(self.float_fn(*function, value.operand()?)))
            }
            OperandWait::First(_) => return Err(EmitError::Malformed("not an operator")),
            OperandWait::Second(Expr::BinInt(op, ..), first) => {
                let first = first_operand(first)?;
                expect(&value, MTy::Int)?;
                OperandStep::Done(Some(self.int_op(*op, first.operand()?, value.operand()?)))
            }
            OperandWait::Second(Expr::BinFloat(op, ..), first) => {
                let first = first_operand(first)?;
                expect(&value, MTy::Float)?;
                OperandStep::Done(Some(self.float_op(*op, first.operand()?, value.operand()?)))
            }
            OperandWait::Second(Expr::Cmp(op, ..), first) => {
                let first = first_operand(first)?;
                OperandStep::Done(Some(self.compare(*op, &first, &value)?))
            }
            OperandWait::Second(..) => return Err(EmitError::Malformed("not a binary operator")),
        })
    }

    fn constant(&self, c: Const) -> Val {
        match c {
            Const::Int(n) => Val::Op(MTy::Int, n.to_string()),
            Const::Float(x) => {
                let rounded = self.module.program.profile.round_float(x);
                Val::Op(MTy::Float, hex_float(rounded))
            }
            Const::Bool(b) => Val::Op(MTy::Bool, b.to_string()),
            Const::Unit => Val::Unit,
        }
    }

    fn int_op(&mut self, op: IntOp, a: &str, b: &str) -> Val {
        let t = self.module.int_ty();
        let value = match op {
            IntOp::Add | IntOp::Sub | IntOp::Mul => {
                let name = match op {
                    IntOp::Add => "sadd",
                    IntOp::Sub => "ssub",
                    _ => "smul",
                };
                let pair_ty = format!("{{ {t}, i1 }}");
                let intrinsic = self.module.intrinsic(
                    &format!("{name}.with.overflow.{t}"),
                    &pair_ty,
                    &format!("{t}, {t}"),
                );
                let pair = self.emit(format!("call {pair_ty} {intrinsic}({t} {a}, {t} {b})"));
                let flag = self.emit(format!("extractvalue {pair_ty} {pair}, 1"));
                self.trap_if(&flag, INT_OVERFLOW);
                self.emit(format!("extractvalue {pair_ty} {pair}, 0"))
            }
            IntOp::Div | IntOp::FloorDiv | IntOp::Mod => self.divide(op, a, b),
        };
        Val::Op(MTy::Int, value)
    }

    /// `a op b` for `Div`, `FloorDiv` and `Mod`, trapping on a zero divisor and
    /// on the one quotient that does not fit. Both checks come before the
    /// division, which is undefined behavior in LLVM for either case.
    fn divide(&mut self, op: IntOp, a: &str, b: &str) -> String {
        let t = self.module.int_ty();
        let zero = self.emit(format!("icmp eq {t} {b}, 0"));
        self.trap_if(&zero, DIVISION_BY_ZERO);
        let divisor = if op == IntOp::Mod {
            // `srem MIN, -1` is undefined in LLVM and 0 in goat; a remainder
            // by -1 is 0, and so is a remainder by 1.
            let minus_one = self.emit(format!("icmp eq {t} {b}, -1"));
            self.emit(format!("select i1 {minus_one}, {t} 1, {t} {b}"))
        } else {
            let min = if self.module.narrow() {
                i64::from(i32::MIN)
            } else {
                i64::MIN
            };
            let is_min = self.emit(format!("icmp eq {t} {a}, {min}"));
            let minus_one = self.emit(format!("icmp eq {t} {b}, -1"));
            let both = self.emit(format!("and i1 {is_min}, {minus_one}"));
            self.trap_if(&both, INT_OVERFLOW);
            b.to_string()
        };
        if op == IntOp::Div {
            return self.emit(format!("sdiv {t} {a}, {divisor}"));
        }
        let r = self.emit(format!("srem {t} {a}, {divisor}"));
        let nonzero = self.emit(format!("icmp ne {t} {r}, 0"));
        let signs = self.emit(format!("xor {t} {r}, {b}"));
        let differ = self.emit(format!("icmp slt {t} {signs}, 0"));
        let rounds_down = self.emit(format!("and i1 {nonzero}, {differ}"));
        if op == IntOp::FloorDiv {
            let q = self.emit(format!("sdiv {t} {a}, {divisor}"));
            let below = self.emit(format!("sub {t} {q}, 1"));
            self.emit(format!("select i1 {rounds_down}, {t} {below}, {t} {q}"))
        } else {
            let shifted = self.emit(format!("add {t} {r}, {b}"));
            self.emit(format!("select i1 {rounds_down}, {t} {shifted}, {t} {r}"))
        }
    }

    fn float_op(&mut self, op: FloatOp, a: &str, b: &str) -> Val {
        let t = self.module.float_ty();
        let instruction = match op {
            FloatOp::Add => "fadd",
            FloatOp::Sub => "fsub",
            FloatOp::Mul => "fmul",
            FloatOp::Div => "fdiv",
            FloatOp::FloorDiv | FloatOp::Mod => {
                let helper = if op == FloatOp::FloorDiv {
                    Helper::FloorDiv
                } else {
                    Helper::FloorMod
                };
                self.module.helpers.insert(helper);
                self.module
                    .intrinsic("copysign.f64", "double", "double, double");
                self.module.intrinsic("floor.f64", "double", "double");
                let name = helper.name();
                return Val::Op(
                    MTy::Float,
                    self.emit(format!("call {t} {name}({t} {a}, {t} {b})")),
                );
            }
        };
        Val::Op(MTy::Float, self.emit(format!("{instruction} {t} {a}, {b}")))
    }

    fn compare(&mut self, op: CmpOp, a: &Val, b: &Val) -> Result<Val, EmitError> {
        if a.ty() != b.ty() {
            return Err(EmitError::Malformed("comparison operand types differ"));
        }
        let (kind, t, predicate) = match a.ty() {
            MTy::Int => (
                "icmp",
                self.module.int_ty(),
                match op {
                    CmpOp::Eq => "eq",
                    CmpOp::Ne => "ne",
                    CmpOp::Lt => "slt",
                    CmpOp::Le => "sle",
                    CmpOp::Gt => "sgt",
                    CmpOp::Ge => "sge",
                },
            ),
            // Ordered, except `!=`: a NaN is unequal to everything.
            MTy::Float => (
                "fcmp",
                self.module.float_ty(),
                match op {
                    CmpOp::Eq => "oeq",
                    CmpOp::Ne => "une",
                    CmpOp::Lt => "olt",
                    CmpOp::Le => "ole",
                    CmpOp::Gt => "ogt",
                    CmpOp::Ge => "oge",
                },
            ),
            _ => return Err(EmitError::Malformed("comparison operands")),
        };
        let (x, y) = (a.operand()?, b.operand()?);
        Ok(Val::Op(
            MTy::Bool,
            self.emit(format!("{kind} {predicate} {t} {x}, {y}")),
        ))
    }

    fn float_fn(&mut self, function: FloatFn, a: &str) -> Val {
        let (t, suffix) = (self.module.float_ty(), self.module.float_suffix());
        match function {
            FloatFn::Sqrt => {
                let sqrt = self.module.intrinsic(&format!("sqrt.{suffix}"), t, t);
                Val::Op(MTy::Float, self.emit(format!("call {t} {sqrt}({t} {a})")))
            }
            FloatFn::Truncate => {
                let trunc = self.module.intrinsic(&format!("trunc.{suffix}"), t, t);
                let whole = self.emit(format!("call {t} {trunc}({t} {a})"));
                let bits = if self.module.narrow() { 31 } else { 63 };
                let low = hex_float(-(2.0_f64.powi(bits)));
                let high = hex_float(2.0_f64.powi(bits));
                // Ordered compares are false for NaN, which does not fit either.
                let above = self.emit(format!("fcmp oge {t} {whole}, {low}"));
                let below = self.emit(format!("fcmp olt {t} {whole}, {high}"));
                let fits = self.emit(format!("and i1 {above}, {below}"));
                let overflow = self.emit(format!("xor i1 {fits}, true"));
                self.trap_if(&overflow, NOT_A_WHOLE_NUMBER);
                let int = self.module.int_ty();
                Val::Op(MTy::Int, self.emit(format!("fptosi {t} {whole} to {int}")))
            }
        }
    }

    fn branch(&mut self, cond: Val, then: &Expr, els: &Expr) -> Result<Lowered, EmitError> {
        expect(&cond, MTy::Bool)?;
        let cond = cond.operand()?.to_string();
        let (then_label, else_label, join) =
            (self.label("then"), self.label("else"), self.label("join"));
        self.line(format!(
            "br i1 {cond}, label %{then_label}, label %{else_label}"
        ));
        let mut arms = Vec::new();
        for (label, arm) in [(then_label, then), (else_label, els)] {
            self.start(&label);
            if let Some(value) = self.expr(arm)? {
                let from = self.block.clone();
                self.line(format!("br label %{join}"));
                arms.push((value, from));
            }
        }
        self.join(arms, join)
    }

    /// Continues in `join`, where `arms` (each a value and the block it ends
    /// in) come together; `None` when every arm traps.
    fn join(&mut self, arms: Vec<(Val, String)>, join: String) -> Result<Lowered, EmitError> {
        let Some((first, _)) = arms.first() else {
            return Ok(None);
        };
        let ty = first.ty();
        if arms.iter().any(|(v, _)| v.ty() != ty) {
            return Err(EmitError::Malformed("if branches differ in type"));
        }
        self.start(&join);
        let Some(llty) = self.module.llty(ty)? else {
            return Ok(Some(Val::Unit));
        };
        let incoming = arms
            .iter()
            .map(|(v, from)| Ok(format!("[ {}, %{from} ]", v.operand()?)))
            .collect::<Result<Vec<_>, EmitError>>()?
            .join(", ");
        Ok(Some(Val::Op(
            ty,
            self.emit(format!("phi {llty} {incoming}")),
        )))
    }

    /// Traps when the stack pointer is below the instance's `stack_limit`,
    /// which the host derives from the goat thread's stack. A null limit is
    /// address 0, which nothing is below.
    fn check_stack(&mut self) {
        let frame = self
            .module
            .intrinsic("frameaddress.p0", "ptr", "i32 immarg");
        let here = self.emit(format!("call ptr {frame}(i32 0)"));
        let here = self.emit(format!("ptrtoint ptr {here} to i64"));
        let limit = self.instance_field("stack_limit");
        let limit = self.emit(format!("load ptr, ptr {limit}"));
        let limit = self.emit(format!("ptrtoint ptr {limit} to i64"));
        let over = self.emit(format!("icmp ult i64 {here}, {limit}"));
        self.trap_if(&over, STACK_OVERFLOW);
    }

    /// Emits `call`, which waits on a result and returns `ret`. On the
    /// embedded profile it also counts the call in the instance's `depth` and
    /// traps past the bound, as the wasm backend does (ADR 0026); the desktop
    /// profile checks the stack pointer instead.
    fn bound_call(&mut self, call: String, ret: MTy) -> Val {
        if !self.module.narrow() {
            self.check_stack();
        }
        let depth = self.module.narrow().then(|| self.instance_field("depth"));
        if let Some(depth) = &depth {
            let before = self.emit(format!("load i32, ptr {depth}"));
            let waiting = self.emit(format!("add i32 {before}, 1"));
            self.line(format!("store i32 {waiting}, ptr {depth}"));
            let limit = self.module.options.call_depth;
            let over = self.emit(format!("icmp ugt i32 {waiting}, {limit}"));
            self.trap_if(&over, STACK_OVERFLOW);
        }
        let result = if ret == MTy::Unit {
            self.line(call);
            Val::Unit
        } else {
            Val::Op(ret, self.emit(call))
        };
        if let Some(depth) = depth {
            let waiting = self.emit(format!("load i32, ptr {depth}"));
            let after = self.emit(format!("sub i32 {waiting}, 1"));
            self.line(format!("store i32 {after}, ptr {depth}"));
        }
        result
    }
}

/// LLVM reads a floating constant written as the hex of its `double` bits, and
/// accepts it for a `float` when the value is exactly representable.
fn hex_float(x: f64) -> String {
    format!("0x{:016X}", x.to_bits())
}

fn expect(value: &Val, ty: MTy) -> Result<(), EmitError> {
    if value.ty() == ty {
        Ok(())
    } else {
        Err(EmitError::Malformed("operand type"))
    }
}
