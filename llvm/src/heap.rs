//! Heap values on the native backend: object layouts, the generated allocator,
//! reference counting and the iterative drop loop. It follows
//! `wasm/src/allocator.rs` and ADR 0002 step for step, so both backends make
//! the same allocations and fail the same checks.
//!
//! Every object has a `{ rc: u32, pad: u32 }` header and 8-byte slots, whatever
//! the target's pointer or number width, so a layout's size depends only on its
//! slot count (ADR 0010). A record is `[header][slot...]`; a variant is
//! `[header][tag: u32][pad: u32][slot...]`; a string is
//! `[header][len: u32][bytes...]`; a closure is
//! `[header][drop id: u32][pad: u32][code: i64][capture slot...]`. A pointer
//! slot holds the address as an `i64`, and a closure's code word is its
//! function's address, which `ptrtoint` makes the same width on every target.
//! A closure carries its own drop id because its type names a signature, not
//! the captures that decide what dies with it.
//!
//! The allocator keeps its state in the `goat_instance`: the bump offset, the
//! free-list heads and the live and total allocation counts. A free block has
//! `rc == 0` and its link in the first payload word. A block's size class sits
//! in the low byte of `pad`. While a dying object waits on the drop loop's
//! pending list, its `rc` word holds the list link (a heap offset divided by 8)
//! and the high 24 bits of `pad` hold its drop function's id.

use super::*;

pub(crate) const RECORD_BASE: usize = 2;
pub(crate) const VARIANT_BASE: usize = 4;
pub(crate) const TAG_AT: u32 = 8;
pub(crate) const STR_LEN_AT: u32 = 8;
pub(crate) const STR_BYTES_AT: u32 = 12;
pub(crate) const CLOSURE_DROP_AT: u32 = 8;
pub(crate) const CLOSURE_CODE_AT: u32 = 16;
pub(crate) const CLOSURE_BASE: usize = 5;
const LINK_AT: u32 = 8;
const IMMORTAL: i32 = -1;
const POISON: i32 = -2;
const MAX_REQUEST: u32 = 1 << 30;
const SMALL_MAX: u32 = 256;
const SMALL_CLASSES: u32 = SMALL_MAX / 8;
const LARGE_BASE: u32 = 24;
/// The number of size classes: `[0, SMALL_CLASSES]` by 8 bytes, then one per
/// power of two up to `MAX_REQUEST`.
pub const FREE_LISTS: usize = (LARGE_BASE + 30 + 1) as usize;
const DROP_ID_SHIFT: u32 = 8;

const DOUBLE_RELEASE: &str = "a heap block was released twice";
const STALE_WRITE: &str = "a freed heap block was written to";

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Runtime {
    ClassBytes,
    Alloc,
    Free,
    DropLoop,
    Retain,
    Release,
    StrEq,
    StrChars,
    StrCopy,
    StrChar,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum DropKind {
    Record(LayoutId),
    Variant(LayoutId),
    Closure(FuncId),
}

#[derive(Default)]
pub(crate) struct Heap {
    types: BTreeMap<String, String>,
    statics: Vec<String>,
    interned: BTreeMap<String, String>,
    /// The kinds that have a drop function, in id order from 1; id 0 is an
    /// object that holds no references.
    drops: Vec<DropKind>,
    runtime: BTreeSet<Runtime>,
}

impl Runtime {
    fn name(self) -> &'static str {
        match self {
            Runtime::ClassBytes => "@goat.class_bytes",
            Runtime::Alloc => "@goat.alloc",
            Runtime::Free => "@goat.free",
            Runtime::DropLoop => "@goat.drop_loop",
            Runtime::Retain => "@goat.retain",
            Runtime::Release => "@goat.release",
            Runtime::StrEq => "@goat.str_eq",
            Runtime::StrChars => "@goat.str_chars",
            Runtime::StrCopy => "@goat.str_copy",
            Runtime::StrChar => "@goat.str_char",
        }
    }

    fn needs(self) -> &'static [Runtime] {
        match self {
            Runtime::Alloc => &[Runtime::ClassBytes],
            Runtime::Free => &[Runtime::ClassBytes],
            Runtime::DropLoop => &[Runtime::Free],
            Runtime::Release => &[Runtime::DropLoop],
            Runtime::StrCopy => &[Runtime::Alloc],
            Runtime::StrChar => &[Runtime::StrCopy],
            _ => &[],
        }
    }
}

/// The LLVM types of one 8-byte slot of type `ty`.
fn slot_fields(narrow: bool, ty: MTy) -> &'static [&'static str] {
    match (ty, narrow) {
        (MTy::Int, false) => &["i64"],
        (MTy::Int, true) => &["i32", "i32"],
        (MTy::Float, false) => &["double"],
        (MTy::Float, true) => &["float", "i32"],
        (MTy::Bool, _) => &["i32", "i32"],
        (MTy::Unit | MTy::Ptr(_), _) => &["i64"],
    }
}

/// The index, in a struct whose slots start at field `base`, of the field that
/// holds slot `i`.
pub(crate) fn field_index(narrow: bool, base: usize, tys: &[MTy], i: usize) -> usize {
    base + tys[..i]
        .iter()
        .map(|ty| slot_fields(narrow, *ty).len())
        .sum::<usize>()
}

/// The byte size of `ty`, as a constant `i32`.
pub(crate) fn size_of(ty: &str) -> String {
    format!("ptrtoint (ptr getelementptr ({ty}, ptr null, i32 1) to i32)")
}

fn holds_references(tys: &[MTy]) -> bool {
    tys.iter().any(|ty| ty.is_ptr())
}

impl<'a> Module<'a> {
    pub(crate) fn need(&mut self, runtime: Runtime) -> &'static str {
        self.heap.runtime.insert(runtime);
        runtime.name()
    }

    fn type_name(&mut self, name: String, base: &[&str], tys: &[MTy]) -> String {
        let narrow = self.narrow();
        let fields: Vec<_> = base
            .iter()
            .copied()
            .chain(tys.iter().flat_map(|ty| slot_fields(narrow, *ty)).copied())
            .collect();
        self.heap
            .types
            .insert(name.clone(), format!("{{ {} }}", fields.join(", ")));
        format!("%{name}")
    }

    /// The struct type of a record layout and its field types.
    pub(crate) fn record_layout(&mut self, l: LayoutId) -> Result<(String, &'a [MTy]), EmitError> {
        match self.program.layouts.get(l.0 as usize) {
            Some(Layout::Record(tys)) => Ok((
                self.type_name(format!("goat.r{}", l.0), &["i32", "i32"], tys),
                tys,
            )),
            _ => Err(EmitError::Malformed("record layout")),
        }
    }

    /// The struct type of the cells of `tag` in a variant layout, and the
    /// types of its payload.
    pub(crate) fn variant_layout(
        &mut self,
        l: LayoutId,
        tag: u32,
    ) -> Result<(String, &'a [MTy]), EmitError> {
        match self.program.layouts.get(l.0 as usize) {
            Some(Layout::Variant(tags)) => {
                let tys = tags
                    .get(&tag)
                    .ok_or(EmitError::Malformed("variant tag"))?
                    .as_slice();
                let name = format!("goat.v{}.t{tag}", l.0);
                Ok((
                    self.type_name(name, &["i32", "i32", "i32", "i32"], tys),
                    tys,
                ))
            }
            _ => Err(EmitError::Malformed("variant layout")),
        }
    }

    /// The id of the drop function for objects of `kind`, 0 when they hold no
    /// references.
    pub(crate) fn drop_id(&mut self, kind: HeapKind) -> Result<u32, EmitError> {
        let (drop, holds) = match kind {
            HeapKind::Str => return Ok(0),
            HeapKind::Closure(_) => {
                return Err(EmitError::Malformed("a closure holds its own drop id"));
            }
            HeapKind::Record(l) => match self.program.layouts.get(l.0 as usize) {
                Some(Layout::Record(tys)) => (DropKind::Record(l), holds_references(tys)),
                _ => return Err(EmitError::Malformed("record layout")),
            },
            HeapKind::Variant(l) | HeapKind::List(l) => {
                match self.program.layouts.get(l.0 as usize) {
                    Some(Layout::Variant(tags)) => (
                        DropKind::Variant(l),
                        tags.values().any(|tys| holds_references(tys)),
                    ),
                    _ => return Err(EmitError::Malformed("variant layout")),
                }
            }
        };
        if !holds {
            return Ok(0);
        }
        Ok(self.drop_id_of(drop))
    }

    fn drop_id_of(&mut self, drop: DropKind) -> u32 {
        let index = self.heap.drops.iter().position(|d| *d == drop);
        let index = index.unwrap_or_else(|| {
            self.heap.drops.push(drop);
            self.heap.drops.len() - 1
        });
        index as u32 + 1
    }

    /// The struct type of the closures made from `f`, and its capture types.
    pub(crate) fn closure_layout(&mut self, f: FuncId) -> Result<(String, &'a [MTy]), EmitError> {
        let env = self.closure_env(f)?;
        let name = format!("goat.c{}", f.0);
        let base = ["i32", "i32", "i32", "i32", "i64"];
        Ok((self.type_name(name, &base, &env.captures), &env.captures))
    }

    /// The drop id stored in the closures made from `f`.
    pub(crate) fn closure_drop_id(&mut self, f: FuncId) -> Result<u32, EmitError> {
        let (_, captures) = self.closure_layout(f)?;
        Ok(if holds_references(captures) {
            self.drop_id_of(DropKind::Closure(f))
        } else {
            0
        })
    }

    /// The immortal closure of `f`, which captures nothing.
    pub(crate) fn static_closure(&mut self, f: FuncId) -> String {
        let code = self.func_name(f);
        self.intern_static(format!("closure {}", f.0), |name| {
            format!(
                "{name} = private unnamed_addr constant {{ i32, i32, i32, i32, i64 }} \
                 {{ i32 {IMMORTAL}, i32 0, i32 0, i32 0, i64 ptrtoint (ptr {code} to i64) }}"
            )
        })
    }

    fn intern_static(&mut self, key: String, define: impl FnOnce(&str) -> String) -> String {
        if let Some(name) = self.heap.interned.get(&key) {
            return name.clone();
        }
        let name = format!("@goat.static.{}", self.heap.interned.len());
        self.heap.statics.push(define(&name));
        self.heap.interned.insert(key, name.clone());
        name
    }

    /// The immortal object for string literal `d`.
    pub(crate) fn string_constant(&mut self, d: DataId) -> Result<String, EmitError> {
        let bytes = self
            .program
            .data
            .get(d.0 as usize)
            .ok_or(EmitError::Malformed("unknown data"))?;
        let len = bytes.len();
        let text = escape_bytes(bytes);
        Ok(self.intern_static(format!("str {text}"), |name| {
            format!(
                "{name} = private unnamed_addr constant {{ i32, i32, i32, [{len} x i8] }} \
                 {{ i32 {IMMORTAL}, i32 0, i32 {len}, [{len} x i8] c\"{text}\" }}"
            )
        }))
    }

    /// The immortal cell of a record built from constants alone, or `None` when
    /// a field is not one.
    pub(crate) fn record_constant(
        &mut self,
        l: LayoutId,
        fields: &[Expr],
    ) -> Result<Option<String>, EmitError> {
        let (ty, tys) = self.record_layout(l)?;
        if tys.len() != fields.len() {
            return Err(EmitError::Malformed("record field count"));
        }
        let mut init = vec![format!("i32 {IMMORTAL}"), "i32 0".to_string()];
        for (ty, field) in tys.iter().zip(fields) {
            let Expr::Const(value) = field else {
                return Ok(None);
            };
            let Some(slot) = self.slot_constant(*ty, *value) else {
                return Ok(None);
            };
            init.push(slot);
        }
        let init = init.join(", ");
        Ok(Some(self.intern_static(format!("{ty} {init}"), |name| {
            format!("{name} = private unnamed_addr constant {ty} {{ {init} }}")
        })))
    }

    fn slot_constant(&self, ty: MTy, value: Const) -> Option<String> {
        let narrow = self.narrow();
        Some(match (ty, value) {
            (MTy::Int, Const::Int(n)) if !narrow => format!("i64 {n}"),
            (MTy::Int, Const::Int(n)) => format!("i32 {}, i32 0", i32::try_from(n).ok()?),
            (MTy::Float, Const::Float(x)) => {
                let rounded = hex_float(self.program.profile.round_float(x));
                if narrow {
                    format!("float {rounded}, i32 0")
                } else {
                    format!("double {rounded}")
                }
            }
            (MTy::Bool, Const::Bool(b)) => format!("i32 {}, i32 0", u8::from(b)),
            (MTy::Unit, Const::Unit) => "i64 0".to_string(),
            _ => return None,
        })
    }

    /// The immortal cell of a variant tag built without a payload.
    pub(crate) fn nullary_constant(&mut self, tag: u32) -> String {
        self.intern_static(format!("tag {tag}"), |name| {
            format!(
                "{name} = private unnamed_addr constant {{ i32, i32, i32, i32 }} \
                 {{ i32 {IMMORTAL}, i32 0, i32 {tag}, i32 0 }}"
            )
        })
    }

    /// The type definitions and constants the lowered code asked for, and the
    /// runtime functions that serve it, as module text. The definitions come
    /// before every function, which needs the types sized.
    pub(crate) fn heap_text(&mut self) -> Result<(String, String), EmitError> {
        let mut functions = String::new();
        loop {
            let wanted: Vec<_> = self.heap.runtime.iter().copied().collect();
            let mut closed = self.heap.runtime.clone();
            for runtime in &wanted {
                closed.extend(runtime.needs());
            }
            let grown = closed.len() != self.heap.runtime.len();
            self.heap.runtime = closed;
            if !grown {
                break;
            }
        }
        for id in 1.. {
            if id as usize > self.heap.drops.len() {
                break;
            }
            let text = self.drop_function(id)?;
            functions.push_str(&text);
            functions.push('\n');
        }
        let wanted: Vec<_> = self.heap.runtime.iter().copied().collect();
        for runtime in wanted {
            let text = match runtime {
                Runtime::ClassBytes => self.class_bytes_function(),
                Runtime::Alloc => self.alloc_function(),
                Runtime::Free => self.free_function(),
                Runtime::DropLoop => self.drop_loop_function(),
                Runtime::Retain => self.retain_function(),
                Runtime::Release => self.release_function(),
                Runtime::StrEq => self.str_eq_function(),
                Runtime::StrChars => self.str_chars_function(),
                Runtime::StrCopy => self.str_copy_function(),
                Runtime::StrChar => self.str_char_function(),
            };
            functions.push_str(&text);
            functions.push('\n');
        }
        let mut out = String::new();
        for (name, body) in &self.heap.types {
            let _ = writeln!(out, "%{name} = type {body}");
        }
        out.push('\n');
        for definition in &self.heap.statics {
            out.push_str(definition);
            out.push('\n');
        }
        Ok((out, functions))
    }

    /// The lines of a trap with `message` from a function whose instance is
    /// `%inst`; `tag` keeps the local names apart within the function.
    fn trap_lines(&mut self, message: &str, tag: &str) -> String {
        let (index, len) = self.text_constant(message);
        let (host, ctx, slot) = (
            instance_slot("host"),
            instance_slot("ctx"),
            host_slot("trap"),
        );
        format!(
            "  %host.{tag}.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 {host}\n  \
             %host.{tag} = load ptr, ptr %host.{tag}.at\n  \
             %ctx.{tag}.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 {ctx}\n  \
             %ctx.{tag} = load ptr, ptr %ctx.{tag}.at\n  \
             %trap.{tag}.at = getelementptr inbounds %goat_host, ptr %host.{tag}, i32 0, i32 {slot}\n  \
             %trap.{tag} = load ptr, ptr %trap.{tag}.at\n  \
             call void %trap.{tag}(ptr %ctx.{tag}, ptr @goat.text.{index}, i64 {len}) noreturn nounwind\n  \
             unreachable\n"
        )
    }

    fn instance_at(slot: &str, field: &str) -> String {
        format!(
            "  %{slot}.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 {}\n",
            instance_slot(field)
        )
    }

    fn class_bytes_function(&mut self) -> String {
        format!(
            "define internal i32 @goat.class_bytes(i32 %class) nounwind alwaysinline {{\n  \
             %small = icmp ule i32 %class, {SMALL_CLASSES}\n  \
             %by_small = shl i32 %class, 3\n  \
             %shift = sub i32 %class, {LARGE_BASE}\n  \
             %by_large = shl i32 1, %shift\n  \
             %bytes = select i1 %small, i32 %by_small, i32 %by_large\n  \
             ret i32 %bytes\n}}\n"
        )
    }

    /// `alloc(inst, size) -> ptr`: a block with `rc = 1`, from its class's free
    /// list when it has one and from the bump region otherwise.
    fn alloc_function(&mut self) -> String {
        let ctlz = self.intrinsic("ctlz.i32", "i32", "i32, i1");
        let exhausted = self.trap_lines(HEAP_BUDGET_EXHAUSTED, "full");
        let stale = self.trap_lines(STALE_WRITE, "stale");
        let over = self.trap_lines(HEAP_BUDGET_EXHAUSTED, "over");
        let free = instance_slot("free");
        let top_at = Self::instance_at("top", "heap_top");
        let limit_at = Self::instance_at("limit", "heap_size");
        let heap_at = Self::instance_at("heap", "heap");
        let live_at = Self::instance_at("live", "live");
        let count_at = Self::instance_at("count", "allocs");
        format!(
            "define internal ptr @goat.alloc(ptr %inst, i32 %size) nounwind {{\n\
             entry:\n  \
             %too_big = icmp ugt i32 %size, {MAX_REQUEST}\n  \
             br i1 %too_big, label %exhausted, label %sized\n\
             exhausted:\n{exhausted}\
             sized:\n  \
             %rounded = add i32 %size, 7\n  \
             %aligned = and i32 %rounded, -8\n  \
             %tiny = icmp ult i32 %aligned, 16\n  \
             %bytes = select i1 %tiny, i32 16, i32 %aligned\n  \
             %is_small = icmp ule i32 %bytes, {SMALL_MAX}\n  \
             %small_class = lshr i32 %bytes, 3\n  \
             %below = sub i32 %bytes, 1\n  \
             %zeros = call i32 {ctlz}(i32 %below, i1 false)\n  \
             %large_class = sub i32 {large}, %zeros\n  \
             %class = select i1 %is_small, i32 %small_class, i32 %large_class\n  \
             %block_bytes = call i32 @goat.class_bytes(i32 %class)\n  \
             %head.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 {free}, i32 %class\n  \
             %head = load ptr, ptr %head.at\n  \
             %has_free = icmp ne ptr %head, null\n  \
             br i1 %has_free, label %pop, label %bump\n\
             pop:\n  \
             %head_rc = load i32, ptr %head\n  \
             %written = icmp ne i32 %head_rc, 0\n  \
             br i1 %written, label %corrupt, label %unlink\n\
             corrupt:\n{stale}\
             unlink:\n  \
             %link.at = getelementptr inbounds i8, ptr %head, i64 {LINK_AT}\n  \
             %next = load ptr, ptr %link.at\n  \
             store ptr %next, ptr %head.at\n  \
             br label %ready\n\
             bump:\n{top_at}  \
             %top0 = load i64, ptr %top.at\n  \
             %fresh = icmp ult i64 %top0, 16\n  \
             %top = select i1 %fresh, i64 16, i64 %top0\n  \
             %span = zext i32 %block_bytes to i64\n  \
             %end = add i64 %top, %span\n{limit_at}  \
             %limit = load i64, ptr %limit.at\n  \
             %past = icmp ugt i64 %end, %limit\n  \
             br i1 %past, label %full, label %take\n\
             full:\n{over}\
             take:\n  \
             store i64 %end, ptr %top.at\n{heap_at}  \
             %heap = load ptr, ptr %heap.at\n  \
             %fresh_block = getelementptr inbounds i8, ptr %heap, i64 %top\n  \
             br label %ready\n\
             ready:\n  \
             %block = phi ptr [ %head, %unlink ], [ %fresh_block, %take ]\n  \
             store i32 1, ptr %block\n  \
             %class.at = getelementptr inbounds i8, ptr %block, i64 4\n  \
             store i32 %class, ptr %class.at\n{live_at}  \
             %live = load i32, ptr %live.at\n  \
             %live1 = add i32 %live, 1\n  \
             store i32 %live1, ptr %live.at\n{count_at}  \
             %count = load i64, ptr %count.at\n  \
             %count1 = add i64 %count, 1\n  \
             store i64 %count1, ptr %count.at\n  \
             ret ptr %block\n}}\n",
            large = LARGE_BASE + 32,
        )
    }

    /// `free(inst, ptr)`: takes a block whose count just reached zero, poisons
    /// it in checked builds, and pushes it on its class's free list.
    fn free_function(&mut self) -> String {
        let twice = self.trap_lines(DOUBLE_RELEASE, "twice");
        let free = instance_slot("free");
        let live_at = Self::instance_at("live", "live");
        let poison = if self.options.poison_freed {
            let memset = self.intrinsic("memset.p0.i64", "void", "ptr, i8, i64, i1");
            format!(
                "  %bytes = call i32 @goat.class_bytes(i32 %class)\n  \
                 %payload = getelementptr inbounds i8, ptr %block, i64 {LINK_AT}\n  \
                 %rest = sub i32 %bytes, {LINK_AT}\n  \
                 %rest64 = zext i32 %rest to i64\n  \
                 call void {memset}(ptr %payload, i8 {POISON}, i64 %rest64, i1 false)\n"
            )
        } else {
            String::new()
        };
        format!(
            "define internal void @goat.free(ptr %inst, ptr %block) nounwind {{\n\
             entry:\n  \
             %rc = load i32, ptr %block\n  \
             %held = icmp ne i32 %rc, 0\n  \
             br i1 %held, label %twice, label %go\n\
             twice:\n{twice}\
             go:\n  \
             %class.at = getelementptr inbounds i8, ptr %block, i64 4\n  \
             %class = load i32, ptr %class.at\n{poison}  \
             %head.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 {free}, i32 %class\n  \
             %head = load ptr, ptr %head.at\n  \
             %link.at = getelementptr inbounds i8, ptr %block, i64 {LINK_AT}\n  \
             store ptr %head, ptr %link.at\n  \
             store ptr %block, ptr %head.at\n{live_at}  \
             %live = load i32, ptr %live.at\n  \
             %live1 = sub i32 %live, 1\n  \
             store i32 %live1, ptr %live.at\n  \
             ret void\n}}\n"
        )
    }

    fn retain_function(&mut self) -> String {
        "define internal void @goat.retain(ptr %p) nounwind alwaysinline {\n  \
         %rc = load i32, ptr %p\n  \
         %immortal = icmp eq i32 %rc, -1\n  \
         br i1 %immortal, label %done, label %inc\n\
         inc:\n  \
         %n = add i32 %rc, 1\n  \
         store i32 %n, ptr %p\n  \
         br label %done\n\
         done:\n  \
         ret void\n}\n"
            .to_string()
    }

    /// `release(inst, ptr, id)`: a count that reaches zero hands the object to
    /// `drop_loop`; a count already at zero is a double release.
    fn release_function(&mut self) -> String {
        let twice = self.trap_lines(DOUBLE_RELEASE, "twice");
        format!(
            "define internal void @goat.release(ptr %inst, ptr %p, i32 %id) nounwind alwaysinline {{\n\
             entry:\n  \
             %rc = load i32, ptr %p\n  \
             %immortal = icmp eq i32 %rc, -1\n  \
             br i1 %immortal, label %done, label %live\n\
             live:\n  \
             %freed = icmp eq i32 %rc, 0\n  \
             br i1 %freed, label %twice, label %dec\n\
             twice:\n{twice}\
             dec:\n  \
             %n = sub i32 %rc, 1\n  \
             store i32 %n, ptr %p\n  \
             %dead = icmp eq i32 %n, 0\n  \
             br i1 %dead, label %drop, label %done\n\
             drop:\n  \
             call void @goat.drop_loop(ptr %inst, ptr %p, i32 %id)\n  \
             br label %done\n\
             done:\n  \
             ret void\n}}\n"
        )
    }

    /// `drop_loop(inst, object, id)`: tears down an object whose count just
    /// reached zero, and everything that dies with it, in constant stack. Each
    /// drop function pushes its dying children on a list threaded through the
    /// dead objects; this loop frees the object, pops the next, and repeats.
    fn drop_loop_function(&mut self) -> String {
        let heap_at = Self::instance_at("heap", "heap");
        let cases: String = (1..=self.heap.drops.len())
            .map(|id| format!(" i32 {id}, label %drop{id}"))
            .collect();
        let calls: String = (1..=self.heap.drops.len())
            .map(|id| {
                format!(
                    "drop{id}:\n  \
                     %after{id} = call i32 @goat.drop.{id}(ptr %inst, ptr %object, i32 %pending)\n  \
                     br label %release\n"
                )
            })
            .collect();
        let joins: String = (1..=self.heap.drops.len())
            .map(|id| format!(", [ %after{id}, %drop{id} ]"))
            .collect();
        format!(
            "define internal void @goat.drop_loop(ptr %inst, ptr %first, i32 %first_id) nounwind {{\n\
             entry:\n  \
             br label %loop\n\
             loop:\n  \
             %object = phi ptr [ %first, %entry ], [ %next, %pop ]\n  \
             %id = phi i32 [ %first_id, %entry ], [ %next_id, %pop ]\n  \
             %pending = phi i32 [ 0, %entry ], [ %link, %pop ]\n  \
             switch i32 %id, label %leaf [{cases} ]\n\
             leaf:\n  \
             br label %release\n{calls}\
             release:\n  \
             %remaining = phi i32 [ %pending, %leaf ]{joins}\n  \
             call void @goat.free(ptr %inst, ptr %object)\n  \
             %empty = icmp eq i32 %remaining, 0\n  \
             br i1 %empty, label %done, label %pop\n\
             pop:\n{heap_at}  \
             %heap = load ptr, ptr %heap.at\n  \
             %scaled = zext i32 %remaining to i64\n  \
             %offset = shl i64 %scaled, 3\n  \
             %next = getelementptr inbounds i8, ptr %heap, i64 %offset\n  \
             %link = load i32, ptr %next\n  \
             store i32 0, ptr %next\n  \
             %pad.at = getelementptr inbounds i8, ptr %next, i64 4\n  \
             %pad = load i32, ptr %pad.at\n  \
             %next_id = lshr i32 %pad, {DROP_ID_SHIFT}\n  \
             %class = and i32 %pad, {mask}\n  \
             store i32 %class, ptr %pad.at\n  \
             br label %loop\n\
             done:\n  \
             ret void\n}}\n",
            mask = (1 << DROP_ID_SHIFT) - 1,
        )
    }

    /// The drop function `id`: `(inst, object, pending) -> pending` releases
    /// each reference the object holds, pushing a child whose count reaches
    /// zero on the pending list instead of dropping it.
    fn drop_function(&mut self, id: u32) -> Result<String, EmitError> {
        let kind = self.heap.drops[id as usize - 1];
        let mut body = DropBody::new();
        match kind {
            DropKind::Closure(f) => {
                let (ty, tys) = self.closure_layout(f)?;
                self.drop_fields(&mut body, &ty, CLOSURE_BASE, tys)?;
            }
            DropKind::Record(l) => {
                let (ty, tys) = self.record_layout(l)?;
                self.drop_fields(&mut body, &ty, RECORD_BASE, tys)?;
            }
            DropKind::Variant(l) => {
                let Some(Layout::Variant(tags)) = self.program.layouts.get(l.0 as usize) else {
                    return Err(EmitError::Malformed("variant layout"));
                };
                let arms: Vec<u32> = tags
                    .iter()
                    .filter(|(_, tys)| holds_references(tys))
                    .map(|(tag, _)| *tag)
                    .collect();
                body.line(format!(
                    "%tag.at = getelementptr inbounds i8, ptr %object, i64 {TAG_AT}"
                ));
                body.line("%tag = load i32, ptr %tag.at".to_string());
                let cases: String = arms
                    .iter()
                    .map(|tag| format!(" i32 {tag}, label %arm{tag}"))
                    .collect();
                let switched = body.block.clone();
                body.line(format!("switch i32 %tag, label %out [{cases} ]"));
                let mut ends = vec![(body.pending.clone(), switched)];
                for tag in arms {
                    body.start(&format!("arm{tag}"));
                    let (ty, tys) = self.variant_layout(l, tag)?;
                    self.drop_fields(&mut body, &ty, VARIANT_BASE, tys)?;
                    body.line("br label %out".to_string());
                    ends.push((body.pending.clone(), body.block.clone()));
                }
                body.start("out");
                let incoming: Vec<_> = ends
                    .iter()
                    .map(|(pending, from)| format!("[ {pending}, %{from} ]"))
                    .collect();
                body.line(format!("%joined = phi i32 {}", incoming.join(", ")));
                body.pending = "%joined".to_string();
            }
        }
        let pending = body.pending.clone();
        body.line(format!("ret i32 {pending}"));
        let heap_at = Self::instance_at("heap", "heap");
        Ok(format!(
            "define internal i32 @goat.drop.{id}(ptr %inst, ptr %object, i32 %pending) nounwind {{\n\
             entry:\n{heap_at}  %heap = load ptr, ptr %heap.at\n{}}}\n",
            body.out
        ))
    }

    fn drop_fields(
        &mut self,
        body: &mut DropBody,
        ty: &str,
        base: usize,
        tys: &[MTy],
    ) -> Result<(), EmitError> {
        let narrow = self.narrow();
        for (i, field) in tys.iter().enumerate() {
            let MTy::Ptr(kind) = field else { continue };
            let at = field_index(narrow, base, tys, i);
            let id = match kind {
                HeapKind::Closure(_) => None,
                _ => Some(self.drop_id(*kind)?),
            };
            body.next += 1;
            let n = body.next;
            let message = self.trap_lines(DOUBLE_RELEASE, &format!("twice{n}"));
            let child = format!("%child{n}");
            body.line(format!(
                "%word{n}.at = getelementptr inbounds {ty}, ptr %object, i32 0, i32 {at}"
            ));
            body.line(format!("%word{n} = load i64, ptr %word{n}.at"));
            body.line(format!("{child} = inttoptr i64 %word{n} to ptr"));
            let from = body.block.clone();
            let before = body.pending.clone();
            body.line(format!("%rc{n} = load i32, ptr {child}"));
            body.line(format!("%immortal{n} = icmp eq i32 %rc{n}, {IMMORTAL}"));
            body.line(format!(
                "br i1 %immortal{n}, label %join{n}, label %live{n}"
            ));
            body.start(&format!("live{n}"));
            body.line(format!("%freed{n} = icmp eq i32 %rc{n}, 0"));
            body.line(format!("br i1 %freed{n}, label %twice{n}, label %dec{n}"));
            body.start(&format!("twice{n}"));
            body.out.push_str(&message);
            body.start(&format!("dec{n}"));
            body.line(format!("%n{n} = sub i32 %rc{n}, 1"));
            body.line(format!("store i32 %n{n}, ptr {child}"));
            body.line(format!("%dead{n} = icmp eq i32 %n{n}, 0"));
            body.line(format!("br i1 %dead{n}, label %push{n}, label %join{n}"));
            let skipped = body.block.clone();
            body.start(&format!("push{n}"));
            body.line(format!("store i32 {before}, ptr {child}"));
            let tag = match id {
                Some(id) => (id << DROP_ID_SHIFT).to_string(),
                None => {
                    body.line(format!(
                        "%cid{n}.at = getelementptr inbounds i8, ptr {child}, i64 {CLOSURE_DROP_AT}"
                    ));
                    body.line(format!("%cid{n} = load i32, ptr %cid{n}.at"));
                    body.line(format!("%shifted{n} = shl i32 %cid{n}, {DROP_ID_SHIFT}"));
                    format!("%shifted{n}")
                }
            };
            body.line(format!(
                "%pad{n}.at = getelementptr inbounds i8, ptr {child}, i64 4"
            ));
            body.line(format!("%pad{n} = load i32, ptr %pad{n}.at"));
            body.line(format!("%tagged{n} = or i32 %pad{n}, {tag}"));
            body.line(format!("store i32 %tagged{n}, ptr %pad{n}.at"));
            body.line(format!("%at{n} = ptrtoint ptr {child} to i64"));
            body.line(format!("%base{n} = ptrtoint ptr %heap to i64"));
            body.line(format!("%away{n} = sub i64 %at{n}, %base{n}"));
            body.line(format!("%scaled{n} = lshr i64 %away{n}, 3"));
            body.line(format!("%link{n} = trunc i64 %scaled{n} to i32"));
            body.line(format!("br label %join{n}"));
            let pushed = body.block.clone();
            body.start(&format!("join{n}"));
            body.line(format!(
                "%pending{n} = phi i32 [ {before}, %{from} ], [ {before}, %{skipped} ], [ %link{n}, %{pushed} ]"
            ));
            body.pending = format!("%pending{n}");
        }
        Ok(())
    }

    fn str_eq_function(&mut self) -> String {
        "define internal i1 @goat.str_eq(ptr %a, ptr %b) nounwind {\n\
         entry:\n  \
         %la.at = getelementptr inbounds i8, ptr %a, i64 8\n  \
         %la = load i32, ptr %la.at\n  \
         %lb.at = getelementptr inbounds i8, ptr %b, i64 8\n  \
         %lb = load i32, ptr %lb.at\n  \
         %same = icmp eq i32 %la, %lb\n  \
         br i1 %same, label %loop, label %no\n\
         loop:\n  \
         %i = phi i32 [ 0, %entry ], [ %i1, %step ]\n  \
         %end = icmp uge i32 %i, %la\n  \
         br i1 %end, label %yes, label %compare\n\
         compare:\n  \
         %i64 = zext i32 %i to i64\n  \
         %at = add i64 %i64, 12\n  \
         %pa = getelementptr inbounds i8, ptr %a, i64 %at\n  \
         %pb = getelementptr inbounds i8, ptr %b, i64 %at\n  \
         %x = load i8, ptr %pa\n  \
         %y = load i8, ptr %pb\n  \
         %equal = icmp eq i8 %x, %y\n  \
         br i1 %equal, label %step, label %no\n\
         step:\n  \
         %i1 = add i32 %i, 1\n  \
         br label %loop\n\
         yes:\n  \
         ret i1 true\n\
         no:\n  \
         ret i1 false\n}\n"
            .to_string()
    }

    /// `str_chars(s) -> i32`: the bytes that are not UTF-8 continuation bytes.
    fn str_chars_function(&mut self) -> String {
        "define internal i32 @goat.str_chars(ptr %s) nounwind {\n\
         entry:\n  \
         %len.at = getelementptr inbounds i8, ptr %s, i64 8\n  \
         %len = load i32, ptr %len.at\n  \
         br label %loop\n\
         loop:\n  \
         %i = phi i32 [ 0, %entry ], [ %i1, %body ]\n  \
         %count = phi i32 [ 0, %entry ], [ %count1, %body ]\n  \
         %end = icmp uge i32 %i, %len\n  \
         br i1 %end, label %done, label %body\n\
         body:\n  \
         %i64 = zext i32 %i to i64\n  \
         %at = add i64 %i64, 12\n  \
         %byte.at = getelementptr inbounds i8, ptr %s, i64 %at\n  \
         %byte = load i8, ptr %byte.at\n  \
         %high = and i8 %byte, -64\n  \
         %lead = icmp ne i8 %high, -128\n  \
         %lead32 = zext i1 %lead to i32\n  \
         %count1 = add i32 %count, %lead32\n  \
         %i1 = add i32 %i, 1\n  \
         br label %loop\n\
         done:\n  \
         ret i32 %count\n}\n"
            .to_string()
    }

    /// `str_copy(inst, bytes, len) -> ptr`: a new string (`rc = 1`) holding
    /// `len` bytes copied from `bytes`.
    fn str_copy_function(&mut self) -> String {
        let memcpy = self.intrinsic("memcpy.p0.p0.i64", "void", "ptr, ptr, i64, i1");
        format!(
            "define internal ptr @goat.str_copy(ptr %inst, ptr %bytes, i32 %len) nounwind {{\n  \
             %sum = add i32 %len, {STR_BYTES_AT}\n  \
             %huge = icmp ugt i32 %len, {MAX_REQUEST}\n  \
             %total = select i1 %huge, i32 -1, i32 %sum\n  \
             %s = call ptr @goat.alloc(ptr %inst, i32 %total)\n  \
             %len.at = getelementptr inbounds i8, ptr %s, i64 {STR_LEN_AT}\n  \
             store i32 %len, ptr %len.at\n  \
             %dst = getelementptr inbounds i8, ptr %s, i64 {STR_BYTES_AT}\n  \
             %n = zext i32 %len to i64\n  \
             call void {memcpy}(ptr %dst, ptr %bytes, i64 %n, i1 false)\n  \
             ret ptr %s\n}}\n"
        )
    }

    /// `str_char(inst, s, position) -> ptr`: a new string holding the code
    /// point at the 1-based `position`, trapping outside the string. The scan
    /// counts `position - 1` down to zero as an unsigned number, so a position
    /// below 1 is a huge count that runs off the end. Every read is checked
    /// against the header's length, so the copy stays inside the string even
    /// when it is not valid UTF-8.
    fn str_char_function(&mut self) -> String {
        let t = self.int_ty();
        let outside = self.trap_lines(BYTE_OUT_OF_RANGE, "outside");
        let lead = |name: &str, at: &str| {
            format!(
                "  %{name}.i = zext i32 {at} to i64\n  \
                 %{name}.off = add i64 %{name}.i, {STR_BYTES_AT}\n  \
                 %{name}.at = getelementptr inbounds i8, ptr %s, i64 %{name}.off\n  \
                 %{name}.byte = load i8, ptr %{name}.at\n  \
                 %{name}.high = and i8 %{name}.byte, -64\n  \
                 %{name} = icmp ne i8 %{name}.high, -128\n"
            )
        };
        let (start_lead, end_lead) = (lead("sl", "%start"), lead("el", "%end"));
        format!(
            "define internal ptr @goat.str_char(ptr %inst, ptr %s, {t} %position) nounwind {{\n\
             entry:\n  \
             %skip0 = sub {t} %position, 1\n  \
             %len.at = getelementptr inbounds i8, ptr %s, i64 {STR_LEN_AT}\n  \
             %len = load i32, ptr %len.at\n  \
             br label %scan\n\
             scan:\n  \
             %start = phi i32 [ 0, %entry ], [ %start1, %advance ]\n  \
             %skip = phi {t} [ %skip0, %entry ], [ %skip1, %advance ]\n  \
             %off_end = icmp uge i32 %start, %len\n  \
             br i1 %off_end, label %outside, label %check\n\
             outside:\n{outside}\
             check:\n{start_lead}  \
             br i1 %sl, label %at_lead, label %advance\n\
             at_lead:\n  \
             %arrived = icmp eq {t} %skip, 0\n  \
             br i1 %arrived, label %found, label %count_down\n\
             count_down:\n  \
             %skip_less = sub {t} %skip, 1\n  \
             br label %advance\n\
             advance:\n  \
             %skip1 = phi {t} [ %skip, %check ], [ %skip_less, %count_down ]\n  \
             %start1 = add i32 %start, 1\n  \
             br label %scan\n\
             found:\n  \
             %first = add i32 %start, 1\n  \
             br label %extend\n\
             extend:\n  \
             %end = phi i32 [ %first, %found ], [ %end1, %more ]\n  \
             %at_end = icmp uge i32 %end, %len\n  \
             br i1 %at_end, label %copy, label %peek\n\
             peek:\n{end_lead}  \
             br i1 %el, label %copy, label %more\n\
             more:\n  \
             %end1 = add i32 %end, 1\n  \
             br label %extend\n\
             copy:\n  \
             %size = sub i32 %end, %start\n  \
             %from.i = zext i32 %start to i64\n  \
             %from.off = add i64 %from.i, {STR_BYTES_AT}\n  \
             %from = getelementptr inbounds i8, ptr %s, i64 %from.off\n  \
             %made = call ptr @goat.str_copy(ptr %inst, ptr %from, i32 %size)\n  \
             ret ptr %made\n}}\n"
        )
    }
}

/// A drop function being written: the text after its entry block's first
/// lines, the block it is in, and the name of the pending list's head.
struct DropBody {
    out: String,
    block: String,
    pending: String,
    next: usize,
}

impl DropBody {
    fn new() -> DropBody {
        DropBody {
            out: String::new(),
            block: "entry".to_string(),
            pending: "%pending".to_string(),
            next: 0,
        }
    }

    fn line(&mut self, text: String) {
        let _ = writeln!(self.out, "  {text}");
    }

    fn start(&mut self, label: &str) {
        let _ = writeln!(self.out, "{label}:");
        self.block = label.to_string();
    }
}
