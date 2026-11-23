//! The MIR nodes that build, read, share and release heap objects.

use super::heap::{
    RECORD_BASE, STR_BYTES_AT, STR_LEN_AT, TAG_AT, VARIANT_BASE, field_index, size_of,
};
use super::*;

impl<'a> FuncLower<'_, 'a> {
    fn pointer(&self, x: Local) -> Result<(String, HeapKind), EmitError> {
        match self.locals.get(&x) {
            Some(Val::Op(MTy::Ptr(kind), operand)) => Ok((operand.clone(), *kind)),
            Some(_) => Err(EmitError::Malformed("expected a pointer")),
            None => Err(EmitError::UnboundLocal(x)),
        }
    }

    fn string(&self, x: Local) -> Result<String, EmitError> {
        match self.pointer(x)? {
            (operand, HeapKind::Str) => Ok(operand),
            _ => Err(EmitError::Malformed("expected a string")),
        }
    }

    fn int_operand(&self, x: Local) -> Result<String, EmitError> {
        match self.locals.get(&x) {
            Some(Val::Op(MTy::Int, operand)) => Ok(operand.clone()),
            Some(_) => Err(EmitError::Malformed("expected an Int")),
            None => Err(EmitError::UnboundLocal(x)),
        }
    }

    fn variant_layout_of(&self, kind: HeapKind) -> Result<LayoutId, EmitError> {
        match kind {
            HeapKind::Variant(l) | HeapKind::List(l) => Ok(l),
            _ => Err(EmitError::Malformed("expected a variant")),
        }
    }

    pub(crate) fn retain(&mut self, p: &str) {
        let retain = self.module.need(Runtime::Retain);
        self.line(format!("call void {retain}(ptr {p})"));
    }

    pub(crate) fn release(&mut self, p: &str, kind: HeapKind) -> Result<(), EmitError> {
        let id = self.module.drop_id(kind)?;
        let release = self.module.need(Runtime::Release);
        self.line(format!("call void {release}(ptr %inst, ptr {p}, i32 {id})"));
        Ok(())
    }

    fn alloc(&mut self, ty: &str) -> String {
        let alloc = self.module.need(Runtime::Alloc);
        let size = size_of(ty);
        self.emit(format!("call ptr {alloc}(ptr %inst, i32 {size})"))
    }

    /// A call to a function that takes the instance first.
    pub(crate) fn runtime_call(&mut self, runtime: Runtime, ret: &str, args: &str) -> String {
        let callee = self.module.need(runtime);
        self.emit(format!("call {ret} {callee}(ptr %inst, {args})"))
    }

    /// Each operand of an allocation or a reuse, in order, checked against the
    /// slot types; `None` when one traps.
    fn values(&mut self, exprs: &[Expr], tys: &[MTy]) -> Result<Option<Vec<Val>>, EmitError> {
        if exprs.len() != tys.len() {
            return Err(EmitError::Malformed("field count"));
        }
        let mut values = Vec::new();
        for (expr, ty) in exprs.iter().zip(tys) {
            let Some(value) = self.expr(expr)? else {
                return Ok(None);
            };
            expect(&value, *ty)?;
            values.push(value);
        }
        Ok(Some(values))
    }

    fn slot_address(
        &mut self,
        object: &str,
        ty: &str,
        base: usize,
        tys: &[MTy],
        i: usize,
    ) -> String {
        let field = field_index(self.module.narrow(), base, tys, i);
        self.emit(format!(
            "getelementptr inbounds {ty}, ptr {object}, i32 0, i32 {field}"
        ))
    }

    fn store_slots(
        &mut self,
        object: &str,
        ty: &str,
        base: usize,
        tys: &[MTy],
        values: &[Val],
    ) -> Result<(), EmitError> {
        for (i, (slot_ty, value)) in tys.iter().zip(values).enumerate() {
            let Val::Op(_, operand) = value else { continue };
            let at = self.slot_address(object, ty, base, tys, i);
            let (stored_ty, stored) = match slot_ty {
                MTy::Ptr(_) => ("i64", self.emit(format!("ptrtoint ptr {operand} to i64"))),
                MTy::Bool => ("i32", self.emit(format!("zext i1 {operand} to i32"))),
                _ => (
                    self.module.llty(*slot_ty)?.expect("a value has a type"),
                    operand.clone(),
                ),
            };
            self.line(format!("store {stored_ty} {stored}, ptr {at}"));
        }
        Ok(())
    }

    /// Loads slot `i`; a pointer is a fresh owned reference when `retain` is
    /// set, and the cell's own reference moved out when it is not.
    fn load_slot(
        &mut self,
        object: &str,
        ty: &str,
        base: usize,
        tys: &[MTy],
        i: usize,
        retain: bool,
    ) -> Result<Val, EmitError> {
        let slot_ty = tys[i];
        if slot_ty == MTy::Unit {
            return Ok(Val::Unit);
        }
        let at = self.slot_address(object, ty, base, tys, i);
        let operand = match slot_ty {
            MTy::Ptr(_) => {
                let word = self.emit(format!("load i64, ptr {at}"));
                let pointer = self.emit(format!("inttoptr i64 {word} to ptr"));
                if retain {
                    self.retain(&pointer);
                }
                pointer
            }
            MTy::Bool => {
                let word = self.emit(format!("load i32, ptr {at}"));
                self.emit(format!("icmp ne i32 {word}, 0"))
            }
            _ => {
                let llty = self.module.llty(slot_ty)?.expect("a value has a type");
                self.emit(format!("load {llty}, ptr {at}"))
            }
        };
        Ok(Val::Op(slot_ty, operand))
    }

    fn store_tag(&mut self, object: &str, tag: u32) {
        let at = self.emit(format!(
            "getelementptr inbounds i8, ptr {object}, i64 {TAG_AT}"
        ));
        self.line(format!("store i32 {tag}, ptr {at}"));
    }

    fn load_i32_at(&mut self, object: &str, offset: u32) -> String {
        let at = self.emit(format!(
            "getelementptr inbounds i8, ptr {object}, i64 {offset}"
        ));
        self.emit(format!("load i32, ptr {at}"))
    }

    /// A `u32` as an `Int`.
    fn widen_unsigned(&mut self, value: String) -> String {
        if self.module.narrow() {
            value
        } else {
            self.emit(format!("zext i32 {value} to i64"))
        }
    }

    /// The address of byte `index` of string `s`, whose `Int` index may be
    /// negative or past the end: the caller has checked it.
    fn string_byte_address(&mut self, s: &str, index: &str) -> String {
        let wide = if self.module.narrow() {
            self.emit(format!("zext i32 {index} to i64"))
        } else {
            index.to_string()
        };
        let at = self.emit(format!("add i64 {wide}, {STR_BYTES_AT}"));
        self.emit(format!("getelementptr inbounds i8, ptr {s}, i64 {at}"))
    }

    pub(crate) fn heap_expr(&mut self, expr: &Expr) -> Result<Lowered, EmitError> {
        match expr {
            Expr::AllocRecord(l, fields) => {
                let kind = HeapKind::Record(*l);
                if let Some(cell) = self.module.record_constant(*l, fields)? {
                    return Ok(Some(Val::Op(MTy::Ptr(kind), cell)));
                }
                let (ty, tys) = self.module.record_layout(*l)?;
                let Some(values) = self.values(fields, tys)? else {
                    return Ok(None);
                };
                let object = self.alloc(&ty);
                self.store_slots(&object, &ty, RECORD_BASE, tys, &values)?;
                Ok(Some(Val::Op(MTy::Ptr(kind), object)))
            }
            Expr::ReuseRecord(x, l, fields) => self.reuse_record(*x, *l, fields),
            Expr::Field(x, i) => {
                let (object, kind) = self.pointer(*x)?;
                let HeapKind::Record(l) = kind else {
                    return Err(EmitError::Malformed("field of a non-record"));
                };
                let (ty, tys) = self.module.record_layout(l)?;
                if *i >= tys.len() {
                    return Err(EmitError::Malformed("field index"));
                }
                self.load_slot(&object, &ty, RECORD_BASE, tys, *i, true)
                    .map(Some)
            }
            Expr::AllocVariant(l, tag, fields) => {
                let kind = HeapKind::Variant(*l);
                let (ty, tys) = self.module.variant_layout(*l, *tag)?;
                if fields.is_empty() && tys.is_empty() {
                    let cell = self.module.nullary_constant(*tag);
                    return Ok(Some(Val::Op(MTy::Ptr(kind), cell)));
                }
                let Some(values) = self.values(fields, tys)? else {
                    return Ok(None);
                };
                let object = self.alloc(&ty);
                self.store_tag(&object, *tag);
                self.store_slots(&object, &ty, VARIANT_BASE, tys, &values)?;
                Ok(Some(Val::Op(MTy::Ptr(kind), object)))
            }
            Expr::Payload(x, tag, i) => {
                let (object, kind) = self.pointer(*x)?;
                let l = self.variant_layout_of(kind)?;
                let (ty, tys) = self.module.variant_layout(l, *tag)?;
                if *i >= tys.len() {
                    return Err(EmitError::Malformed("payload index"));
                }
                self.load_slot(&object, &ty, VARIANT_BASE, tys, *i, true)
                    .map(Some)
            }
            Expr::Unpack(x, tag, binds, body) => self.unpack(*x, *tag, binds, body),
            Expr::ReuseVariant(x, l, tag, fields) => self.reuse_variant(*x, *l, *tag, fields),
            Expr::Free(x) => {
                let (token, _) = self.pointer(*x)?;
                let empty = self.emit(format!("icmp eq ptr {token}, null"));
                let (free, done) = (self.label("free"), self.label("done"));
                self.line(format!("br i1 {empty}, label %{done}, label %{free}"));
                self.start(&free);
                self.line(format!("store i32 0, ptr {token}"));
                let release = self.module.need(Runtime::Free);
                self.line(format!("call void {release}(ptr %inst, ptr {token})"));
                self.line(format!("br label %{done}"));
                self.start(&done);
                Ok(Some(Val::Unit))
            }
            Expr::StrLit(d) => {
                let cell = self.module.string_constant(*d)?;
                Ok(Some(Val::Op(MTy::Ptr(HeapKind::Str), cell)))
            }
            Expr::StrEq(a, b) => {
                let (a, b) = (self.string(*a)?, self.string(*b)?);
                let equal = self.module.need(Runtime::StrEq);
                let same = self.emit(format!("call i1 {equal}(ptr {a}, ptr {b})"));
                Ok(Some(Val::Op(MTy::Bool, same)))
            }
            Expr::StrLen(s) => {
                let s = self.string(*s)?;
                let len = self.load_i32_at(&s, STR_LEN_AT);
                let len = self.widen_unsigned(len);
                Ok(Some(Val::Op(MTy::Int, len)))
            }
            Expr::StrByte(s, position) => {
                let (s, position) = (self.string(*s)?, self.int_operand(*position)?);
                let t = self.module.int_ty();
                let index = self.emit(format!("sub {t} {position}, 1"));
                let len = self.load_i32_at(&s, STR_LEN_AT);
                let len = self.widen_unsigned(len);
                // One unsigned comparison covers both ends: `Int::MIN` wraps to
                // a huge index.
                let outside = self.emit(format!("icmp uge {t} {index}, {len}"));
                self.trap_if(&outside, BYTE_OUT_OF_RANGE);
                let at = self.string_byte_address(&s, &index);
                let byte = self.emit(format!("load i8, ptr {at}"));
                let byte = self.emit(format!("zext i8 {byte} to {t}"));
                Ok(Some(Val::Op(MTy::Int, byte)))
            }
            Expr::StrChars(s) => {
                let s = self.string(*s)?;
                let chars = self.module.need(Runtime::StrChars);
                let count = self.emit(format!("call i32 {chars}(ptr {s})"));
                let count = self.widen_unsigned(count);
                Ok(Some(Val::Op(MTy::Int, count)))
            }
            Expr::StrChar(s, position) => {
                let (s, position) = (self.string(*s)?, self.int_operand(*position)?);
                let t = self.module.int_ty();
                let made =
                    self.runtime_call(Runtime::StrChar, "ptr", &format!("ptr {s}, {t} {position}"));
                Ok(Some(Val::Op(MTy::Ptr(HeapKind::Str), made)))
            }
            Expr::Addr(x) => {
                let (object, _) = self.pointer(*x)?;
                let address = self.emit(format!("ptrtoint ptr {object} to i64"));
                let heap = self.heap_base();
                let away = self.emit(format!("sub i64 {address}, {heap}"));
                let offset = if self.module.narrow() {
                    self.emit(format!("trunc i64 {away} to i32"))
                } else {
                    away
                };
                Ok(Some(Val::Op(MTy::Int, offset)))
            }
            Expr::Shared(x) => {
                let (object, _) = self.pointer(*x)?;
                let rc = self.emit(format!("load i32, ptr {object}"));
                // Counts 2 through `u32::MAX - 1`: not unique, not immortal, not freed.
                let shifted = self.emit(format!("sub i32 {rc}, 2"));
                let shared = self.emit(format!("icmp ult i32 {shifted}, -3"));
                Ok(Some(Val::Op(MTy::Bool, shared)))
            }
            Expr::Retain(x, ty) => {
                if !ty.is_ptr() {
                    return Err(EmitError::Malformed("retain of a non-pointer type"));
                }
                let offset = self.int_operand(*x)?;
                let offset = if self.module.narrow() {
                    self.emit(format!("zext i32 {offset} to i64"))
                } else {
                    offset
                };
                let heap = self.instance_field("heap");
                let heap = self.emit(format!("load ptr, ptr {heap}"));
                let object = self.emit(format!("getelementptr i8, ptr {heap}, i64 {offset}"));
                self.retain(&object);
                Ok(Some(Val::Op(*ty, object)))
            }
            Expr::KeepStr(s) => {
                let s = self.string(*s)?;
                let rc = self.emit(format!("load i32, ptr {s}"));
                let literal = self.emit(format!("icmp eq i32 {rc}, -1"));
                let (copy, keep, join) =
                    (self.label("copy"), self.label("keep"), self.label("join"));
                self.line(format!("br i1 {literal}, label %{copy}, label %{keep}"));
                self.start(&copy);
                let len = self.load_i32_at(&s, STR_LEN_AT);
                let bytes = self.emit(format!(
                    "getelementptr inbounds i8, ptr {s}, i64 {STR_BYTES_AT}"
                ));
                let made =
                    self.runtime_call(Runtime::StrCopy, "ptr", &format!("ptr {bytes}, i32 {len}"));
                let copied = self.block.clone();
                self.line(format!("br label %{join}"));
                self.start(&keep);
                self.retain(&s);
                self.line(format!("br label %{join}"));
                self.start(&join);
                let kept = self.emit(format!("phi ptr [ {made}, %{copied} ], [ {s}, %{keep} ]"));
                Ok(Some(Val::Op(MTy::Ptr(HeapKind::Str), kept)))
            }
            Expr::Dup(x) => {
                let (object, _) = self.pointer(*x)?;
                self.retain(&object);
                Ok(Some(Val::Unit))
            }
            Expr::Drop(x) => {
                let (object, kind) = self.pointer(*x)?;
                self.release(&object, kind)?;
                Ok(Some(Val::Unit))
            }
            _ => Err(EmitError::Unsupported("this node")),
        }
    }

    /// `ptrtoint` of the heap base.
    fn heap_base(&mut self) -> String {
        let heap = self.instance_field("heap");
        let heap = self.emit(format!("load ptr, ptr {heap}"));
        self.emit(format!("ptrtoint ptr {heap} to i64"))
    }

    pub(crate) fn switch(
        &mut self,
        x: Local,
        arms: &[(u32, Block)],
        default: &Block,
    ) -> Result<Lowered, EmitError> {
        let (object, kind) = self.pointer(x)?;
        self.variant_layout_of(kind)?;
        let tag = self.load_i32_at(&object, TAG_AT);
        let (join, fallback) = (self.label("join"), self.label("default"));
        let labels: Vec<String> = arms.iter().map(|_| self.label("case")).collect();
        let cases: Vec<_> = arms
            .iter()
            .zip(&labels)
            .map(|((tag, _), label)| format!("i32 {tag}, label %{label}"))
            .collect();
        self.line(format!(
            "switch i32 {tag}, label %{fallback} [ {} ]",
            cases.join(" ")
        ));
        let blocks = arms.iter().map(|(_, block)| block).chain([default]);
        let mut done = Vec::new();
        for (label, block) in labels.iter().chain([&fallback]).zip(blocks) {
            self.start(label);
            if let Some(value) = self.expr(block)? {
                let from = self.block.clone();
                self.line(format!("br label %{join}"));
                done.push((value, from));
            }
        }
        self.join(done, join)
    }

    /// Overwrites the record's cell when the count is 1, releasing the fields
    /// it held; otherwise drops this reference (the cell is shared, so the
    /// count cannot reach zero) and allocates.
    fn reuse_record(
        &mut self,
        x: Local,
        l: LayoutId,
        fields: &[Expr],
    ) -> Result<Lowered, EmitError> {
        let (cell, kind) = self.pointer(x)?;
        if kind != HeapKind::Record(l) {
            return Err(EmitError::Malformed("reuse of a different layout"));
        }
        let (ty, tys) = self.module.record_layout(l)?;
        let Some(values) = self.values(fields, tys)? else {
            return Ok(None);
        };
        let rc = self.emit(format!("load i32, ptr {cell}"));
        let unique = self.emit(format!("icmp eq i32 {rc}, 1"));
        let (reuse, fresh, join) = (self.label("reuse"), self.label("fresh"), self.label("join"));
        self.line(format!("br i1 {unique}, label %{reuse}, label %{fresh}"));
        self.start(&reuse);
        let mut olds = Vec::new();
        for (i, slot_ty) in tys.iter().enumerate() {
            if let MTy::Ptr(kind) = slot_ty {
                let old = self.load_slot(&cell, &ty, RECORD_BASE, tys, i, false)?;
                olds.push((old.operand()?.to_string(), *kind));
            }
        }
        self.store_slots(&cell, &ty, RECORD_BASE, tys, &values)?;
        for (old, kind) in olds {
            self.release(&old, kind)?;
        }
        let reused = self.block.clone();
        self.line(format!("br label %{join}"));
        self.start(&fresh);
        self.release(&cell, kind)?;
        let object = self.alloc(&ty);
        self.store_slots(&object, &ty, RECORD_BASE, tys, &values)?;
        let allocated = self.block.clone();
        self.line(format!("br label %{join}"));
        self.start(&join);
        let result = self.emit(format!(
            "phi ptr [ {cell}, %{reused} ], [ {object}, %{allocated} ]"
        ));
        Ok(Some(Val::Op(MTy::Ptr(kind), result)))
    }

    /// Moves the payload out of a cell this local solely owns. A unique cell
    /// is left hollow, and is the reuse token; a shared one has each field
    /// retained and this reference released, and the token is null.
    fn unpack(
        &mut self,
        x: Local,
        tag: u32,
        binds: &[Local],
        body: &Expr,
    ) -> Result<Lowered, EmitError> {
        let (cell, kind) = self.pointer(x)?;
        let l = self.variant_layout_of(kind)?;
        let (ty, tys) = self.module.variant_layout(l, tag)?;
        if tys.len() != binds.len() {
            return Err(EmitError::Malformed("unpack arity"));
        }
        let rc = self.emit(format!("load i32, ptr {cell}"));
        let unique = self.emit(format!("icmp eq i32 {rc}, 1"));
        let (hollow, shared, join) = (
            self.label("hollow"),
            self.label("shared"),
            self.label("join"),
        );
        self.line(format!("br i1 {unique}, label %{hollow}, label %{shared}"));
        self.start(&hollow);
        let moved = (0..tys.len())
            .map(|i| self.load_slot(&cell, &ty, VARIANT_BASE, tys, i, false))
            .collect::<Result<Vec<_>, _>>()?;
        let from_hollow = self.block.clone();
        self.line(format!("br label %{join}"));
        self.start(&shared);
        let copied = (0..tys.len())
            .map(|i| self.load_slot(&cell, &ty, VARIANT_BASE, tys, i, true))
            .collect::<Result<Vec<_>, _>>()?;
        self.release(&cell, kind)?;
        let from_shared = self.block.clone();
        self.line(format!("br label %{join}"));
        self.start(&join);
        let mut bound = Vec::new();
        for ((bind, slot_ty), (a, b)) in binds.iter().zip(tys).zip(moved.iter().zip(&copied)) {
            let value = match self.module.llty(*slot_ty)? {
                Some(llty) => {
                    let (a, b) = (a.operand()?, b.operand()?);
                    let phi = self.emit(format!(
                        "phi {llty} [ {a}, %{from_hollow} ], [ {b}, %{from_shared} ]"
                    ));
                    Val::Op(*slot_ty, phi)
                }
                None => Val::Unit,
            };
            bound.push((*bind, value));
        }
        let token = self.emit(format!(
            "phi ptr [ {cell}, %{from_hollow} ], [ null, %{from_shared} ]"
        ));
        bound.push((x, Val::Op(MTy::Ptr(kind), token)));
        let shadowed: Vec<_> = bound
            .into_iter()
            .map(|(local, value)| (local, self.locals.insert(local, value)))
            .collect();
        let result = self.expr(body);
        for (local, old) in shadowed.into_iter().rev() {
            match old {
                Some(old) => self.locals.insert(local, old),
                None => self.locals.remove(&local),
            };
        }
        result
    }

    /// Fills the reuse token's cell with the new variant, or allocates when
    /// the token is null (the cell it came from was shared).
    fn reuse_variant(
        &mut self,
        x: Local,
        l: LayoutId,
        tag: u32,
        fields: &[Expr],
    ) -> Result<Lowered, EmitError> {
        let (token, _) = self.pointer(x)?;
        let (ty, tys) = self.module.variant_layout(l, tag)?;
        let Some(values) = self.values(fields, tys)? else {
            return Ok(None);
        };
        let empty = self.emit(format!("icmp eq ptr {token}, null"));
        let (reuse, fresh, join) = (self.label("reuse"), self.label("fresh"), self.label("join"));
        self.line(format!("br i1 {empty}, label %{fresh}, label %{reuse}"));
        self.start(&reuse);
        self.store_tag(&token, tag);
        self.store_slots(&token, &ty, VARIANT_BASE, tys, &values)?;
        let reused = self.block.clone();
        self.line(format!("br label %{join}"));
        self.start(&fresh);
        let object = self.alloc(&ty);
        self.store_tag(&object, tag);
        self.store_slots(&object, &ty, VARIANT_BASE, tys, &values)?;
        let allocated = self.block.clone();
        self.line(format!("br label %{join}"));
        self.start(&join);
        let result = self.emit(format!(
            "phi ptr [ {token}, %{reused} ], [ {object}, %{allocated} ]"
        ));
        Ok(Some(Val::Op(MTy::Ptr(HeapKind::Variant(l)), result)))
    }
}
