//! The frame buffer and method keys of an interactive program (ADR 0015, second
//! addendum; ADR 0035). A frame's shapes are encoded as `mir/src/frame.rs`
//! says into a heap block the instance holds (`frame`, `frame_len`,
//! `frame_cap`), and `present` hands the bytes to the table's `scene_frame`
//! and frees the block. The block is allocated by the first write of a frame,
//! so a frame that traps leaves it for the next frame's `reset`.

use super::heap::{CLOSURE_CODE_AT, Runtime, STR_BYTES_AT, STR_LEN_AT};
use super::*;
use goat_mir::frame::{LIMIT, TOO_BIG};

/// The smallest block the buffer asks the allocator for.
const MIN_CAPACITY: u32 = 256;
const HEADER: u32 = 8;

const NOT_A_METHOD: &str = "this closure is not a method";

impl Module<'_> {
    /// `frame_reserve(inst, n) -> ptr`: the address of `n` more bytes of the
    /// buffer, growing it (doubling, at least to fit) and trapping past the
    /// frame limit. The size is an `i64` so that a sum of string lengths cannot
    /// wrap before it is checked.
    pub(crate) fn frame_reserve_function(&mut self) -> String {
        let too_big = self.trap_lines(TOO_BIG, "big");
        let memcpy = self.intrinsic("memcpy.p0.p0.i64", "void", "ptr, ptr, i64, i1");
        let len_at = Self::instance_at("len", "frame_len");
        let cap_at = Self::instance_at("cap", "frame_cap");
        let frame_at = Self::instance_at("frame", "frame");
        format!(
            "define internal ptr @goat.frame_reserve(ptr %inst, i64 %n) nounwind {{\n\
             entry:\n{len_at}{frame_at}  \
             %len = load i32, ptr %len.at\n  \
             %len64 = zext i32 %len to i64\n  \
             %room = sub i64 {limit}, %len64\n  \
             %over = icmp ugt i64 %n, %room\n  \
             br i1 %over, label %big, label %fits\n\
             big:\n{too_big}\
             fits:\n  \
             %n32 = trunc i64 %n to i32\n  \
             %total = add i32 %len, %n32\n{cap_at}  \
             %cap = load i32, ptr %cap.at\n  \
             %needs_room = icmp ugt i32 %total, %cap\n  \
             br i1 %needs_room, label %grow, label %ready\n\
             grow:\n  \
             %doubled = shl i32 %cap, 1\n  \
             %short = icmp ult i32 %doubled, %total\n  \
             %want = select i1 %short, i32 %total, i32 %doubled\n  \
             %tiny = icmp ult i32 %want, {MIN_CAPACITY}\n  \
             %grown = select i1 %tiny, i32 {MIN_CAPACITY}, i32 %want\n  \
             %size = add i32 %grown, {HEADER}\n  \
             %block = call ptr @goat.alloc(ptr %inst, i32 %size)\n  \
             %old = load ptr, ptr %frame.at\n  \
             %has_old = icmp ne ptr %old, null\n  \
             br i1 %has_old, label %move, label %swap\n\
             move:\n  \
             %from = getelementptr inbounds i8, ptr %old, i64 {HEADER}\n  \
             %to = getelementptr inbounds i8, ptr %block, i64 {HEADER}\n  \
             call void {memcpy}(ptr %to, ptr %from, i64 %len64, i1 false)\n  \
             store i32 0, ptr %old\n  \
             call void @goat.free(ptr %inst, ptr %old)\n  \
             br label %swap\n\
             swap:\n  \
             store ptr %block, ptr %frame.at\n  \
             store i32 %grown, ptr %cap.at\n  \
             br label %ready\n\
             ready:\n  \
             store i32 %total, ptr %len.at\n  \
             %buffer = load ptr, ptr %frame.at\n  \
             %data = getelementptr inbounds i8, ptr %buffer, i64 {HEADER}\n  \
             %end = getelementptr inbounds i8, ptr %data, i64 %len64\n  \
             ret ptr %end\n}}\n",
            limit = LIMIT,
        )
    }

    /// `frame_reset(inst)`: frees whatever a frame that trapped left behind.
    pub(crate) fn frame_reset_function(&mut self) -> String {
        let len_at = Self::instance_at("len", "frame_len");
        let cap_at = Self::instance_at("cap", "frame_cap");
        let frame_at = Self::instance_at("frame", "frame");
        format!(
            "define internal void @goat.frame_reset(ptr %inst) nounwind {{\n\
             entry:\n{frame_at}  \
             %buffer = load ptr, ptr %frame.at\n  \
             %has = icmp ne ptr %buffer, null\n  \
             br i1 %has, label %release, label %done\n\
             release:\n  \
             store i32 0, ptr %buffer\n  \
             call void @goat.free(ptr %inst, ptr %buffer)\n  \
             br label %done\n\
             done:\n{len_at}{cap_at}  \
             store ptr null, ptr %frame.at\n  \
             store i32 0, ptr %len.at\n  \
             store i32 0, ptr %cap.at\n  \
             ret void\n}}\n"
        )
    }

    /// `frame_present(inst)`: hands the buffer's bytes to the host and frees it.
    pub(crate) fn frame_present_function(&mut self) -> String {
        let len_at = Self::instance_at("len", "frame_len");
        let frame_at = Self::instance_at("frame", "frame");
        let host_at = Self::instance_at("host", "host");
        let ctx_at = Self::instance_at("ctx", "ctx");
        let slot = host_slot("scene_frame");
        format!(
            "define internal void @goat.frame_present(ptr %inst) nounwind {{\n\
             entry:\n{frame_at}  \
             %buffer = load ptr, ptr %frame.at\n  \
             %has = icmp ne ptr %buffer, null\n  \
             br i1 %has, label %send, label %done\n\
             send:\n{len_at}  \
             %len = load i32, ptr %len.at\n  \
             %len64 = zext i32 %len to i64\n  \
             %data = getelementptr inbounds i8, ptr %buffer, i64 {HEADER}\n{host_at}  \
             %host = load ptr, ptr %host.at\n{ctx_at}  \
             %ctx = load ptr, ptr %ctx.at\n  \
             %send_fn.at = getelementptr inbounds %goat_host, ptr %host, i32 0, i32 {slot}\n  \
             %send_fn = load ptr, ptr %send_fn.at\n  \
             call void %send_fn(ptr %ctx, ptr %data, i64 %len64) nounwind\n  \
             br label %done\n\
             done:\n  \
             call void @goat.frame_reset(ptr %inst)\n  \
             ret void\n}}\n"
        )
    }
}

impl FuncLower<'_, '_> {
    pub(crate) fn frame_op(&mut self, op: &FrameOp) -> Result<Lowered, EmitError> {
        match op {
            FrameOp::Reset => {
                let reset = self.module.need(Runtime::FrameReset);
                self.line(format!("call void {reset}(ptr %inst)"));
            }
            FrameOp::Put(items) => self.frame_put(items)?,
            FrameOp::Present => {
                let present = self.module.need(Runtime::FramePresent);
                self.line(format!("call void {present}(ptr %inst)"));
            }
        }
        Ok(Some(Val::Unit))
    }

    fn literal_len(&self, data: DataId) -> Result<usize, EmitError> {
        self.module
            .program
            .data
            .get(data.0 as usize)
            .map(Vec::len)
            .ok_or(EmitError::Malformed("unknown data"))
    }

    /// The operand of the local `x`, which must have type `ty`.
    fn frame_value(&self, x: Local, ty: MTy) -> Result<String, EmitError> {
        match self.locals.get(&x) {
            Some(Val::Op(have, operand)) if *have == ty => Ok(operand.clone()),
            Some(_) => Err(EmitError::Malformed("frame value type")),
            None => Err(EmitError::UnboundLocal(x)),
        }
    }

    /// Appends `items` to the frame buffer: one `reserve` for the whole
    /// record, then each value stored where the cursor stands. The cursor
    /// moves past a string by its run-time length.
    fn frame_put(&mut self, items: &[FrameItem]) -> Result<(), EmitError> {
        if self.module.narrow() {
            return Err(EmitError::Unsupported("a frame on the embedded profile"));
        }
        let mut fixed = 0_i64;
        let mut strings = Vec::new();
        for item in items {
            fixed += match *item {
                FrameItem::Byte(_) | FrameItem::Bool(_) => 1,
                FrameItem::Int(_) | FrameItem::Float(_) => 8,
                FrameItem::Lit(d) => self.literal_len(d)? as i64,
                FrameItem::Str(x) => {
                    let s = self.string(x)?;
                    let len = self.load_i32_at(&s, STR_LEN_AT);
                    strings.push((s, len));
                    4
                }
            };
        }
        let mut total = fixed.to_string();
        for (_, len) in &strings {
            let wide = self.emit(format!("zext i32 {len} to i64"));
            total = self.emit(format!("add i64 {total}, {wide}"));
        }
        let reserve = self.module.need(Runtime::FrameReserve);
        let mut cursor = self.emit(format!("call ptr {reserve}(ptr %inst, i64 {total})"));
        let memcpy = self
            .module
            .intrinsic("memcpy.p0.p0.i64", "void", "ptr, ptr, i64, i1");
        let mut strings = strings.into_iter();
        for item in items {
            let advance = match *item {
                FrameItem::Byte(byte) => {
                    self.line(format!("store i8 {byte}, ptr {cursor}, align 1"));
                    "1".to_string()
                }
                FrameItem::Lit(d) => {
                    let len = self.literal_len(d)?;
                    if len > 0 {
                        let cell = self.module.string_constant(d)?;
                        let bytes = self.emit(format!(
                            "getelementptr inbounds i8, ptr {cell}, i64 {STR_BYTES_AT}"
                        ));
                        self.line(format!(
                            "call void {memcpy}(ptr {cursor}, ptr {bytes}, i64 {len}, i1 false)"
                        ));
                    }
                    len.to_string()
                }
                FrameItem::Int(x) => {
                    let value = self.frame_value(x, MTy::Int)?;
                    self.line(format!("store i64 {value}, ptr {cursor}, align 1"));
                    "8".to_string()
                }
                FrameItem::Float(x) => {
                    let value = self.frame_value(x, MTy::Float)?;
                    self.line(format!("store double {value}, ptr {cursor}, align 1"));
                    "8".to_string()
                }
                FrameItem::Bool(x) => {
                    let value = self.frame_value(x, MTy::Bool)?;
                    let byte = self.emit(format!("zext i1 {value} to i8"));
                    self.line(format!("store i8 {byte}, ptr {cursor}, align 1"));
                    "1".to_string()
                }
                FrameItem::Str(_) => {
                    let (s, len) = strings.next().ok_or(EmitError::Malformed("frame string"))?;
                    self.line(format!("store i32 {len}, ptr {cursor}, align 1"));
                    let body = self.emit(format!("getelementptr inbounds i8, ptr {cursor}, i64 4"));
                    let bytes = self.emit(format!(
                        "getelementptr inbounds i8, ptr {s}, i64 {STR_BYTES_AT}"
                    ));
                    let wide = self.emit(format!("zext i32 {len} to i64"));
                    self.line(format!(
                        "call void {memcpy}(ptr {body}, ptr {bytes}, i64 {wide}, i1 false)"
                    ));
                    self.emit(format!("add i64 {wide}, 4"))
                }
            };
            cursor = self.emit(format!(
                "getelementptr inbounds i8, ptr {cursor}, i64 {advance}"
            ));
        }
        Ok(())
    }

    /// The key of the method site `closure` was made at, as a string literal;
    /// traps for a closure no method site made.
    pub(crate) fn method_key(&mut self, closure: Local) -> Result<Lowered, EmitError> {
        let (object, _) = self.pointer(closure)?;
        let code = self.load_i64_at(&object, CLOSURE_CODE_AT);
        let (miss, join) = (self.label("miss"), self.label("join"));
        let mut arms = Vec::new();
        let program = self.module.program;
        for site in &program.method_sites {
            let address = self.module.func_name(site.func);
            let is = self.emit(format!(
                "icmp eq i64 {code}, ptrtoint (ptr {address} to i64)"
            ));
            let (hit, next) = (self.label("hit"), self.label("next"));
            self.line(format!("br i1 {is}, label %{hit}, label %{next}"));
            self.start(&hit);
            let key = self.module.string_constant(site.key)?;
            let from = self.block.clone();
            self.line(format!("br label %{join}"));
            arms.push((key, from));
            self.start(&next);
        }
        self.line(format!("br label %{miss}"));
        self.start(&miss);
        self.trap(NOT_A_METHOD);
        if arms.is_empty() {
            return Ok(None);
        }
        let ty = MTy::Ptr(HeapKind::Str);
        self.start(&join);
        let incoming = arms
            .iter()
            .map(|(key, from)| format!("[ {key}, %{from} ]"))
            .collect::<Vec<_>>()
            .join(", ");
        Ok(Some(Val::Op(ty, self.emit(format!("phi ptr {incoming}")))))
    }
}
