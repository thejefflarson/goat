//! Host output and foreign calls: what a program does that the table of
//! `goat_host` functions answers.

use super::heap::{STR_BYTES_AT, STR_LEN_AT};
use super::*;

/// The `goat_host` entries a `scene` or `turtle` foreign function has of its
/// own, in place of the generic `foreign`.
const VOCABULARY_MODULES: [&str; 2] = ["scene", "turtle"];

const VALUE_UNIT: u32 = 0;
const VALUE_NUMBER: u32 = 1;
const VALUE_INT: u32 = 2;
const VALUE_BOOL: u32 = 3;
const VALUE_STR: u32 = 4;

impl FuncLower<'_, '_> {
    /// Loads the table entry `name` and the context pointer the host expects
    /// as its first argument.
    pub(crate) fn host_entry(&mut self, name: &str) -> (String, String) {
        let host = self.instance_field("host");
        let host = self.emit(format!("load ptr, ptr {host}"));
        let ctx = self.instance_field("ctx");
        let ctx = self.emit(format!("load ptr, ptr {ctx}"));
        let slot = host_slot(name);
        let slot = self.emit(format!(
            "getelementptr inbounds %goat_host, ptr {host}, i32 0, i32 {slot}"
        ));
        let function = self.emit(format!("load ptr, ptr {slot}"));
        (function, ctx)
    }

    fn host_call(&mut self, name: &str, args: &str) {
        let (function, ctx) = self.host_entry(name);
        let args = if args.is_empty() {
            String::new()
        } else {
            format!(", {args}")
        };
        self.line(format!("call void {function}(ptr {ctx}{args}) nounwind"));
    }

    /// The bytes of string `s` and their count, as a pointer and an `i64`.
    fn string_text(&mut self, s: &str) -> (String, String) {
        let bytes = self.emit(format!(
            "getelementptr inbounds i8, ptr {s}, i64 {STR_BYTES_AT}"
        ));
        let len = self.emit(format!(
            "getelementptr inbounds i8, ptr {s}, i64 {STR_LEN_AT}"
        ));
        let len = self.emit(format!("load i32, ptr {len}"));
        let len = self.emit(format!("zext i32 {len} to i64"));
        (bytes, len)
    }

    /// The `double` or `i64` the host takes for a number, from the profile's.
    fn boundary_number(&mut self, value: &Val) -> Result<String, EmitError> {
        let operand = value.operand()?;
        Ok(match (value.ty(), self.module.narrow()) {
            (MTy::Float, true) => self.emit(format!("fpext float {operand} to double")),
            (MTy::Int, true) => self.emit(format!("sext i32 {operand} to i64")),
            _ => operand.to_string(),
        })
    }

    pub(crate) fn write(&mut self, write: &Write) -> Result<Lowered, EmitError> {
        match write {
            Write::Number(value) => {
                let Some(value) = self.expr(value)? else {
                    return Ok(None);
                };
                let (name, ty) = match value.ty() {
                    MTy::Float => ("write_number", "double"),
                    MTy::Int => ("write_int", "i64"),
                    _ => return Err(EmitError::Malformed("write of a non-number")),
                };
                let number = self.boundary_number(&value)?;
                self.host_call(name, &format!("{ty} {number}"));
            }
            Write::Str(x) => {
                let s = match self.locals.get(x) {
                    Some(Val::Op(MTy::Ptr(HeapKind::Str), operand)) => operand.clone(),
                    Some(_) => return Err(EmitError::Malformed("expected a string")),
                    None => return Err(EmitError::UnboundLocal(*x)),
                };
                let (bytes, len) = self.string_text(&s);
                self.host_call("write_string", &format!("ptr {bytes}, i64 {len}"));
            }
            Write::Lit(d) => {
                let s = self.module.string_constant(*d)?;
                let (bytes, len) = self.string_text(&s);
                self.host_call("write_string", &format!("ptr {bytes}, i64 {len}"));
            }
            Write::End => self.host_call("write_end", ""),
        }
        Ok(Some(Val::Unit))
    }

    /// A text constant as a pointer and an `i64` length.
    fn text_operands(&mut self, text: &str) -> String {
        let (index, len) = self.module.text_constant(text);
        format!("ptr @goat.text.{index}, i64 {len}")
    }

    pub(crate) fn call_foreign(
        &mut self,
        f: ForeignId,
        args: &[Local],
    ) -> Result<Lowered, EmitError> {
        let foreign = self
            .module
            .program
            .foreign
            .get(f.0 as usize)
            .ok_or(EmitError::Malformed("unknown foreign function"))?;
        if foreign.params.len() != args.len() {
            return Err(EmitError::Malformed("foreign call arity"));
        }
        let mut values = Vec::new();
        for (arg, want) in args.iter().zip(&foreign.params) {
            let value = self
                .locals
                .get(arg)
                .cloned()
                .ok_or(EmitError::UnboundLocal(*arg))?;
            expect(&value, *want)?;
            values.push(value);
        }
        let entry = format!("{}_{}", foreign.module, foreign.name);
        let vocabulary = VOCABULARY_MODULES.contains(&foreign.module.as_str())
            && foreign.ret == MTy::Unit
            && foreign
                .params
                .iter()
                .all(|ty| matches!(ty, MTy::Float | MTy::Ptr(HeapKind::Str)))
            && HOST_FUNCTIONS.contains(&entry.as_str())
            && entry != "scene_frame";
        if vocabulary {
            let mut passed = Vec::new();
            for value in &values {
                passed.push(match value.ty() {
                    MTy::Float => format!("double {}", self.boundary_number(value)?),
                    _ => {
                        let (bytes, len) = self.string_text(value.operand()?);
                        format!("ptr {bytes}, i64 {len}")
                    }
                });
            }
            self.host_call(&entry, &passed.join(", "));
            return Ok(Some(Val::Unit));
        }
        self.generic_foreign(foreign, &values).map(Some)
    }

    fn alloca(&mut self, ty: &str) -> String {
        let name = self.fresh();
        let _ = writeln!(self.allocas, "  {name} = alloca {ty}");
        name
    }

    fn value_field(&mut self, value: &str, field: usize) -> String {
        self.emit(format!(
            "getelementptr inbounds %goat_value, ptr {value}, i32 0, i32 {field}"
        ))
    }

    /// `foreign(ctx, module, name, args, count, result)`: the arguments are
    /// tagged values in an array, and the result comes back the same way. A
    /// string result is host memory valid until the next call, so it is copied
    /// into a new heap string.
    fn generic_foreign(&mut self, foreign: &ForeignFn, values: &[Val]) -> Result<Val, EmitError> {
        let count = values.len();
        let array = self.alloca(&format!("[{} x %goat_value]", count.max(1)));
        for (i, value) in values.iter().enumerate() {
            let cell = self.emit(format!(
                "getelementptr inbounds %goat_value, ptr {array}, i32 {i}"
            ));
            let (tag, a, b) = match value.ty() {
                MTy::Unit => (VALUE_UNIT, "0".to_string(), "0".to_string()),
                MTy::Float => {
                    let number = self.boundary_number(value)?;
                    let bits = self.emit(format!("bitcast double {number} to i64"));
                    (VALUE_NUMBER, bits, "0".to_string())
                }
                MTy::Int => (VALUE_INT, self.boundary_number(value)?, "0".to_string()),
                MTy::Bool => {
                    let wide = self.emit(format!("zext i1 {} to i64", value.operand()?));
                    (VALUE_BOOL, wide, "0".to_string())
                }
                MTy::Ptr(HeapKind::Str) => {
                    let (bytes, len) = self.string_text(value.operand()?);
                    let address = self.emit(format!("ptrtoint ptr {bytes} to i64"));
                    (VALUE_STR, address, len)
                }
                MTy::Ptr(_) => return Err(EmitError::Malformed("foreign argument type")),
            };
            for (field, text) in [
                (0, format!("i32 {tag}")),
                (1, format!("i64 {a}")),
                (2, format!("i64 {b}")),
            ] {
                let at = self.emit(format!(
                    "getelementptr inbounds %goat_value, ptr {cell}, i32 0, i32 {field}"
                ));
                self.line(format!("store {text}, ptr {at}"));
            }
        }
        let result = self.alloca("%goat_value");
        let module = self.text_operands(&foreign.module);
        let name = self.text_operands(&foreign.name);
        self.host_call(
            "foreign",
            &format!("{module}, {name}, ptr {array}, i64 {count}, ptr {result}"),
        );
        let word = |this: &mut Self, field: usize| {
            let at = this.value_field(&result, field);
            this.emit(format!("load i64, ptr {at}"))
        };
        Ok(match foreign.ret {
            MTy::Unit => Val::Unit,
            MTy::Float => {
                let bits = word(self, 1);
                let number = self.emit(format!("bitcast i64 {bits} to double"));
                let number = if self.module.narrow() {
                    self.emit(format!("fptrunc double {number} to float"))
                } else {
                    number
                };
                Val::Op(MTy::Float, number)
            }
            MTy::Int => {
                let wide = word(self, 1);
                if !self.module.narrow() {
                    return Ok(Val::Op(MTy::Int, wide));
                }
                let narrow = self.emit(format!("trunc i64 {wide} to i32"));
                let back = self.emit(format!("sext i32 {narrow} to i64"));
                let lost = self.emit(format!("icmp ne i64 {back}, {wide}"));
                self.trap_if(&lost, INT_OVERFLOW);
                Val::Op(MTy::Int, narrow)
            }
            MTy::Bool => {
                let wide = word(self, 1);
                Val::Op(MTy::Bool, self.emit(format!("icmp ne i64 {wide}, 0")))
            }
            MTy::Ptr(HeapKind::Str) => {
                let address = word(self, 1);
                let len = word(self, 2);
                let bytes = self.emit(format!("inttoptr i64 {address} to ptr"));
                let len = self.emit(format!("trunc i64 {len} to i32"));
                let made =
                    self.runtime_call(Runtime::StrCopy, "ptr", &format!("ptr {bytes}, i32 {len}"));
                Val::Op(MTy::Ptr(HeapKind::Str), made)
            }
            MTy::Ptr(_) => return Err(EmitError::Malformed("foreign result type")),
        })
    }
}
