//! Closures on the native backend. A closure is a heap object holding its
//! body's address and its captures (`heap` has the layout); one that captures
//! nothing is a single immortal object. Every closure of a signature is called
//! the same way, `tailcc` with the instance, the environment, then the
//! arguments, so the caller needs only the signature.

use super::heap::{CLOSURE_BASE, CLOSURE_CODE_AT, CLOSURE_DROP_AT};
use super::*;

impl<'a> Module<'a> {
    pub(crate) fn closure_env(&self, f: FuncId) -> Result<&'a Env, EmitError> {
        self.program
            .funcs
            .get(f.0 as usize)
            .ok_or(EmitError::UnknownFunc(f))?
            .env
            .as_ref()
            .ok_or(EmitError::Malformed("closure target has no env"))
    }
}

impl FuncLower<'_, '_> {
    pub(crate) fn make_closure(
        &mut self,
        f: FuncId,
        captures: &[Expr],
    ) -> Result<Lowered, EmitError> {
        let env = self.module.closure_env(f)?;
        let kind = HeapKind::Closure(env.sig);
        if captures.is_empty() && env.captures.is_empty() {
            let cell = self.module.static_closure(f);
            return Ok(Some(Val::Op(MTy::Ptr(kind), cell)));
        }
        let (ty, tys) = self.module.closure_layout(f)?;
        let Some(values) = self.values(captures, tys)? else {
            return Ok(None);
        };
        let object = self.alloc(&ty);
        let drop_id = self.module.closure_drop_id(f)?;
        let at = self.emit(format!(
            "getelementptr inbounds i8, ptr {object}, i64 {CLOSURE_DROP_AT}"
        ));
        self.line(format!("store i32 {drop_id}, ptr {at}"));
        let at = self.emit(format!(
            "getelementptr inbounds i8, ptr {object}, i64 {CLOSURE_CODE_AT}"
        ));
        let code = self.module.func_name(f);
        self.line(format!("store i64 ptrtoint (ptr {code} to i64), ptr {at}"));
        self.store_slots(&object, &ty, CLOSURE_BASE, tys, &values)?;
        Ok(Some(Val::Op(MTy::Ptr(kind), object)))
    }

    /// A new reference to capture `i` of the closure this body runs as.
    pub(crate) fn capture(&mut self, i: usize) -> Result<Val, EmitError> {
        let env = self
            .func
            .env
            .as_ref()
            .ok_or(EmitError::Malformed("capture outside a closure"))?;
        let (object, _) = self.pointer(env.local)?;
        let (ty, tys) = self.module.closure_layout(self.id)?;
        if i >= tys.len() {
            return Err(EmitError::Malformed("capture index"));
        }
        self.load_slot(&object, &ty, CLOSURE_BASE, tys, i, true)
    }
}
