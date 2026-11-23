//! The exports of an interactive program (ADR 0015) on the native backend. Each
//! takes `(host, ctx, instance)` first, as `goat_main` does, records the host
//! and context in the instance, and returns a zero value without running when
//! the table or the instance is older than the code (`goat_attach` says which).
//!
//! The host owns the model (count 1 from `goat_setup`); `goat_update` consumes
//! it and the event, `goat_draw` keeps the host's reference, and the stored
//! closures stay owned by the instance's `update`, `draw` and `sites` fields
//! until `goat_shutdown`. A host that swaps in a recompiled program keeps one
//! copy of those four fields per module and puts the running module's in the
//! instance around each call.

use super::heap::{RECORD_BASE, Runtime, TAG_AT, VARIANT_BASE};
use super::*;

/// The `goat_event_*` labels of the program, NUL-separated and closed by an
/// empty label: what the host subscribes to.
pub const SUBSCRIPTIONS: &str = "goat_subscriptions";

/// A parameter of an export after the instance: its LLVM type, its name and
/// its MIR type.
type Param = (&'static str, String, MTy);

impl<'a> Module<'a> {
    pub(crate) fn interactive_exports(
        &mut self,
        interactive: &Interactive,
    ) -> Result<String, EmitError> {
        let program = self.program;
        let func = |id: FuncId| {
            program
                .funcs
                .get(id.0 as usize)
                .ok_or(EmitError::UnknownFunc(id))
        };
        let param = |f: &Func, i: usize| match f.params.get(i) {
            Some((_, ty)) => Ok(*ty),
            None => Err(EmitError::Malformed("interactive function parameters")),
        };
        let kind_of = |ty: MTy| match ty {
            MTy::Ptr(kind) => Ok(kind),
            _ => Err(EmitError::Malformed("interactive entry takes no pointer")),
        };
        let root = func(program.entry)?;
        let (update, draw) = (func(interactive.update)?, func(interactive.draw)?);
        let reload = &interactive.reload;
        let root_kind = kind_of(root.ret)?;
        let root_layout = match root_kind {
            HeapKind::Record(l) => l,
            _ => return Err(EmitError::Malformed("interactive root is not a record")),
        };
        let root_fields = match program.layouts.get(root_layout.0 as usize) {
            Some(Layout::Record(fields)) => fields,
            _ => return Err(EmitError::Malformed("interactive root is not a record")),
        };
        let sites_ty = *root_fields
            .get(interactive.sites_slot)
            .ok_or(EmitError::Malformed("interactive root has no sites"))?;
        let update_ty = param(update, 0)?;
        let model_ty = param(update, 1)?;
        let draw_ty = param(draw, 0)?;
        let node = MTy::Ptr(HeapKind::Variant(reload.node));
        let outcome_kind = HeapKind::Variant(reload.outcome);
        let ptr = |name: &str, ty: MTy| -> Param { ("ptr", format!("%{name}"), ty) };

        let mut out = String::new();
        out.push_str(&self.attach_export());

        out.push_str(&self.export("goat_setup", &[], "ptr", |l| {
            let entry = l.module.program.entry;
            let Val::Op(_, root) = l.call_function(entry, Vec::new())? else {
                return Err(EmitError::Malformed("interactive root"));
            };
            let (ty, tys) = l.module.record_layout(root_layout)?;
            let mut slots = Vec::new();
            for slot in [
                interactive.draw_slot,
                interactive.init_slot,
                interactive.update_slot,
                interactive.sites_slot,
            ] {
                let value = l.load_slot(&root, &ty, RECORD_BASE, tys, slot, true)?;
                slots.push(value.operand()?.to_string());
            }
            l.release(&root, root_kind)?;
            for (field, operand) in [
                ("draw", &slots[0]),
                ("update", &slots[2]),
                ("sites", &slots[3]),
            ] {
                l.store_instance_ptr(field, operand);
            }
            Ok(Some(slots[1].clone()))
        })?);

        out.push_str(&self.export(
            "goat_update",
            &[ptr("model", model_ty), ptr("event", param(update, 2)?)],
            "ptr",
            |l| {
                let closure = l.load_instance_ptr("update");
                l.retain(&closure);
                let args = vec![
                    Val::Op(update_ty, closure),
                    Val::Op(model_ty, "%model".into()),
                    Val::Op(param(update, 2)?, "%event".into()),
                ];
                let result = l.call_function(interactive.update, args)?;
                Ok(Some(result.operand()?.to_string()))
            },
        )?);

        out.push_str(
            &self.export("goat_draw", &[ptr("model", model_ty)], "void", |l| {
                l.retain("%model");
                let closure = l.load_instance_ptr("draw");
                l.retain(&closure);
                let args = vec![
                    Val::Op(draw_ty, closure),
                    Val::Op(model_ty, "%model".into()),
                ];
                l.call_function(interactive.draw, args)?;
                Ok(None)
            })?,
        );

        out.push_str(&self.export(
            "goat_release_model",
            &[ptr("model", model_ty)],
            "void",
            |l| {
                l.release("%model", kind_of(model_ty)?)?;
                Ok(None)
            },
        )?);

        out.push_str(&self.export("goat_shutdown", &[], "void", |l| {
            for (field, ty) in [
                ("update", update_ty),
                ("draw", draw_ty),
                ("sites", sites_ty),
                ("reason", node),
            ] {
                l.release_instance_ptr(field, kind_of(ty)?)?;
            }
            Ok(None)
        })?);

        let snapshot = func(reload.snapshot)?;
        out.push_str(
            &self.export("goat_snapshot", &[ptr("model", model_ty)], "ptr", |l| {
                let args = vec![Val::Op(param(snapshot, 0)?, "%model".into())];
                let image = l.call_function(reload.snapshot, args)?;
                Ok(Some(image.operand()?.to_string()))
            })?,
        );

        let refresh = func(reload.refresh)?;
        out.push_str(&self.export(
            "goat_refresh",
            &[
                ptr("image", param(refresh, 0)?),
                ptr("fresh", param(refresh, 1)?),
            ],
            "ptr",
            |l| {
                l.retain("%fresh");
                let sites = l.load_instance_ptr("sites");
                l.retain(&sites);
                let args = vec![
                    Val::Op(param(refresh, 0)?, "%image".into()),
                    Val::Op(param(refresh, 1)?, "%fresh".into()),
                    Val::Op(param(refresh, 2)?, sites),
                ];
                let outcome = l.call_function(reload.refresh, args)?;
                let outcome = outcome.operand()?.to_string();
                let tag = l.load_i32_at(&outcome, TAG_AT);
                let refreshed = l.emit(format!("icmp eq i32 {tag}, {REFRESHED}"));
                let (ok, reset, join) = (l.label("refreshed"), l.label("reset"), l.label("join"));
                l.line(format!("br i1 {refreshed}, label %{ok}, label %{reset}"));

                l.start(&ok);
                let (ty, tys) = l.module.variant_layout(reload.outcome, REFRESHED)?;
                let rebuilt = l.load_slot(&outcome, &ty, VARIANT_BASE, tys, 0, true)?;
                let rebuilt = rebuilt.operand()?.to_string();
                l.release(&outcome, outcome_kind)?;
                let ok_end = l.block.clone();
                l.line(format!("br label %{join}"));

                l.start(&reset);
                l.release_instance_ptr("reason", kind_of(node)?)?;
                let (ty, tys) = l.module.variant_layout(reload.outcome, RESET)?;
                let reason = l.load_slot(&outcome, &ty, VARIANT_BASE, tys, 0, true)?;
                l.store_instance_ptr("reason", reason.operand()?);
                l.release(&outcome, outcome_kind)?;
                let reset_end = l.block.clone();
                l.line(format!("br label %{join}"));

                l.start(&join);
                Ok(Some(l.emit(format!(
                    "phi ptr [ {rebuilt}, %{ok_end} ], [ null, %{reset_end} ]"
                ))))
            },
        )?);

        let part = func(reload.part)?;
        out.push_str(&self.export(
            "goat_reason_part",
            &[("i32", "%index".into(), MTy::Int)],
            "ptr",
            |l| {
                let reason = l.load_instance_ptr("reason");
                let held = l.emit(format!("icmp ne ptr {reason}, null"));
                let (some, join) = (l.label("some"), l.label("join"));
                let entry = l.block.clone();
                l.line(format!("br i1 {held}, label %{some}, label %{join}"));
                l.start(&some);
                l.retain(&reason);
                let index = l.emit("zext i32 %index to i64");
                let args = vec![
                    Val::Op(param(part, 0)?, reason.clone()),
                    Val::Op(MTy::Int, index),
                ];
                let text = l.call_function(reload.part, args)?;
                let text = text.operand()?.to_string();
                l.release(&text, HeapKind::Str)?;
                let some_end = l.block.clone();
                l.line(format!("br label %{join}"));
                l.start(&join);
                Ok(Some(l.emit(format!(
                    "phi ptr [ {text}, %{some_end} ], [ null, %{entry} ]"
                ))))
            },
        )?);

        out.push_str(&self.export("goat_free_static", &[], "void", |_| Ok(None))?);

        out.push_str(&self.export(
            "goat_alloc",
            &[("i32", "%size".into(), MTy::Int)],
            "ptr",
            |l| Ok(Some(l.runtime_call(Runtime::Alloc, "ptr", "i32 %size"))),
        )?);

        let mut labels = String::new();
        for event in &interactive.events {
            let ctor = func(event.func)?;
            let mut params = Vec::new();
            for (i, (_, ty)) in ctor.params.iter().enumerate() {
                if let Some(llty) = self.llty(*ty)? {
                    params.push((llty, format!("%a{i}"), *ty));
                }
            }
            let ret = self.ret_ty(ctor.ret)?;
            let name = format!("goat_event_{}", event.label);
            out.push_str(&self.export(&name, &params, ret, |l| {
                let args = ctor
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, (_, ty))| match ty {
                        MTy::Unit => Val::Unit,
                        _ => Val::Op(*ty, format!("%a{i}")),
                    })
                    .collect();
                let event = l.call_function(event.func, args)?;
                Ok(match event {
                    Val::Unit => None,
                    Val::Op(_, operand) => Some(operand),
                })
            })?);
            labels.push_str(&event.label);
            labels.push('\0');
        }
        labels.push('\0');
        let _ = writeln!(
            out,
            "@{SUBSCRIPTIONS} = constant [{} x i8] c\"{}\"",
            labels.len(),
            escape_bytes(labels.as_bytes())
        );
        Ok(out)
    }

    /// `goat_attach(host, ctx, inst) -> status`: the version checks alone.
    fn attach_export(&self) -> String {
        format!(
            "define i32 @goat_attach(ptr %host, ptr %ctx, ptr %inst) nounwind {{\n\
             entry:\n  \
             %host_version = load i32, ptr %host\n  \
             %host_old = icmp ult i32 %host_version, {HOST_VERSION}\n  \
             br i1 %host_old, label %bad_host, label %check_instance\n\
             bad_host:\n  ret i32 {STATUS_HOST_VERSION}\n\
             check_instance:\n  \
             %instance_version = load i32, ptr %inst\n  \
             %instance_old = icmp ult i32 %instance_version, {INSTANCE_VERSION}\n  \
             br i1 %instance_old, label %bad_instance, label %ok\n\
             bad_instance:\n  ret i32 {STATUS_INSTANCE_VERSION}\n\
             ok:\n  ret i32 {STATUS_OK}\n}}\n\n"
        )
    }

    /// An export named `name`: `(host, ctx, inst, params...)`, whose body
    /// `body` lowers after the version checks. `body` returns the operand to
    /// return, or `None` for `void`.
    fn export(
        &mut self,
        name: &str,
        params: &[Param],
        ret: &str,
        body: impl FnOnce(&mut FuncLower<'_, 'a>) -> Result<Option<String>, EmitError>,
    ) -> Result<String, EmitError> {
        let program = self.program;
        let root = program.funcs.get(program.entry.0 as usize);
        let root = root.ok_or(EmitError::UnknownFunc(program.entry))?;
        let zero = match ret {
            "void" => "ret void",
            "ptr" => "ret ptr null",
            _ => "ret i32 0",
        };
        let mut lower = FuncLower::new(self, program.entry, root);
        let (host_field, ctx_field) = (instance_slot("host"), instance_slot("ctx"));
        lower.line("%host_version = load i32, ptr %host".to_string());
        lower.line(format!(
            "%host_old = icmp ult i32 %host_version, {HOST_VERSION}"
        ));
        lower.line("br i1 %host_old, label %stale, label %check".to_string());
        lower.start("check");
        lower.line("%instance_version = load i32, ptr %inst".to_string());
        lower.line(format!(
            "%instance_old = icmp ult i32 %instance_version, {INSTANCE_VERSION}"
        ));
        lower.line("br i1 %instance_old, label %stale, label %run".to_string());
        lower.start("stale");
        lower.line(zero.to_string());
        lower.start("run");
        lower.line(format!(
            "%host_at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 {host_field}"
        ));
        lower.line("store ptr %host, ptr %host_at".to_string());
        lower.line(format!(
            "%ctx_at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 {ctx_field}"
        ));
        lower.line("store ptr %ctx, ptr %ctx_at".to_string());
        let result = body(&mut lower)?;
        match result {
            Some(operand) => lower.line(format!("ret {ret} {operand}")),
            None => lower.line("ret void".to_string()),
        }
        let params: String = params
            .iter()
            .map(|(ty, name, _)| format!(", {ty} {name}"))
            .collect();
        Ok(format!(
            "define {ret} @{name}(ptr %host, ptr %ctx, ptr %inst{params}) nounwind {{\n\
             entry:\n{}{}{}}}\n\n",
            lower.allocas, lower.prologue, lower.body
        ))
    }
}

impl FuncLower<'_, '_> {
    /// A non-tail call of `f` on `values`, as a goat function makes one.
    fn call_function(&mut self, f: FuncId, values: Vec<Val>) -> Result<Val, EmitError> {
        let target = self
            .module
            .program
            .funcs
            .get(f.0 as usize)
            .ok_or(EmitError::UnknownFunc(f))?;
        let (name, prefix, operands) = self.direct_target(f, &values);
        let arguments = self.call_arguments(prefix, &operands)?;
        let ret = self.module.ret_ty(target.ret)?;
        let call = format!("call tailcc {ret} {name}({arguments})");
        self.finish_call(call, target.ret, false)?
            .ok_or(EmitError::Malformed("a call that does not return"))
    }

    fn load_instance_ptr(&mut self, field: &str) -> String {
        let at = self.instance_field(field);
        self.emit(format!("load ptr, ptr {at}"))
    }

    fn store_instance_ptr(&mut self, field: &str, value: &str) {
        let at = self.instance_field(field);
        self.line(format!("store ptr {value}, ptr {at}"));
    }

    /// Releases the reference an instance field holds, if it holds one, and
    /// clears it.
    fn release_instance_ptr(&mut self, field: &str, kind: HeapKind) -> Result<(), EmitError> {
        let held = self.load_instance_ptr(field);
        let some = self.emit(format!("icmp ne ptr {held}, null"));
        let (release, done) = (self.label("release"), self.label("done"));
        self.line(format!("br i1 {some}, label %{release}, label %{done}"));
        self.start(&release);
        self.release(&held, kind)?;
        self.line(format!("br label %{done}"));
        self.start(&done);
        self.store_instance_ptr(field, "null");
        Ok(())
    }
}
