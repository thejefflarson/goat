//! The goat native backend: typed HIR → a native object via Cranelift.
//!
//! Representation is uniform: every goat value is a Cranelift `i64`. A `Number`
//! is its `f64` bit pattern (reinterpreted, not converted), a `Bool` is 0/1,
//! `Unit` is 0, and a function value is a code pointer. One representation means
//! polymorphic functions compile once, with no monomorphization — a
//! `program(x) do x done` is a single `(i64) -> i64`.
//!
//! Functions are lambda-lifted: every `program(...)` becomes a top-level
//! Cranelift function. This first milestone does not implement closures, so a
//! function that refers to a variable it neither declares as a parameter nor
//! finds among the top-level functions is rejected with a clear error.

use cranelift::codegen::ir::{MemFlagsData, UserFuncName};
use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use goat_checker::Checked;
use goat_checker::hir::{BinOp, Expr, ExprId, ExprKind, Span, Symbol};
use goat_checker::ty::Ty;
use std::collections::HashMap;
use std::fmt;

pub use goat_checker::{GoatError, check};

#[derive(Debug)]
pub struct CompileError {
    pub span: Span,
    pub message: String,
}

impl CompileError {
    fn new(span: Span, message: impl Into<String>) -> CompileError {
        CompileError {
            span,
            message: message.into(),
        }
    }
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (at byte {})", self.message, self.span.start)
    }
}

impl std::error::Error for CompileError {}

/// A lifted function awaiting body compilation.
struct FuncDef<'a> {
    id: FuncId,
    params: Vec<Symbol>,
    body: &'a Expr,
}

/// Compile a checked program to a native object file's bytes.
pub fn compile(checked: &Checked) -> Result<Vec<u8>, CompileError> {
    let mut flags = settings::builder();
    // Position-independent code; required for PIE executables (the default on
    // macOS and most Linux distributions).
    flags.set("is_pic", "true").expect("known setting");
    let isa_builder = cranelift_native::builder().expect("host is a supported Cranelift target");
    let isa = isa_builder
        .finish(settings::Flags::new(flags))
        .expect("valid ISA flags");
    let builder = ObjectBuilder::new(isa, "goat", cranelift_module::default_libcall_names())
        .expect("object builder");

    let mut cg = Codegen {
        module: ObjectModule::new(builder),
        symbol_funcs: HashMap::new(),
        func_ids: HashMap::new(),
        print_number: None,
        print_bool: None,
    };

    // The runtime's `main` calls this.
    let entry = cg
        .module
        .declare_function("goat_entry", Linkage::Export, &cg.uni_sig(0, false))
        .expect("declare entry");
    cg.declare_runtime();

    // First pass: give every function a FuncId (so recursion and forward
    // references resolve) and map directly-bound names to their function.
    let mut defs = Vec::new();
    cg.collect(&checked.root, &mut defs)?;

    // Second pass: compile bodies, then the entry point.
    for def in &defs {
        cg.compile_function(def)?;
    }
    cg.compile_entry(entry, &checked.root, &checked.typed.root_ty)?;

    let product = cg.module.finish();
    Ok(product.emit().expect("emit object"))
}

struct Codegen {
    module: ObjectModule,
    symbol_funcs: HashMap<Symbol, FuncId>,
    func_ids: HashMap<ExprId, FuncId>,
    print_number: Option<FuncId>,
    print_bool: Option<FuncId>,
}

impl Codegen {
    /// A uniform signature: `argc` `i64` parameters, and one `i64` result
    /// unless `void`.
    fn uni_sig(&self, argc: usize, void: bool) -> Signature {
        let mut sig = self.module.make_signature();
        for _ in 0..argc {
            sig.params.push(AbiParam::new(types::I64));
        }
        if !void {
            sig.returns.push(AbiParam::new(types::I64));
        }
        sig
    }

    fn declare_runtime(&mut self) {
        let mut num = self.module.make_signature();
        num.params.push(AbiParam::new(types::F64));
        self.print_number = Some(
            self.module
                .declare_function("goat_print_number", Linkage::Import, &num)
                .expect("declare print_number"),
        );
        let mut b = self.module.make_signature();
        b.params.push(AbiParam::new(types::I64));
        self.print_bool = Some(
            self.module
                .declare_function("goat_print_bool", Linkage::Import, &b)
                .expect("declare print_bool"),
        );
    }

    /// Walk the whole tree, declaring a FuncId for every `program(...)` and
    /// recording the name each is bound to.
    fn collect<'b>(
        &mut self,
        expr: &'b Expr,
        defs: &mut Vec<FuncDef<'b>>,
    ) -> Result<(), CompileError> {
        match &expr.kind {
            ExprKind::Func { params, body } => {
                let sig = self.uni_sig(params.len(), false);
                let name = format!("goat_fn_{}", expr.id);
                let id = self
                    .module
                    .declare_function(&name, Linkage::Local, &sig)
                    .expect("declare function");
                self.func_ids.insert(expr.id, id);
                defs.push(FuncDef {
                    id,
                    params: params.iter().map(|p| p.symbol).collect(),
                    body,
                });
                self.collect(body, defs)?;
            }
            ExprKind::Let {
                symbol,
                value,
                rest,
                ..
            } => {
                self.collect(value, defs)?;
                if let ExprKind::Func { .. } = &value.kind {
                    self.symbol_funcs.insert(*symbol, self.func_ids[&value.id]);
                }
                if let Some(rest) = rest {
                    self.collect(rest, defs)?;
                }
            }
            ExprKind::App { callee, args } => {
                self.collect(callee, defs)?;
                for a in args {
                    self.collect(a, defs)?;
                }
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.collect(cond, defs)?;
                self.collect(then_branch, defs)?;
                if let Some(e) = else_branch {
                    self.collect(e, defs)?;
                }
            }
            ExprKind::Bin { lhs, rhs, .. } => {
                self.collect(lhs, defs)?;
                self.collect(rhs, defs)?;
            }
            ExprKind::Record { fields } => {
                for (_, v) in fields {
                    self.collect(v, defs)?;
                }
            }
            ExprKind::Field { record, .. } => self.collect(record, defs)?,
            ExprKind::Unit
            | ExprKind::Number(_)
            | ExprKind::Str(_)
            | ExprKind::Bool(_)
            | ExprKind::Var { .. } => {}
        }
        Ok(())
    }

    fn compile_function(&mut self, def: &FuncDef) -> Result<(), CompileError> {
        let mut ctx = self.module.make_context();
        ctx.func.signature = self.uni_sig(def.params.len(), false);
        ctx.func.name = UserFuncName::user(0, def.id.as_u32());
        let mut fbctx = FunctionBuilderContext::new();
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
            let block = b.create_block();
            b.append_block_params_for_function_params(block);
            b.switch_to_block(block);
            b.seal_block(block);

            let mut scope: HashMap<Symbol, Variable> = HashMap::new();
            for (i, sym) in def.params.iter().enumerate() {
                let param_val = b.block_params(block)[i];
                let var = b.declare_var(types::I64);
                b.def_var(var, param_val);
                scope.insert(*sym, var);
            }
            let ret = self.compile_expr(&mut b, &mut scope, def.body)?;
            b.ins().return_(&[ret]);
            let cfg = self.module.target_config();
            b.finalize(cfg);
        }
        self.module
            .define_function(def.id, &mut ctx)
            .expect("define function");
        self.module.clear_context(&mut ctx);
        Ok(())
    }

    fn compile_entry(
        &mut self,
        entry: FuncId,
        root: &Expr,
        root_ty: &Ty,
    ) -> Result<(), CompileError> {
        let mut ctx = self.module.make_context();
        ctx.func.signature = self.uni_sig(0, true);
        ctx.func.name = UserFuncName::user(0, entry.as_u32());
        let mut fbctx = FunctionBuilderContext::new();
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
            let block = b.create_block();
            b.switch_to_block(block);
            b.seal_block(block);

            let mut scope: HashMap<Symbol, Variable> = HashMap::new();
            let value = self.compile_expr(&mut b, &mut scope, root)?;
            self.emit_print(&mut b, value, root_ty);
            b.ins().return_(&[]);
            let cfg = self.module.target_config();
            b.finalize(cfg);
        }
        self.module
            .define_function(entry, &mut ctx)
            .expect("define entry");
        self.module.clear_context(&mut ctx);
        Ok(())
    }

    /// Print the program's result according to its static type.
    fn emit_print(&mut self, b: &mut FunctionBuilder, value: Value, ty: &Ty) {
        match ty {
            Ty::Number => {
                let f = b.ins().bitcast(types::F64, MemFlagsData::new(), value);
                let id = self.print_number.expect("runtime declared");
                let fref = self.module.declare_func_in_func(id, b.func);
                b.ins().call(fref, &[f]);
            }
            Ty::Bool => {
                let id = self.print_bool.expect("runtime declared");
                let fref = self.module.declare_func_in_func(id, b.func);
                b.ins().call(fref, &[value]);
            }
            // Unit, functions, and (for now) records/strings print nothing.
            _ => {}
        }
    }

    fn compile_expr(
        &mut self,
        b: &mut FunctionBuilder,
        scope: &mut HashMap<Symbol, Variable>,
        expr: &Expr,
    ) -> Result<Value, CompileError> {
        match &expr.kind {
            ExprKind::Unit => Ok(b.ins().iconst(types::I64, 0)),
            ExprKind::Bool(value) => Ok(b.ins().iconst(types::I64, i64::from(*value))),
            ExprKind::Number(n) => {
                let f = b.ins().f64const(*n);
                Ok(b.ins().bitcast(types::I64, MemFlagsData::new(), f))
            }
            ExprKind::Str(_) => Err(CompileError::new(
                expr.span,
                "strings are not supported by the native backend yet",
            )),
            ExprKind::Record { .. } | ExprKind::Field { .. } => Err(CompileError::new(
                expr.span,
                "records are not supported by the native backend yet",
            )),
            ExprKind::Var { symbol, name } => {
                if let Some(var) = scope.get(symbol) {
                    Ok(b.use_var(*var))
                } else if let Some(id) = self.symbol_funcs.get(symbol).copied() {
                    let fref = self.module.declare_func_in_func(id, b.func);
                    let ptr = self.module.target_config().pointer_type();
                    let addr = b.ins().func_addr(ptr, fref);
                    // Widen to the uniform i64 if the pointer is narrower.
                    Ok(if ptr == types::I64 {
                        addr
                    } else {
                        b.ins().uextend(types::I64, addr)
                    })
                } else {
                    Err(CompileError::new(
                        expr.span,
                        format!(
                            "`{name}` is captured from an enclosing scope; the native backend \
                             does not support closures yet"
                        ),
                    ))
                }
            }
            ExprKind::Func { .. } => {
                // A function used as a value: its address.
                let fid = self.func_id_of(expr)?;
                let fref = self.module.declare_func_in_func(fid, b.func);
                let ptr = self.module.target_config().pointer_type();
                let addr = b.ins().func_addr(ptr, fref);
                Ok(if ptr == types::I64 {
                    addr
                } else {
                    b.ins().uextend(types::I64, addr)
                })
            }
            ExprKind::Bin { op, lhs, rhs } => {
                let l = self.compile_expr(b, scope, lhs)?;
                let r = self.compile_expr(b, scope, rhs)?;
                let lf = b.ins().bitcast(types::F64, MemFlagsData::new(), l);
                let rf = b.ins().bitcast(types::F64, MemFlagsData::new(), r);
                let out = match op {
                    BinOp::Add => b.ins().fadd(lf, rf),
                    BinOp::Sub => b.ins().fsub(lf, rf),
                    BinOp::Mul => b.ins().fmul(lf, rf),
                    BinOp::Div => b.ins().fdiv(lf, rf),
                    BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte => {
                        let cc = match op {
                            BinOp::Lt => FloatCC::LessThan,
                            BinOp::Lte => FloatCC::LessThanOrEqual,
                            BinOp::Gt => FloatCC::GreaterThan,
                            BinOp::Gte => FloatCC::GreaterThanOrEqual,
                            _ => unreachable!(),
                        };
                        let cmp = b.ins().fcmp(cc, lf, rf);
                        return Ok(b.ins().uextend(types::I64, cmp));
                    }
                };
                Ok(b.ins().bitcast(types::I64, MemFlagsData::new(), out))
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_val = self.compile_expr(b, scope, cond)?;
                let then_blk = b.create_block();
                let else_blk = b.create_block();
                let merge = b.create_block();
                b.append_block_param(merge, types::I64);
                b.ins().brif(cond_val, then_blk, &[], else_blk, &[]);

                b.switch_to_block(then_blk);
                b.seal_block(then_blk);
                let tv = self.compile_expr(b, scope, then_branch)?;
                b.ins().jump(merge, &[tv.into()]);

                b.switch_to_block(else_blk);
                b.seal_block(else_blk);
                let ev = match else_branch {
                    Some(e) => self.compile_expr(b, scope, e)?,
                    None => b.ins().iconst(types::I64, 0),
                };
                b.ins().jump(merge, &[ev.into()]);

                b.switch_to_block(merge);
                b.seal_block(merge);
                Ok(b.block_params(merge)[0])
            }
            ExprKind::Let {
                symbol,
                value,
                rest,
                ..
            } => {
                let is_func = matches!(value.kind, ExprKind::Func { .. });
                if !is_func {
                    let v = self.compile_expr(b, scope, value)?;
                    let var = b.declare_var(types::I64);
                    b.def_var(var, v);
                    scope.insert(*symbol, var);
                }
                match rest {
                    Some(rest) => self.compile_expr(b, scope, rest),
                    // A trailing `name = value` with no body evaluates to the
                    // value itself.
                    None => {
                        if is_func {
                            self.compile_expr(b, scope, value)
                        } else {
                            let var = scope.get(symbol).expect("just bound");
                            Ok(b.use_var(*var))
                        }
                    }
                }
            }
            ExprKind::App { callee, args } => {
                let arg_vals: Vec<Value> = args
                    .iter()
                    .map(|a| self.compile_expr(b, scope, a))
                    .collect::<Result<_, _>>()?;

                // Direct call when the callee names a known function.
                if let ExprKind::Var { symbol, .. } = &callee.kind
                    && let Some(id) = self.symbol_funcs.get(symbol).copied()
                {
                    let fref = self.module.declare_func_in_func(id, b.func);
                    let call = b.ins().call(fref, &arg_vals);
                    return Ok(b.inst_results(call)[0]);
                }

                // Otherwise the callee is a function value: call it indirectly.
                let callee_val = self.compile_expr(b, scope, callee)?;
                let ptr = self.module.target_config().pointer_type();
                let addr = if ptr == types::I64 {
                    callee_val
                } else {
                    b.ins().ireduce(ptr, callee_val)
                };
                let sig = self.uni_sig(args.len(), false);
                let sigref = b.import_signature(sig);
                let call = b.ins().call_indirect(sigref, addr, &arg_vals);
                Ok(b.inst_results(call)[0])
            }
        }
    }

    /// The FuncId assigned to a `program(...)` node during collection.
    fn func_id_of(&self, func: &Expr) -> Result<FuncId, CompileError> {
        self.func_ids
            .get(&func.id)
            .copied()
            .ok_or_else(|| CompileError::new(func.span, "internal: unlifted function"))
    }
}
