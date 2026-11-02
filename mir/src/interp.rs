use std::collections::HashMap;

use crate::mir::*;

const IMMORTAL: u32 = u32::MAX;
/// Debug-build interpreter frames are large; callers with deep recursion
/// should raise the limit via `run_with_depth` and grow their own stack.
const DEFAULT_MAX_DEPTH: usize = 128;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Unit,
    Ptr(usize),
}

#[derive(Debug, Clone, PartialEq)]
pub enum InterpError {
    Trap(String),
    DoubleFree(usize),
    UseAfterFree(usize),
    StackOverflow,
    Malformed(&'static str),
}

/// `live_allocations` counts heap objects still allocated when the entry
/// function returned, including its result if that is a pointer.
#[derive(Debug, Clone, PartialEq)]
pub struct Outcome {
    pub value: Value,
    pub live_allocations: usize,
}

pub fn run(program: &Program) -> Result<Outcome, InterpError> {
    run_with_depth(program, DEFAULT_MAX_DEPTH)
}

pub fn run_with_depth(program: &Program, max_depth: usize) -> Result<Outcome, InterpError> {
    let mut interp = Interp {
        program,
        max_depth,
        slots: Vec::new(),
        live: 0,
        strings: HashMap::new(),
    };
    let entry = Pending {
        func: program.entry,
        env: None,
        args: Vec::new(),
    };
    let value = interp.call(entry, 0)?;
    Ok(Outcome {
        value,
        live_allocations: interp.live,
    })
}

enum Body {
    Record(Vec<Value>),
    Variant(u32, Vec<Value>),
    Str,
    Closure(FuncId, Vec<Value>),
}

struct Obj {
    rc: u32,
    body: Body,
}

impl Obj {
    fn children(&self) -> impl Iterator<Item = usize> + '_ {
        let fields: &[Value] = match &self.body {
            Body::Record(f) | Body::Variant(_, f) | Body::Closure(_, f) => f,
            Body::Str => &[],
        };
        fields.iter().filter_map(|v| match v {
            Value::Ptr(a) => Some(*a),
            _ => None,
        })
    }
}

struct Pending {
    func: FuncId,
    env: Option<Value>,
    args: Vec<Value>,
}

enum Flow {
    Val(Value),
    Tail(Pending),
}

struct Frame {
    locals: HashMap<Local, Value>,
    env: Option<Local>,
}

impl Frame {
    fn get(&self, local: Local) -> Result<Value, InterpError> {
        self.locals
            .get(&local)
            .copied()
            .ok_or(InterpError::Malformed("unbound local"))
    }
}

struct Interp<'p> {
    program: &'p Program,
    max_depth: usize,
    slots: Vec<Option<Obj>>,
    live: usize,
    strings: HashMap<DataId, usize>,
}

impl Interp<'_> {
    fn alloc(&mut self, body: Body, rc: u32) -> Value {
        if rc != IMMORTAL {
            self.live += 1;
        }
        self.slots.push(Some(Obj { rc, body }));
        Value::Ptr(self.slots.len() - 1)
    }

    fn obj(&self, addr: usize) -> Result<&Obj, InterpError> {
        match self.slots.get(addr) {
            Some(Some(obj)) => Ok(obj),
            Some(None) => Err(InterpError::UseAfterFree(addr)),
            None => Err(InterpError::Malformed("dangling pointer")),
        }
    }

    fn retain(&mut self, value: Value) -> Result<Value, InterpError> {
        if let Value::Ptr(addr) = value {
            self.obj(addr)?;
            if let Some(Some(obj)) = self.slots.get_mut(addr)
                && obj.rc != IMMORTAL
            {
                obj.rc += 1;
            }
        }
        Ok(value)
    }

    fn release(&mut self, value: Value) -> Result<(), InterpError> {
        let Value::Ptr(addr) = value else {
            return Ok(());
        };
        let mut work = vec![addr];
        while let Some(addr) = work.pop() {
            let Some(slot) = self.slots.get_mut(addr) else {
                return Err(InterpError::Malformed("dangling pointer"));
            };
            let obj = slot.as_mut().ok_or(InterpError::DoubleFree(addr))?;
            match obj.rc {
                IMMORTAL => {}
                1 => {
                    let freed = slot.take().expect("slot checked above");
                    self.live -= 1;
                    work.extend(freed.children());
                }
                _ => obj.rc -= 1,
            }
        }
        Ok(())
    }

    fn call(&mut self, mut pending: Pending, depth: usize) -> Result<Value, InterpError> {
        if depth > self.max_depth {
            return Err(InterpError::StackOverflow);
        }
        loop {
            let func = self
                .program
                .funcs
                .get(pending.func.0 as usize)
                .ok_or(InterpError::Malformed("unknown function"))?;
            let mut frame = Frame {
                locals: func.params.iter().map(|p| p.0).zip(pending.args).collect(),
                env: func.env.as_ref().map(|e| e.local),
            };
            if let (Some(env), Some(value)) = (&func.env, pending.env) {
                frame.locals.insert(env.local, value);
            }
            match self.eval(&func.body, &mut frame, depth)? {
                Flow::Val(v) => return Ok(v),
                Flow::Tail(next) => pending = next,
            }
        }
    }

    fn value(&mut self, e: &Expr, frame: &mut Frame, depth: usize) -> Result<Value, InterpError> {
        match self.eval(e, frame, depth)? {
            Flow::Val(v) => Ok(v),
            Flow::Tail(_) => Err(InterpError::Malformed("tail call outside tail position")),
        }
    }

    fn values(
        &mut self,
        es: &[Expr],
        frame: &mut Frame,
        depth: usize,
    ) -> Result<Vec<Value>, InterpError> {
        es.iter().map(|e| self.value(e, frame, depth)).collect()
    }

    fn closure_target(&self, closure: Value) -> Result<FuncId, InterpError> {
        match closure {
            Value::Ptr(addr) => match self.obj(addr)?.body {
                Body::Closure(func, _) => Ok(func),
                _ => Err(InterpError::Malformed("not a closure")),
            },
            _ => Err(InterpError::Malformed("not a closure")),
        }
    }

    fn pending_closure(
        &mut self,
        closure: &Expr,
        args: &[Expr],
        frame: &mut Frame,
        depth: usize,
    ) -> Result<Pending, InterpError> {
        let closure = self.value(closure, frame, depth)?;
        let func = self.closure_target(closure)?;
        let args = self.values(args, frame, depth)?;
        Ok(Pending {
            func,
            env: Some(closure),
            args,
        })
    }

    fn field(&mut self, addr: Value, index: usize, tag: Option<u32>) -> Result<Value, InterpError> {
        let Value::Ptr(addr) = addr else {
            return Err(InterpError::Malformed("not a pointer"));
        };
        let value = match (&self.obj(addr)?.body, tag) {
            (Body::Record(fields), None) => fields.get(index),
            (Body::Variant(t, fields), Some(want)) if *t == want => fields.get(index),
            _ => None,
        }
        .copied()
        .ok_or(InterpError::Malformed("bad field access"))?;
        self.retain(value)
    }

    fn eval(&mut self, e: &Expr, frame: &mut Frame, depth: usize) -> Result<Flow, InterpError> {
        let value = match e {
            Expr::Const(c) => match *c {
                Const::Int(n) => Value::Int(n),
                Const::Float(x) => Value::Float(x),
                Const::Bool(b) => Value::Bool(b),
                Const::Unit => Value::Unit,
            },
            Expr::Local(x) => frame.get(*x)?,
            Expr::Let(x, rhs, body) => {
                let v = self.value(rhs, frame, depth)?;
                frame.locals.insert(*x, v);
                return self.eval(body, frame, depth);
            }
            Expr::BinInt(op, a, b) => {
                let (a, b) = (self.value(a, frame, depth)?, self.value(b, frame, depth)?);
                int_op(*op, a, b)?
            }
            Expr::BinFloat(op, a, b) => {
                let (a, b) = (self.value(a, frame, depth)?, self.value(b, frame, depth)?);
                float_op(*op, a, b)?
            }
            Expr::Cmp(op, a, b) => {
                let (a, b) = (self.value(a, frame, depth)?, self.value(b, frame, depth)?);
                compare(*op, a, b)?
            }
            Expr::If(cond, then, otherwise) => {
                let Value::Bool(c) = self.value(cond, frame, depth)? else {
                    return Err(InterpError::Malformed("if condition"));
                };
                return self.eval(if c { then } else { otherwise }, frame, depth);
            }
            Expr::Switch(x, arms, default) => {
                let Value::Ptr(addr) = frame.get(*x)? else {
                    return Err(InterpError::Malformed("switch scrutinee"));
                };
                let Body::Variant(tag, _) = self.obj(addr)?.body else {
                    return Err(InterpError::Malformed("switch scrutinee"));
                };
                let arm = arms
                    .iter()
                    .find(|(t, _)| *t == tag)
                    .map_or(&**default, |a| &a.1);
                return self.eval(arm, frame, depth);
            }
            Expr::CallDirect(f, args) => {
                let args = self.values(args, frame, depth)?;
                let pending = Pending {
                    func: *f,
                    env: None,
                    args,
                };
                self.call(pending, depth + 1)?
            }
            Expr::CallClosure(closure, args) => {
                let pending = self.pending_closure(closure, args, frame, depth)?;
                self.call(pending, depth + 1)?
            }
            Expr::TailCall(Callee::Direct(f), args) => {
                let args = self.values(args, frame, depth)?;
                return Ok(Flow::Tail(Pending {
                    func: *f,
                    env: None,
                    args,
                }));
            }
            Expr::TailCall(Callee::Closure(closure), args) => {
                return Ok(Flow::Tail(
                    self.pending_closure(closure, args, frame, depth)?,
                ));
            }
            Expr::MakeClosure(f, captures) => {
                let captures = self.values(captures, frame, depth)?;
                self.alloc(Body::Closure(*f, captures), 1)
            }
            Expr::Capture(i) => {
                let env = frame.env.ok_or(InterpError::Malformed("no env"))?;
                let Value::Ptr(addr) = frame.get(env)? else {
                    return Err(InterpError::Malformed("env"));
                };
                let Body::Closure(_, captures) = &self.obj(addr)?.body else {
                    return Err(InterpError::Malformed("env"));
                };
                let value = *captures.get(*i).ok_or(InterpError::Malformed("capture"))?;
                self.retain(value)?
            }
            Expr::AllocRecord(_, fields) => {
                let fields = self.values(fields, frame, depth)?;
                self.alloc(Body::Record(fields), 1)
            }
            Expr::Field(x, i) => {
                let record = frame.get(*x)?;
                self.field(record, *i, None)?
            }
            Expr::AllocVariant(_, tag, fields) => {
                let fields = self.values(fields, frame, depth)?;
                self.alloc(Body::Variant(*tag, fields), 1)
            }
            Expr::Payload(x, tag, i) => {
                let variant = frame.get(*x)?;
                self.field(variant, *i, Some(*tag))?
            }
            Expr::StrLit(d) => match self.strings.get(d) {
                Some(&addr) => Value::Ptr(addr),
                None => {
                    let Value::Ptr(addr) = self.alloc(Body::Str, IMMORTAL) else {
                        unreachable!("alloc returns a pointer");
                    };
                    self.strings.insert(*d, addr);
                    Value::Ptr(addr)
                }
            },
            Expr::Dup(x) => {
                self.retain(frame.get(*x)?)?;
                Value::Unit
            }
            Expr::Drop(x) => {
                self.release(frame.get(*x)?)?;
                Value::Unit
            }
            Expr::Trap(message) => return Err(InterpError::Trap(message.clone())),
        };
        Ok(Flow::Val(value))
    }
}

fn int_op(op: IntOp, a: Value, b: Value) -> Result<Value, InterpError> {
    let (Value::Int(a), Value::Int(b)) = (a, b) else {
        return Err(InterpError::Malformed("int operands"));
    };
    Ok(Value::Int(match op {
        IntOp::Add => a.wrapping_add(b),
        IntOp::Sub => a.wrapping_sub(b),
        IntOp::Mul => a.wrapping_mul(b),
        IntOp::Div if b == 0 => return Err(InterpError::Trap("division by zero".into())),
        IntOp::Div => a.wrapping_div(b),
    }))
}

fn float_op(op: FloatOp, a: Value, b: Value) -> Result<Value, InterpError> {
    let (Value::Float(a), Value::Float(b)) = (a, b) else {
        return Err(InterpError::Malformed("float operands"));
    };
    Ok(Value::Float(match op {
        FloatOp::Add => a + b,
        FloatOp::Sub => a - b,
        FloatOp::Mul => a * b,
        FloatOp::Div => a / b,
    }))
}

fn compare(op: CmpOp, a: Value, b: Value) -> Result<Value, InterpError> {
    use std::cmp::Ordering::*;
    let ord = match (a, b) {
        (Value::Int(a), Value::Int(b)) => a.partial_cmp(&b),
        (Value::Float(a), Value::Float(b)) => a.partial_cmp(&b),
        _ => return Err(InterpError::Malformed("comparison operands")),
    };
    Ok(Value::Bool(match op {
        CmpOp::Eq => ord == Some(Equal),
        CmpOp::Ne => ord != Some(Equal),
        CmpOp::Lt => ord == Some(Less),
        CmpOp::Le => matches!(ord, Some(Less | Equal)),
        CmpOp::Gt => ord == Some(Greater),
        CmpOp::Ge => matches!(ord, Some(Greater | Equal)),
    }))
}
