//! Tail calls on the native backend (ADR 0042, D4). A function that tail-calls
//! itself becomes a loop. A group of functions joined by direct tail calls
//! becomes one function with a `which` argument and a `switch`, so mutual
//! recursion is a loop too. Every other tail call is `musttail call tailcc`.
//!
//! A `tailcc` signature keeps its arguments in registers. Apple clang's
//! aarch64 backend, at -O1 and above, returns from a `tailcc` function with
//! stack arguments without popping them, so a call passes the arguments past
//! the register budget through the instance's spill area instead. The area is
//! one set of words per instance: a caller stores them after it has evaluated
//! every argument and the callee loads them before it does anything else, and
//! a goat instance is single-threaded, so nothing runs between the two.

use super::heap::CLOSURE_CODE_AT;
use super::*;

/// How many arguments a `tailcc` signature carries in registers, and whether the
/// target guarantees `musttail`. The defaults are the smallest register files
/// of the 64-bit targets goat builds for (x86-64's six integer registers,
/// aarch64's eight vector ones), so one body is right on both.
#[derive(Clone, Copy, Debug)]
pub struct Abi {
    pub int_registers: usize,
    pub float_registers: usize,
    /// `false` for a target whose LLVM backend cannot tail call (thumbv6m): a
    /// tail call that is not a loop is then an error instead of `musttail`.
    pub musttail: bool,
}

impl Abi {
    pub const DEFAULT: Abi = Abi {
        int_registers: 6,
        float_registers: 8,
        musttail: true,
    };
}

/// Words in the instance's spill area, as `INSTANCE_FIELDS` declares it.
pub const SPILL_WORDS: usize = 8;

/// Functions emitted as one: `members[i]` runs when `which` is `i`. Each
/// member's parameters sit in `slots`, a parameter taking the first slot of
/// its LLVM type no earlier parameter of the member took.
pub(crate) struct Group {
    pub(crate) name: String,
    pub(crate) members: Vec<FuncId>,
    pub(crate) slots: Vec<&'static str>,
    /// For each member, the slot of each of its parameters (`None` for a `Unit`).
    pub(crate) assigned: Vec<Vec<Option<usize>>>,
    pub(crate) ret: MTy,
}

#[derive(Default)]
pub(crate) struct Plan {
    pub(crate) groups: Vec<Group>,
    member: BTreeMap<FuncId, (usize, usize)>,
    loops: BTreeSet<FuncId>,
}

impl Plan {
    pub(crate) fn new(program: &Program, narrow: bool) -> Plan {
        let mut plan = Plan::default();
        let eligible =
            |id: usize| program.funcs[id].env.is_none() && FuncId(id as u32) != program.entry;
        let mut edges = vec![Vec::new(); program.funcs.len()];
        for (index, func) in program.funcs.iter().enumerate() {
            func.body.for_each_node(&mut |e| {
                let Expr::TailCall(callee, _) = e else { return };
                match callee {
                    Callee::Direct(g) if g.0 as usize == index => {
                        plan.loops.insert(FuncId(index as u32));
                    }
                    Callee::Direct(g) => {
                        let g = g.0 as usize;
                        if g < edges.len() && eligible(index) && eligible(g) {
                            edges[index].push(g);
                        }
                    }
                    Callee::Closure(c) => {
                        if let (Expr::Local(l), Some(env)) = (&**c, &func.env)
                            && *l == env.local
                        {
                            plan.loops.insert(FuncId(index as u32));
                        }
                    }
                }
            });
        }
        for members in components(&edges) {
            let index = plan.groups.len();
            for (i, m) in members.iter().enumerate() {
                plan.member.insert(FuncId(*m as u32), (index, i));
            }
            plan.groups.push(group(program, narrow, index, &members));
        }
        plan
    }

    pub(crate) fn group_of(&self, f: FuncId) -> Option<(usize, usize)> {
        self.member.get(&f).copied()
    }

    pub(crate) fn loops(&self, f: FuncId) -> bool {
        self.loops.contains(&f)
    }
}

fn group(program: &Program, narrow: bool, index: usize, members: &[usize]) -> Group {
    let mut slots: Vec<&'static str> = Vec::new();
    let mut assigned = Vec::new();
    for &m in members {
        let mut taken = vec![false; slots.len()];
        let mut mine = Vec::new();
        for (_, ty) in &program.funcs[m].params {
            let Some(llty) = llvm_type(narrow, *ty) else {
                mine.push(None);
                continue;
            };
            let slot = match (0..slots.len()).find(|&s| slots[s] == llty && !taken[s]) {
                Some(s) => s,
                None => {
                    slots.push(llty);
                    taken.push(false);
                    slots.len() - 1
                }
            };
            taken[slot] = true;
            mine.push(Some(slot));
        }
        assigned.push(mine);
    }
    Group {
        name: format!("@goat_g{index}"),
        members: members.iter().map(|m| FuncId(*m as u32)).collect(),
        slots,
        assigned,
        ret: program.funcs[members[0]].ret,
    }
}

/// The strongly connected components of `edges` with more than one node, each
/// in ascending order and the components in order of their first node.
fn components(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = edges.len();
    let mut order = Vec::with_capacity(n);
    let mut seen = vec![false; n];
    for root in 0..n {
        if seen[root] {
            continue;
        }
        seen[root] = true;
        let mut stack = vec![(root, 0)];
        while let Some((node, next)) = stack.pop() {
            if let Some(&to) = edges[node].get(next) {
                stack.push((node, next + 1));
                if !seen[to] {
                    seen[to] = true;
                    stack.push((to, 0));
                }
            } else {
                order.push(node);
            }
        }
    }
    let mut back = vec![Vec::new(); n];
    for (from, tos) in edges.iter().enumerate() {
        for &to in tos {
            back[to].push(from);
        }
    }
    let mut component = vec![usize::MAX; n];
    let mut found: Vec<Vec<usize>> = Vec::new();
    for &root in order.iter().rev() {
        if component[root] != usize::MAX {
            continue;
        }
        let id = found.len();
        let mut members = Vec::new();
        let mut stack = vec![root];
        component[root] = id;
        while let Some(node) = stack.pop() {
            members.push(node);
            for &from in &back[node] {
                if component[from] == usize::MAX {
                    component[from] = id;
                    stack.push(from);
                }
            }
        }
        members.sort_unstable();
        found.push(members);
    }
    found.retain(|members| members.len() > 1);
    found.sort();
    found
}

/// The LLVM type of a value, `None` for the erased `Unit`.
pub(crate) fn llvm_type(narrow: bool, ty: MTy) -> Option<&'static str> {
    match ty {
        MTy::Int => Some(if narrow { "i32" } else { "i64" }),
        MTy::Float => Some(if narrow { "float" } else { "double" }),
        MTy::Bool => Some("i1"),
        MTy::Unit => None,
        MTy::Ptr(_) => Some("ptr"),
    }
}

/// Stands for an argument a group member does not take, in a slot it does not use.
const UNUSED: &str = "undef";

/// A branch back to the top of the function being lowered.
struct Edge {
    from: String,
    which: Option<usize>,
    values: Vec<String>,
}

/// The loop at the top of a function: its slots, what they hold when the
/// function is entered, and the tail calls that branch back to it.
pub(crate) struct Loop {
    slots: Vec<&'static str>,
    group: Option<usize>,
    entry: Vec<String>,
    entry_which: String,
    edges: Vec<Edge>,
}

impl Module<'_> {
    /// For each of `tys`, the arguments after a signature's `fixed`
    /// integer-class ones (the instance, the environment, `which`): `None` when
    /// it travels in a register, or the spill word it uses.
    pub(crate) fn spill_plan(
        &self,
        fixed: usize,
        tys: &[&str],
    ) -> Result<Vec<Option<usize>>, EmitError> {
        let abi = self.options.abi;
        let (mut ints, mut floats, mut spilled) = (fixed, 0, 0);
        tys.iter()
            .map(|ty| {
                let (used, budget) = if matches!(*ty, "float" | "double") {
                    (&mut floats, abi.float_registers)
                } else {
                    (&mut ints, abi.int_registers)
                };
                if *used < budget {
                    *used += 1;
                    return Ok(None);
                }
                spilled += 1;
                if spilled > SPILL_WORDS {
                    return Err(EmitError::Unsupported(
                        "a call with more arguments than registers and the spill area hold",
                    ));
                }
                Ok(Some(spilled - 1))
            })
            .collect()
    }
}

impl<'a> FuncLower<'_, 'a> {
    /// The LLVM type and operand of each value that is not a `Unit`.
    fn typed_operands(&self, values: &[Val]) -> Vec<(&'static str, String)> {
        let narrow = self.module.narrow();
        values
            .iter()
            .filter_map(|value| match value {
                Val::Op(ty, operand) => llvm_type(narrow, *ty).map(|ty| (ty, operand.clone())),
                Val::Unit => None,
            })
            .collect()
    }

    /// The callee, its leading arguments and the rest of them, for a direct
    /// call. A member of a group is called through the group's function, naming
    /// the member in `which`.
    fn direct_target(
        &self,
        callee: FuncId,
        values: &[Val],
    ) -> (String, Vec<String>, Vec<(&'static str, String)>) {
        let Some((index, member)) = self.module.plan.group_of(callee) else {
            let name = self.module.func_name(callee);
            return (
                name,
                vec!["ptr %inst".to_string()],
                self.typed_operands(values),
            );
        };
        let group = &self.module.plan.groups[index];
        let mut operands: Vec<_> = group
            .slots
            .iter()
            .map(|ty| (*ty, UNUSED.to_string()))
            .collect();
        for (slot, value) in group.assigned[member].iter().zip(values) {
            if let (Some(slot), Val::Op(_, operand)) = (slot, value) {
                operands[*slot].1 = operand.clone();
            }
        }
        let prefix = vec!["ptr %inst".to_string(), format!("i32 {member}")];
        (group.name.clone(), prefix, operands)
    }

    pub(crate) fn call(
        &mut self,
        callee: FuncId,
        args: &[Expr],
        tail: bool,
    ) -> Result<Lowered, EmitError> {
        let target = self
            .module
            .program
            .funcs
            .get(callee.0 as usize)
            .ok_or(EmitError::UnknownFunc(callee))?;
        let tys: Vec<_> = target.params.iter().map(|(_, ty)| *ty).collect();
        let Some(values) = self.values(args, &tys)? else {
            return Ok(None);
        };
        if tail && let Some(edge) = self.loop_edge(callee, &values) {
            return Ok(self.branch_back(edge));
        }
        let (name, prefix, operands) = self.direct_target(callee, &values);
        let arguments = self.call_arguments(prefix, &operands)?;
        let ret = self.module.ret_ty(target.ret)?;
        self.finish_call(
            format!("call tailcc {ret} {name}({arguments})"),
            target.ret,
            tail,
        )
    }

    pub(crate) fn call_closure(
        &mut self,
        closure: &Expr,
        args: &[Expr],
        tail: bool,
    ) -> Result<Lowered, EmitError> {
        let Some(callee) = self.expr(closure)? else {
            return Ok(None);
        };
        let Val::Op(MTy::Ptr(HeapKind::Closure(sig)), env) = callee else {
            return Err(EmitError::Malformed("callee is not a closure"));
        };
        let sig = self
            .module
            .program
            .sigs
            .get(sig.0 as usize)
            .ok_or(EmitError::Malformed("unknown signature"))?;
        if sig.params.len() != args.len() {
            return Err(EmitError::Malformed("closure call arity"));
        }
        let Some(values) = self.values(args, &sig.params)? else {
            return Ok(None);
        };
        let own_env = self.func.env.as_ref().map(|env| env.local);
        if tail && self.looped.is_some() && matches!(closure, Expr::Local(l) if Some(*l) == own_env)
        {
            let values = self
                .typed_operands(&values)
                .into_iter()
                .map(|(_, v)| v)
                .collect();
            let edge = Edge {
                from: String::new(),
                which: None,
                values,
            };
            return Ok(self.branch_back(edge));
        }
        let word = self.load_i64_at(&env, CLOSURE_CODE_AT);
        let code = self.emit(format!("inttoptr i64 {word} to ptr"));
        let prefix = vec!["ptr %inst".to_string(), format!("ptr {env}")];
        let operands = self.typed_operands(&values);
        let arguments = self.call_arguments(prefix, &operands)?;
        let ret = self.module.ret_ty(sig.ret)?;
        self.finish_call(
            format!("call tailcc {ret} {code}({arguments})"),
            sig.ret,
            tail,
        )
    }

    /// Emits `call`: a tail call, or one that waits on a result.
    fn finish_call(&mut self, call: String, ret: MTy, tail: bool) -> Result<Lowered, EmitError> {
        if !tail {
            return Ok(Some(self.bound_call(call, ret)));
        }
        if !self.module.options.abi.musttail {
            return Err(EmitError::Unsupported(
                "a tail call on a target without guaranteed tail calls",
            ));
        }
        if ret == MTy::Unit {
            self.line(format!("musttail {call}"));
            self.line("ret void".to_string());
        } else {
            let result = self.emit(format!("musttail {call}"));
            let ret = self.module.ret_ty(ret)?;
            self.line(format!("ret {ret} {result}"));
        }
        Ok(None)
    }

    /// The branch back that a tail call to `callee` is, when the function being
    /// lowered is the loop `callee` is the top of.
    fn loop_edge(&self, callee: FuncId, values: &[Val]) -> Option<Edge> {
        let looped = self.looped.as_ref()?;
        let from = String::new();
        match (looped.group, self.module.plan.group_of(callee)) {
            (Some(g), Some((index, member))) if g == index => {
                let (_, _, operands) = self.direct_target(callee, values);
                let values = operands.into_iter().map(|(_, v)| v).collect();
                Some(Edge {
                    from,
                    which: Some(member),
                    values,
                })
            }
            (None, None) if callee == self.id => {
                let values = self
                    .typed_operands(values)
                    .into_iter()
                    .map(|(_, v)| v)
                    .collect();
                Some(Edge {
                    from,
                    which: None,
                    values,
                })
            }
            _ => None,
        }
    }

    fn branch_back(&mut self, mut edge: Edge) -> Lowered {
        edge.from = self.block.clone();
        self.line("br label %loop".to_string());
        self.looped
            .as_mut()
            .expect("a loop edge needs a loop")
            .edges
            .push(edge);
        None
    }

    fn spill_address(&mut self, word: usize) -> String {
        let slot = instance_slot("spill");
        self.emit(format!(
            "getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 {slot}, i32 {word}"
        ))
    }

    /// The text of a call's arguments: `prefix` (the instance and whatever else
    /// is passed first), then each operand, with the ones past the register
    /// budget stored to the spill area instead.
    fn call_arguments(
        &mut self,
        prefix: Vec<String>,
        operands: &[(&'static str, String)],
    ) -> Result<String, EmitError> {
        let tys: Vec<_> = operands.iter().map(|(ty, _)| *ty).collect();
        let plan = self.module.spill_plan(prefix.len(), &tys)?;
        let mut passed = prefix;
        for ((ty, operand), spill) in operands.iter().zip(plan) {
            match spill {
                None => passed.push(format!("{ty} {operand}")),
                Some(word) if operand != UNUSED => {
                    let value = self.spill_word(ty, operand);
                    let at = self.spill_address(word);
                    self.line(format!("store i64 {value}, ptr {at}"));
                }
                Some(_) => {}
            }
        }
        Ok(passed.join(", "))
    }

    fn spill_word(&mut self, ty: &str, operand: &str) -> String {
        match ty {
            "i64" => operand.to_string(),
            "i32" | "i1" => self.emit(format!("zext {ty} {operand} to i64")),
            "ptr" => self.emit(format!("ptrtoint ptr {operand} to i64")),
            "double" => self.emit(format!("bitcast double {operand} to i64")),
            _ => {
                let bits = self.emit(format!("bitcast float {operand} to i32"));
                self.emit(format!("zext i32 {bits} to i64"))
            }
        }
    }

    fn unspill_word(&mut self, ty: &str, word: &str) -> String {
        match ty {
            "i64" => word.to_string(),
            "i32" | "i1" => self.emit(format!("trunc i64 {word} to {ty}")),
            "ptr" => self.emit(format!("inttoptr i64 {word} to ptr")),
            "double" => self.emit(format!("bitcast i64 {word} to double")),
            _ => {
                let bits = self.emit(format!("trunc i64 {word} to i32"));
                self.emit(format!("bitcast i32 {bits} to float"))
            }
        }
    }

    /// The parameter list of the function being lowered: `fixed` (`ptr %inst`
    /// and the like), then each of `names`, a value's LLVM type and the name its
    /// register is given. A value past the register budget is loaded from the
    /// spill area at the top of the function instead. Returns the list and what
    /// each value is called in the body.
    fn signature(
        &mut self,
        mut fixed: Vec<String>,
        names: &[(&'static str, String)],
    ) -> Result<(String, Vec<String>), EmitError> {
        let tys: Vec<_> = names.iter().map(|(ty, _)| *ty).collect();
        let plan = self.module.spill_plan(fixed.len(), &tys)?;
        let mut operands = Vec::new();
        for ((ty, name), spill) in names.iter().zip(plan) {
            operands.push(match spill {
                None => {
                    fixed.push(format!("{ty} {name}"));
                    name.clone()
                }
                Some(word) => {
                    let at = self.spill_address(word);
                    let loaded = self.emit(format!("load i64, ptr {at}"));
                    self.unspill_word(ty, &loaded)
                }
            });
        }
        self.prologue = std::mem::take(&mut self.body);
        Ok((fixed.join(", "), operands))
    }

    pub(crate) fn lower(mut self) -> Result<String, EmitError> {
        let id = self.id;
        let func = self.func;
        let mut fixed = vec!["ptr %inst".to_string()];
        if let Some(env) = &func.env {
            if id == self.module.program.entry {
                return Err(EmitError::Malformed("the entry function has an env"));
            }
            fixed.push("ptr %env".to_string());
            let ty = MTy::Ptr(HeapKind::Closure(env.sig));
            self.locals
                .insert(env.local, Val::Op(ty, "%env".to_string()));
        }
        let looped = self.module.plan.loops(id);
        let mut names = Vec::new();
        for (local, ty) in &func.params {
            if let Some(llty) = self.module.llty(*ty)? {
                let name = if looped {
                    format!("%in{}", names.len())
                } else {
                    format!("%l{}", local.0)
                };
                names.push((llty, name));
            }
        }
        let (signature, operands) = self.signature(fixed, &names)?;
        let mut operands = operands.into_iter();
        let mut entry = Vec::new();
        for (local, ty) in &func.params {
            let value = if *ty == MTy::Unit {
                Val::Unit
            } else {
                let operand = operands.next().ok_or(EmitError::Malformed("a parameter"))?;
                if looped {
                    entry.push(operand);
                    Val::Op(*ty, format!("%s{}", entry.len() - 1))
                } else {
                    Val::Op(*ty, operand)
                }
            };
            self.locals.insert(*local, value);
        }
        if looped {
            self.looped = Some(Loop {
                slots: names.iter().map(|(ty, _)| *ty).collect(),
                group: None,
                entry,
                entry_which: String::new(),
                edges: Vec::new(),
            });
        }
        self.return_value(func)?;
        let linkage = if id == self.module.program.entry {
            ""
        } else {
            "internal "
        };
        let ret = self.module.ret_ty(func.ret)?;
        let name = self.module.func_name(id);
        self.assemble(&format!("{linkage}tailcc {ret} {name}"), &signature, "")
    }

    pub(crate) fn lower_group(mut self, index: usize) -> Result<String, EmitError> {
        let program = self.module.program;
        let group = &self.module.plan.groups[index];
        let (name, ret, slots) = (group.name.clone(), group.ret, group.slots.clone());
        let members = group.members.clone();
        let mut names = vec![("i32", "%in_which".to_string())];
        names.extend(
            slots
                .iter()
                .enumerate()
                .map(|(i, ty)| (*ty, format!("%in{i}"))),
        );
        let (signature, mut operands) = self.signature(vec!["ptr %inst".to_string()], &names)?;
        let entry_which = operands.remove(0);
        self.looped = Some(Loop {
            slots,
            group: Some(index),
            entry: operands,
            entry_which,
            edges: Vec::new(),
        });
        let labels: Vec<_> = (0..members.len()).map(|i| format!("member.{i}")).collect();
        let last = members.len() - 1;
        let cases: Vec<_> = labels[..last]
            .iter()
            .enumerate()
            .map(|(i, label)| format!("i32 {i}, label %{label}"))
            .collect();
        let dispatch = format!(
            "  switch i32 %which, label %{} [ {} ]\n",
            labels[last],
            cases.join(" ")
        );
        for (i, member) in members.iter().enumerate() {
            let func = &program.funcs[member.0 as usize];
            self.id = *member;
            self.func = func;
            self.locals.clear();
            let assigned = &self.module.plan.groups[index].assigned[i];
            for ((local, ty), slot) in func.params.iter().zip(assigned) {
                let value = match slot {
                    Some(slot) => Val::Op(*ty, format!("%s{slot}")),
                    None => Val::Unit,
                };
                self.locals.insert(*local, value);
            }
            self.start(&labels[i]);
            self.return_value(func)?;
        }
        let ret = self.module.ret_ty(ret)?;
        self.assemble(
            &format!("internal tailcc {ret} {name}"),
            &signature,
            &dispatch,
        )
    }

    /// Lowers `func`'s body and returns what it evaluates to, unless it ended
    /// in a trap, a loop or a tail call.
    fn return_value(&mut self, func: &'a Func) -> Result<(), EmitError> {
        let ret = self.module.ret_ty(func.ret)?;
        match self.expr(&func.body)? {
            Some(Val::Op(_, op)) => self.line(format!("ret {ret} {op}")),
            Some(Val::Unit) => self.line("ret void".to_string()),
            None => {}
        }
        Ok(())
    }

    /// The function: its entry block, then the loop header when there is one,
    /// then the body.
    fn assemble(&self, head: &str, signature: &str, dispatch: &str) -> Result<String, EmitError> {
        let mut out = format!(
            "define {head}({signature}) nounwind {{\nentry:\n{}{}",
            self.allocas, self.prologue
        );
        if let Some(looped) = &self.looped {
            out.push_str("  br label %loop\nloop:\n");
            if looped.group.is_some() {
                let mut incoming = vec![format!("[ {}, %entry ]", looped.entry_which)];
                for edge in &looped.edges {
                    let which = edge.which.expect("a group edge names its member");
                    incoming.push(format!("[ {which}, %{} ]", edge.from));
                }
                let _ = writeln!(out, "  %which = phi i32 {}", incoming.join(", "));
            }
            for (i, ty) in looped.slots.iter().enumerate() {
                let mut incoming = vec![format!("[ {}, %entry ]", looped.entry[i])];
                for edge in &looped.edges {
                    incoming.push(format!("[ {}, %{} ]", edge.values[i], edge.from));
                }
                let _ = writeln!(out, "  %s{i} = phi {ty} {}", incoming.join(", "));
            }
            out.push_str(dispatch);
        }
        out.push_str(&self.body);
        out.push_str("}\n");
        Ok(out)
    }
}
