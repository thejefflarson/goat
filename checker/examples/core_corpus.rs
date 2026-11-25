//! Writes the programs of the differential test (ADR 0037, decision 6), one per
//! line, with what the Rust checker says about each:
//!
//!     MODE <TAB> SEXP <TAB> VERDICT <TAB> SOURCE
//!
//! `proofs/GoatExtract.v` extracts the proven inference algorithm, and
//! `differential/driver.ml` runs it on these lines and fails on any
//! disagreement. See `differential/README.md`.
//!
//! The programs are every goat source the repository holds (`examples/`, the
//! code blocks of `docs/llm.md`, every string literal in the checker's Rust
//! sources and tests) plus generators run at fixed seeds. A program is kept when it is
//! in the fragment of `proofs/goat_ln.ott`: numerals, Float literals, strings,
//! unit, booleans, functions, calls, `if` with an `else`, the twelve binary
//! operators on Int, Float, String and Bool, `and`, `or` and `not` (read as the
//! `if` they are derived forms of: `a and b` is `if a then b else false`,
//! `a or b` is `if a then true else b`, `not a` is `if a then false else true`), `let` of any value, record
//! literals with distinct labels, field access, spread (`{...p, x: v}`) and
//! rest patterns, using only names it binds.
//! The calculus generalizes a `let` of a syntactic value (`is_gen_value` in
//! `proofs/GoatDefs.v`, the checker's `is_syntactic_value`) and types any other
//! `let` monomorphically (`T_LetMono`). Of a value that is neither a function
//! nor a bare numeral, the algorithm leaves the `Literal` variables of its type
//! shared and generalizes the rest, as the checker does (ADR 0038). A function that calls itself, or that
//! belongs to a group of functions that mention each other, is a `letrec` of
//! the group (`T_Letrec`), generalized once the whole group is typed, as the
//! checker does. A group whose functions are not next to each other in their
//! block (a value binding between them) is written as one `letrec`, placed
//! after the last binding its members mention and before the value bindings
//! that use it.
//!
//! The calculus has no implicit Int-to-Float widening: elaboration writes
//! `float(e)` where the checker accepts an Int for a Float (an operand beside a
//! Float operand, each operand of `/`, an argument to a Float parameter, a
//! branch of an `if` whose result is a Float, a numeral inside a comparison). A numeral the checker settled as a Float
//! elsewhere is written bare, which the calculus types at `Float`. This reader
//! inserts the coercions from the checker's node types, so the differential test
//! also checks that those places are exactly where the checker widens. `+ - *`
//! on operands the checker leaves as type variables are generic in the calculus
//! and are compared, a record passed to one included (the calculus applies them
//! to records of numbers field by field). A program is outside the fragment when an operator's
//! operands are not all Int, Float, String or Bool or open numeric variables, when
//! a comparison has an operand that is a parameter's generic type
//! (`differential/README.md`), or when a rest pattern has no fields.
//! Every other program outside the fragment is counted under one `Feature` it
//! uses, the first in that enum's order.
//!
//! A program in which the checker gives some node a recursive type is mode `R`
//! (mode `K` when the recursive type's body holds a record with an open row),
//! and its verdict writes a recursive type as `(mu mK. T)`, `mK` naming the
//! binder by its depth. A field the checker reads as a method (a `program(self)`
//! written directly in a record literal) is written `(meth e)`: the calculus
//! gives the methods of one literal a single receiver (`T_Obj`).
//!
//!     cargo run -q -p goat_checker --example core_corpus > corpus.tsv
//!
//! With `--sources` it writes every source it collected, whether or not it is
//! in the fragment, one per line as decimal code points: the programs the
//! lexer's differential test reads (`parser/examples/lex_dump.rs`).

use goat_checker::captures::for_each_node;
use goat_checker::check_with_prelude;
use goat_checker::hir::{BinOp, Expr, ExprId, ExprKind, MatchArm, Symbol};
use goat_checker::lower::{Lowered, lower, lower_with_prelude};
use goat_checker::ty::{Group, Row, Ty, TypeVar};
use goat_checker::{Checked, ErrorKind};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write;
use std::path::Path;
use std::sync::Arc;

const GENERATED: usize = 4000;
const GENERATED_TYPED: usize = 6000;
const GENERATED_GROUPS: usize = 8000;
const GENERATED_SPREADS: usize = 3000;
const GENERATED_LISTS: usize = 4000;
const TYPED_DEPTH: u32 = 4;
/// Each seed drives all three generators, so a change to one stream cannot
/// hide a mismatch another seed's programs would show.
const SEEDS: [u64; 3] = [
    0x9E37_79B9_7F4A_7C15,
    0xD1B5_4A32_D192_ED03,
    0x2545_F491_4F6C_DD1D,
];
const MAX_DEPTH: u32 = 6;

/// A term of the locally nameless core: a variable is the number of binders
/// between its use and its binder.
enum Core {
    Var(usize),
    Num(i64),
    Float,
    Str(Vec<u8>),
    Unit,
    Bool(bool),
    If(Box<Core>, Box<Core>, Box<Core>),
    Bin(BinOp, Box<Core>, Box<Core>),
    ToFloat(Box<Core>),
    Abs(Box<Core>),
    /// A record field the checker reads as a method.
    Meth(Box<Core>),
    App(Box<Core>, Box<Core>),
    Let(Box<Core>, Box<Core>),
    /// A group of functions under one binder naming the record of them, and
    /// the body that binder scopes over.
    Letrec(Vec<(usize, Core)>, Box<Core>),
    Rec(Vec<(usize, Core)>),
    Proj(Box<Core>, usize),
    /// `{...base, label: value}`: one field, so a spread of several is a nest.
    Spread(Box<Core>, usize, Box<Core>),
    /// `record` with its first `label` taken out.
    Restrict(Box<Core>, usize),
    /// `Tag(args)`: the tag's group, the tag's position, and the values of its
    /// slots (none for a bare tag).
    Con(GroupDecl, usize, Vec<Core>),
    /// The `i`th slot of a tag's payload, which an arm reads off its payload.
    Slot(Box<Core>, usize),
    /// `match`: the group, the scrutinee, each arm by its tag's position (its
    /// body binds the payload as index 0), and the `else`.
    Match(GroupDecl, Box<Core>, Vec<(usize, Core)>, Option<Box<Core>>),
}

fn relabel_fields(fields: &mut [(usize, Core)], rank: &[usize]) {
    for (label, value) in fields {
        *label = rank[*label];
        value.relabel(rank);
    }
}

/// A tag group as the calculus declares it: the number that names it, and the
/// slot codes of each of its tags. Two groups are one type only when both agree.
type GroupDecl = (usize, Vec<Vec<usize>>);

fn group_sexp((name, tags): &GroupDecl, out: &mut String) {
    write!(out, "(grp {name}").unwrap();
    for tag in tags {
        out.push_str(" (");
        let codes: Vec<String> = tag.iter().map(usize::to_string).collect();
        out.push_str(&codes.join(" "));
        out.push(')');
    }
    out.push(')');
}

/// The calculus's slot code of a payload type: 0 the group itself, 1 to 5 Int,
/// Float, Bool, Unit, String, and 6 + j the group's `j`th `_`.
fn slot_code(ty: &Ty, group: &Group) -> Option<usize> {
    match ty {
        Ty::Int => Some(1),
        Ty::Float => Some(2),
        Ty::Bool => Some(3),
        Ty::Unit => Some(4),
        Ty::Str => Some(5),
        Ty::Var(v) if *v == Group::SELF => Some(0),
        Ty::Var(v) if *v < Group::SELF && Group::SELF - 1 - *v < group.params as TypeVar => {
            Some(6 + (Group::SELF - 1 - *v) as usize)
        }
        _ => None,
    }
}

/// The fields of a closed row labelled `"0"`, `"1"`, ... in order, which is how a
/// tag with several values holds them; `None` for any other row.
fn positional_fields(row: &Row) -> Option<Vec<&Ty>> {
    let mut fields = Vec::new();
    let mut at = row;
    loop {
        match at {
            Row::Empty => break,
            Row::Extend {
                label, field, rest, ..
            } => {
                fields.push((label.as_str(), &**field));
                at = rest;
            }
            _ => return None,
        }
    }
    if fields.len() < 2 {
        return None;
    }
    (0..fields.len())
        .map(|i| {
            let label = i.to_string();
            fields.iter().find(|(l, _)| *l == label).map(|(_, ty)| *ty)
        })
        .collect()
}

/// The slot codes of each tag of `group`. A bare tag has none, a tag with one
/// value has one, and a tag with several has one for each positional field.
/// `None` when a payload is a type the calculus has no slot for.
fn group_slots(group: &Group) -> Option<Vec<Vec<usize>>> {
    group
        .tags
        .iter()
        .map(|(_, payload)| match payload {
            Ty::Unit => Some(Vec::new()),
            Ty::Record(row) => positional_fields(row)?
                .into_iter()
                .map(|field| slot_code(field, group))
                .collect(),
            single => Some(vec![slot_code(single, group)?]),
        })
        .collect()
}

fn fields_sexp(fields: &[(usize, Core)], out: &mut String) {
    out.push_str("(rec");
    for (label, value) in fields {
        write!(out, " ({label} ").unwrap();
        value.sexp(out);
        out.push(')');
    }
    out.push(')');
}

impl Core {
    /// Renames every label by `rank`, which maps a label's first-use number to
    /// its number in sorted-name order.
    fn relabel(&mut self, rank: &[usize]) {
        match self {
            Core::Var(_)
            | Core::Num(_)
            | Core::Float
            | Core::Str(_)
            | Core::Unit
            | Core::Bool(_) => {}
            Core::If(a, b, c) => {
                for e in [a, b, c] {
                    e.relabel(rank);
                }
            }
            Core::Bin(_, a, b) | Core::App(a, b) | Core::Let(a, b) => {
                a.relabel(rank);
                b.relabel(rank);
            }
            Core::ToFloat(e) | Core::Abs(e) | Core::Meth(e) => e.relabel(rank),
            Core::Rec(fields) => relabel_fields(fields, rank),
            Core::Letrec(fields, body) => {
                relabel_fields(fields, rank);
                body.relabel(rank);
            }
            Core::Proj(e, label) | Core::Restrict(e, label) => {
                *label = rank[*label];
                e.relabel(rank);
            }
            Core::Spread(base, label, value) => {
                *label = rank[*label];
                base.relabel(rank);
                value.relabel(rank);
            }
            Core::Con(_, _, slots) => {
                for slot in slots {
                    slot.relabel(rank);
                }
            }
            Core::Slot(e, _) => e.relabel(rank),
            Core::Match(_, scrutinee, arms, otherwise) => {
                scrutinee.relabel(rank);
                for (_, body) in arms {
                    body.relabel(rank);
                }
                if let Some(body) = otherwise {
                    body.relabel(rank);
                }
            }
        }
    }

    fn sexp(&self, out: &mut String) {
        match self {
            Core::Var(i) => write!(out, "(b {i})").unwrap(),
            Core::Num(n) => write!(out, "(n {n})").unwrap(),
            Core::Float => out.push_str("(d 0)"),
            Core::Unit => out.push('u'),
            Core::Str(bytes) => {
                out.push_str("(str");
                for byte in bytes {
                    write!(out, " {byte}").unwrap();
                }
                out.push(')');
            }
            Core::If(c, a, b) => {
                out.push_str("(if ");
                c.sexp(out);
                out.push(' ');
                a.sexp(out);
                out.push(' ');
                b.sexp(out);
                out.push(')');
            }
            Core::Bin(op, a, b) => {
                write!(out, "(bin {} ", bop_atom(*op)).unwrap();
                a.sexp(out);
                out.push(' ');
                b.sexp(out);
                out.push(')');
            }
            Core::ToFloat(e) => {
                out.push_str("(float ");
                e.sexp(out);
                out.push(')');
            }
            Core::Bool(true) => out.push('t'),
            Core::Bool(false) => out.push('f'),
            Core::Abs(body) => {
                out.push_str("(abs ");
                body.sexp(out);
                out.push(')');
            }
            Core::Meth(body) => {
                out.push_str("(meth ");
                body.sexp(out);
                out.push(')');
            }
            Core::App(f, a) => {
                out.push_str("(app ");
                f.sexp(out);
                out.push(' ');
                a.sexp(out);
                out.push(')');
            }
            Core::Let(v, b) => {
                out.push_str("(let ");
                v.sexp(out);
                out.push(' ');
                b.sexp(out);
                out.push(')');
            }
            Core::Rec(fields) => fields_sexp(fields, out),
            Core::Letrec(fields, body) => {
                out.push_str("(letrec ");
                fields_sexp(fields, out);
                out.push(' ');
                body.sexp(out);
                out.push(')');
            }
            Core::Proj(e, label) => {
                out.push_str("(proj ");
                e.sexp(out);
                write!(out, " {label})").unwrap();
            }
            Core::Spread(base, label, value) => {
                out.push_str("(spread ");
                base.sexp(out);
                write!(out, " {label} ").unwrap();
                value.sexp(out);
                out.push(')');
            }
            Core::Restrict(record, label) => {
                out.push_str("(restrict ");
                record.sexp(out);
                write!(out, " {label})").unwrap();
            }
            Core::Con(group, tag, slots) => {
                out.push_str("(con ");
                group_sexp(group, out);
                write!(out, " {tag} ").unwrap();
                if slots.is_empty() {
                    out.push('u');
                } else {
                    out.push_str("(rec");
                    for (i, slot) in slots.iter().enumerate() {
                        write!(out, " ({i} ").unwrap();
                        slot.sexp(out);
                        out.push(')');
                    }
                    out.push(')');
                }
                out.push(')');
            }
            Core::Slot(e, i) => {
                out.push_str("(proj ");
                e.sexp(out);
                write!(out, " {i})").unwrap();
            }
            Core::Match(group, scrutinee, arms, otherwise) => {
                out.push_str("(match ");
                group_sexp(group, out);
                out.push(' ');
                scrutinee.sexp(out);
                for (tag, body) in arms {
                    write!(out, " ({tag} ").unwrap();
                    body.sexp(out);
                    out.push(')');
                }
                if let Some(body) = otherwise {
                    out.push_str(" (else ");
                    body.sexp(out);
                    out.push(')');
                }
                out.push(')');
            }
        }
    }
}

/// What a program outside the calculus uses that the calculus lacks. A program
/// that uses several is counted under the first in this order, which is the
/// order of the proof phases that will bring each in: a count falls to 0 when
/// its phase lands, and its programs then show up under the next feature they
/// use, or are compared.
#[derive(Clone, Debug, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Feature {
    ForeignCall,
    TagsAndMatch,
    Builtin,
    OperatorOperand,
    EmptyRest,
    UnwritableType,
    LargeNumeral,
    Other,
}

impl Feature {
    fn describe(self) -> &'static str {
        match self {
            Feature::ForeignCall => "outside the calculus: a foreign host call",
            Feature::TagsAndMatch => "outside the calculus: tags and match",
            Feature::Builtin => "outside the calculus: print or trap",
            Feature::OperatorOperand => {
                "outside the calculus: arithmetic on non-primitive operands"
            }
            Feature::EmptyRest => {
                "outside the calculus: a rest pattern with no fields, which only says its source is a record"
            }
            Feature::UnwritableType => {
                "outside the calculus: an inferred type the corpus cannot write"
            }
            Feature::LargeNumeral => "outside the calculus: a numeral of 2^30 or more",
            Feature::Other => "outside the calculus: none of the above",
        }
    }
}

/// The first feature, in `Feature` order, that `lowered` uses.
fn feature_of(lowered: &Lowered, checked: Option<&Checked>, gap: Feature) -> Feature {
    let mut first = gap;
    let mut note = |feature: Feature| first = first.min(feature);
    let types = checked.map(|c| &c.typed.node_types);
    let non_primitive = |e: &Expr| {
        types
            .and_then(|t| t.get(&e.id))
            .is_some_and(|t| !matches!(t, Ty::Int | Ty::Float | Ty::Str | Ty::Bool | Ty::Var(_)))
    };
    for_each_node(&lowered.root, &mut |e| match &e.kind {
        ExprKind::Foreign { .. } => note(Feature::ForeignCall),
        ExprKind::Int(n) if n.unsigned_abs() >= 1 << 30 => note(Feature::LargeNumeral),
        ExprKind::Tag { .. } | ExprKind::Match { .. } => note(Feature::TagsAndMatch),
        ExprKind::Builtin(_) | ExprKind::Trap(_) => note(Feature::Builtin),
        ExprKind::Bin {
            op: BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::FloorDiv | BinOp::Mod,
            lhs,
            rhs,
        } if non_primitive(lhs) || non_primitive(rhs) => note(Feature::OperatorOperand),
        _ => {}
    });
    first
}

/// Why a program is left out of the differential test.
#[derive(Clone, Debug, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Skip {
    Rejected,
    OutsideFragment(Feature),
    MethodFlag,
    ResourceLimit,
}

impl Skip {
    pub fn describe(self) -> &'static str {
        match self {
            Skip::Rejected => "does not lower",
            Skip::OutsideFragment(feature) => feature.describe(),
            Skip::MethodFlag => {
                "the checker rejects a method used as a plain function or the reverse"
            }
            Skip::ResourceLimit => "the checker gives up on a program too complex",
        }
    }
}

fn bop_atom(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::Div => "div",
        BinOp::FloorDiv => "fdiv",
        BinOp::Mod => "rem",
        BinOp::Lt => "lt",
        BinOp::Lte => "lte",
        BinOp::Gt => "gt",
        BinOp::Gte => "gte",
        BinOp::Eq => "eq",
        BinOp::Ne => "ne",
    }
}

/// Reads lowered HIR as a core term, or says it is outside the fragment.
struct Reader<'a> {
    labels: Vec<String>,
    scope: Vec<Binder>,
    /// Cleared when a function or call has more than one parameter or argument,
    /// and, in a rejected program, when one has none: the reader cannot tell a
    /// call that matches the arity from one the checker refuses for it.
    unary: bool,
    /// The checker's node types when it accepted the program; a rejected
    /// program has none, so it is read without coercions.
    types: Option<&'a HashMap<ExprId, Ty>>,
    /// How many comparison operands the reader is inside.
    in_comparison: usize,
    /// The symbols of function parameters. A `let` of one (a record pattern
    /// binds its source so) holds no numeral the calculus could generalize.
    /// Why the reader stopped, when the cause is the shape of the program and
    /// not a node the calculus lacks.
    gap: Feature,
    /// The tag groups read so far; a group's position is its name.
    groups: Vec<Arc<Group>>,
}

/// What a name in scope is bound by: a parameter or `let`, one binder; or a
/// group of functions, which share one binder naming the record of them, each
/// reached by the label it has in that record.
enum Binder {
    Bound(Symbol),
    Group(Vec<(Symbol, usize)>),
}

/// One step of a block once its groups are placed: a value binding, by its
/// position in the block, or a group, by its position among the block's groups.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Unit {
    Value(usize),
    Group(usize),
}

/// How the checker settles a block's function bindings into groups. `mentions[m]`
/// holds the other members that member `m` mentions. The checker infers the
/// members in order and generalizes a member only once every member it is
/// connected to, through what either mentions among the members not yet
/// generalized, has been inferred; a group is those members, in the order the
/// checker generalizes them.
fn function_groups(mentions: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut pending = vec![true; mentions.len()];
    let mut inferred: Vec<usize> = Vec::new();
    let mut groups = Vec::new();
    for member in 0..mentions.len() {
        inferred.push(member);
        let mut group = vec![member];
        let mut at = 0;
        while at < group.len() {
            let current = group[at];
            at += 1;
            if inferred.contains(&current) {
                for &used in &mentions[current] {
                    if pending[used] && !group.contains(&used) {
                        group.push(used);
                    }
                }
            }
            for &other in &inferred {
                if mentions[other].contains(&current) && !group.contains(&other) {
                    group.push(other);
                }
            }
        }
        if group.iter().all(|m| inferred.contains(m)) {
            group.sort_unstable();
            for &m in &group {
                pending[m] = false;
            }
            inferred.retain(|m| !group.contains(m));
            groups.push(group);
        }
    }
    groups
}

impl Reader<'_> {
    fn label(&mut self, name: &str) -> usize {
        match self.labels.iter().position(|l| l == name) {
            Some(at) => at,
            None => {
                self.labels.push(name.to_string());
                self.labels.len() - 1
            }
        }
    }

    /// Renumbers the labels in name order, so the calculus's `nat` order on
    /// labels is the checker's alphabetical one and a record comparison
    /// agrees between the two.
    fn number_labels_by_name(&mut self, core: &mut Core) {
        let mut sorted = self.labels.clone();
        sorted.sort();
        let rank: Vec<usize> = self
            .labels
            .iter()
            .map(|l| sorted.binary_search(l).unwrap())
            .collect();
        core.relabel(&rank);
        self.labels = sorted;
    }

    fn node_ty(&self, expr: &Expr) -> Option<&Ty> {
        self.types?.get(&expr.id)
    }

    /// The type of an operator's operand, which must be one the calculus has
    /// an operator signature for. A comparison or a division also takes `Unit`
    /// and a record, when both operands have one type, so no field needs a
    /// coercion.
    fn operand_ty(&self, expr: &Expr, other: &Expr, same_type: bool) -> Option<Ty> {
        match self.node_ty(expr)? {
            ty @ (Ty::Int | Ty::Float | Ty::Str | Ty::Bool) => Some(ty.clone()),
            ty @ (Ty::Unit | Ty::Record(_)) if same_type && self.node_ty(other) == Some(ty) => {
                Some(ty.clone())
            }
            _ => None,
        }
    }

    /// The core term for a use of the variable bound as `symbol`, or `None`
    /// when no binder in scope binds it. It looks up by symbol, not by name,
    /// because a hoisted group can sit past a binding that reuses a name a
    /// member reads from further out.
    fn var(&self, symbol: &Symbol) -> Option<Core> {
        for (depth, binder) in self.scope.iter().rev().enumerate() {
            match binder {
                Binder::Bound(s) if s == symbol => return Some(Core::Var(depth)),
                Binder::Group(members) => {
                    if let Some((_, label)) = members.iter().find(|(s, _)| s == symbol) {
                        return Some(Core::Proj(Box::new(Core::Var(depth)), *label));
                    }
                }
                Binder::Bound(_) => {}
            }
        }
        None
    }

    /// A chain of `let`s and its result. A `program` binding that mentions
    /// itself, or belongs to a group with another, is a `letrec`; the others
    /// are `let`s. A group is placed after the last binding its members
    /// mention, which is where elaboration hoists it past value bindings that
    /// split it; the checker infers the group there too.
    fn block(&mut self, first: &Expr) -> Option<Core> {
        let mut bindings = Vec::new();
        let mut cursor = Some(first);
        while let Some(ExprKind::Let {
            symbol,
            name,
            value,
            rest,
        }) = cursor.map(|c| &c.kind)
        {
            bindings.push((*symbol, name.as_str(), &**value));
            cursor = rest.as_deref();
        }
        let tail = cursor;
        let members: Vec<usize> = (0..bindings.len())
            .filter(|&i| matches!(bindings[i].2.kind, ExprKind::Func { .. }))
            .collect();
        let used: Vec<HashSet<Symbol>> = bindings
            .iter()
            .map(|&(.., value)| {
                let mut used = HashSet::new();
                for_each_node(value, &mut |e| {
                    if let ExprKind::Var { symbol, .. } = &e.kind {
                        used.insert(*symbol);
                    }
                });
                used
            })
            .collect();
        let symbols: Vec<Symbol> = members.iter().map(|&i| bindings[i].0).collect();
        let mentions: Vec<Vec<usize>> = members
            .iter()
            .map(|&i| {
                (0..members.len())
                    .filter(|&m| symbols[m] != bindings[i].0 && used[i].contains(&symbols[m]))
                    .collect()
            })
            .collect();
        let groups: Vec<Vec<usize>> = function_groups(&mentions)
            .into_iter()
            .filter(|group| group.len() > 1 || used[members[group[0]]].contains(&symbols[group[0]]))
            .map(|group| group.into_iter().map(|m| members[m]).collect())
            .collect();
        let units = self.place_groups(&bindings, &used, &groups)?;
        self.chain(&bindings, &groups, &units, tail)
    }

    /// The order of a block's bindings and groups: the value bindings in
    /// source order, each group directly after the last binding or group its
    /// members mention. `None` when a binding needs a group whose own
    /// dependencies come later, which the checker rejects.
    fn place_groups(
        &mut self,
        bindings: &[(Symbol, &str, &Expr)],
        used: &[HashSet<Symbol>],
        groups: &[Vec<usize>],
    ) -> Option<Vec<Unit>> {
        let grouped: HashSet<usize> = groups.iter().flatten().copied().collect();
        let owner = |symbol: &Symbol| {
            let at = bindings.iter().position(|b| b.0 == *symbol)?;
            Some(match groups.iter().position(|g| g.contains(&at)) {
                Some(g) => Unit::Group(g),
                None => Unit::Value(at),
            })
        };
        let needs = |at: usize| used[at].iter().filter_map(&owner).collect::<Vec<_>>();
        let group_needs: Vec<Vec<Unit>> = groups
            .iter()
            .enumerate()
            .map(|(g, members)| {
                let mut needed: Vec<Unit> = members.iter().flat_map(|&at| needs(at)).collect();
                needed.retain(|u| *u != Unit::Group(g));
                needed
            })
            .collect();
        let mut units = Vec::new();
        let done = |units: &mut Vec<Unit>| {
            while let Some(g) = (0..groups.len()).find(|&g| {
                !units.contains(&Unit::Group(g)) && group_needs[g].iter().all(|u| units.contains(u))
            }) {
                units.push(Unit::Group(g));
            }
        };
        done(&mut units);
        for i in (0..bindings.len()).filter(|i| !grouped.contains(i)) {
            if !needs(i).iter().all(|u| units.contains(u)) {
                return None;
            }
            units.push(Unit::Value(i));
            done(&mut units);
        }
        if units.len() != groups.len() + bindings.len() - grouped.len() {
            return None;
        }
        Some(units)
    }

    fn chain(
        &mut self,
        bindings: &[(Symbol, &str, &Expr)],
        groups: &[Vec<usize>],
        units: &[Unit],
        tail: Option<&Expr>,
    ) -> Option<Core> {
        let Some((unit, units)) = units.split_first() else {
            return match tail {
                Some(tail) => self.read(tail),
                None => self.var(&bindings.last()?.0),
            };
        };
        let group = match *unit {
            Unit::Value(at) => {
                let (symbol, _, value) = bindings[at];
                let value = self.read(value)?;
                self.scope.push(Binder::Bound(symbol));
                let body = self.chain(bindings, groups, units, tail);
                self.scope.pop();
                return Some(Core::Let(Box::new(value), Box::new(body?)));
            }
            Unit::Group(g) => &groups[g],
        };
        let members: Vec<(Symbol, usize)> = group
            .iter()
            .map(|&i| {
                let (symbol, name, _) = bindings[i];
                (symbol, self.label(name))
            })
            .collect();
        self.scope.push(Binder::Group(members));
        let fields: Option<Vec<(usize, Core)>> = group
            .iter()
            .map(|&i| {
                let label = self.label(bindings[i].1);
                Some((label, self.read(bindings[i].2)?))
            })
            .collect();
        let body = fields.and_then(|fields| {
            let body = self.chain(bindings, groups, units, tail)?;
            Some(Core::Letrec(fields, Box::new(body)))
        });
        self.scope.pop();
        body
    }

    /// `group` as the calculus declares it: numbered by first use, so two
    /// groups of one shape stay two.
    fn group_decl(&mut self, group: &Arc<Group>) -> Option<GroupDecl> {
        let slots = group_slots(group)?;
        let name = match self.groups.iter().position(|g| Arc::ptr_eq(g, group)) {
            Some(name) => name,
            None => {
                self.groups.push(group.clone());
                self.groups.len() - 1
            }
        };
        Some((name, slots))
    }

    /// `Tag(a, b)` is the tag with a record of its slots, an `Int` made a
    /// `Float` where the slot is one.
    fn tag(&mut self, name: &str, payload: Option<&Expr>, group: &Arc<Group>) -> Option<Core> {
        let decl = self.group_decl(group)?;
        let slots = &decl.1;
        let tag = group.tags.iter().position(|(n, _)| n == name)?;
        let values: Vec<&Expr> = match (payload, slots[tag].len()) {
            (None, 0) => Vec::new(),
            (Some(only), 1) => vec![only],
            (Some(record), n) if n > 1 => match &record.kind {
                ExprKind::Record { fields } if fields.len() == n => {
                    fields.iter().map(|(_, value)| value).collect()
                }
                _ => return None,
            },
            _ => return None,
        };
        let mut read = Vec::new();
        for (value, code) in values.into_iter().zip(&slots[tag]) {
            let mut core = self.read(value)?;
            if *code == 2 && self.node_ty(value) == Some(&Ty::Int) {
                core = Core::ToFloat(Box::new(core));
            }
            read.push(core);
        }
        Some(Core::Con(decl, tag, read))
    }

    /// What lowering's `Trap` is to the calculus: `letrec f = program(x) do f(x) done in f()`,
    /// a term of every type that never returns, as the checker types a trap.
    fn diverge(&mut self) -> Core {
        let label = self.label("@trap");
        let call = |depth| Core::Proj(Box::new(Core::Var(depth)), label);
        let step = Core::App(Box::new(call(1)), Box::new(Core::Var(0)));
        Core::Letrec(
            vec![(label, Core::Abs(Box::new(step)))],
            Box::new(Core::App(Box::new(call(0)), Box::new(Core::Unit))),
        )
    }

    /// Each arm binds the payload as one variable and each name as a `let` of
    /// its slot, in the arm's body; the `else` binds nothing.
    fn match_arms(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        else_branch: Option<&Expr>,
    ) -> Option<Core> {
        let group = arms.first()?.pattern.group.as_ref()?;
        let decl = self.group_decl(group)?;
        let slots = &decl.1;
        let scrutinee = self.read(scrutinee)?;
        let mut read = Vec::new();
        for arm in arms {
            if !arm
                .pattern
                .group
                .as_ref()
                .is_some_and(|g| Arc::ptr_eq(g, group))
            {
                return None;
            }
            let tag = group.tags.iter().position(|(n, _)| *n == arm.pattern.tag)?;
            let binders: Vec<_> = arm.pattern.payload.binders().collect();
            if binders.len() > slots[tag].len() {
                return None;
            }
            let mark = self.scope.len();
            self.scope.push(Binder::Bound(Symbol::MAX));
            self.scope
                .extend(binders.iter().map(|p| Binder::Bound(p.symbol)));
            let body = self.read(&arm.body);
            self.scope.truncate(mark);
            let body = (0..binders.len()).rev().fold(body?, |body, i| {
                Core::Let(
                    Box::new(Core::Slot(Box::new(Core::Var(i)), i)),
                    Box::new(body),
                )
            });
            read.push((tag, body));
        }
        let otherwise = match else_branch {
            Some(Expr {
                kind: ExprKind::Trap(_),
                ..
            }) => Some(Box::new(self.diverge())),
            Some(body) => Some(Box::new(self.read(body)?)),
            None => None,
        };
        Some(Core::Match(decl, Box::new(scrutinee), read, otherwise))
    }

    fn read(&mut self, expr: &Expr) -> Option<Core> {
        match &expr.kind {
            ExprKind::Int(n) => {
                let num = Some(*n)
                    .filter(|n| n.unsigned_abs() < 1 << 30)
                    .map(Core::Num)?;
                match self.node_ty(expr) {
                    Some(Ty::Float) if self.in_comparison > 0 => Some(Core::ToFloat(Box::new(num))),
                    _ => Some(num),
                }
            }
            ExprKind::Float(_) => Some(Core::Float),
            ExprKind::Str(text) => Some(Core::Str(text.bytes().collect())),
            ExprKind::Unit => Some(Core::Unit),
            ExprKind::Bool(b) => Some(Core::Bool(*b)),
            ExprKind::If {
                cond,
                then_branch,
                else_branch: Some(else_branch),
            } => {
                let result = self.node_ty(expr) == Some(&Ty::Float);
                let branch = |this: &mut Self, branch: &Expr| {
                    let value = this.read(branch)?;
                    let widens = result && this.node_ty(branch) == Some(&Ty::Int);
                    Some(if widens {
                        Core::ToFloat(Box::new(value))
                    } else {
                        value
                    })
                };
                Some(Core::If(
                    Box::new(self.read(cond)?),
                    Box::new(branch(self, then_branch)?),
                    Box::new(branch(self, else_branch)?),
                ))
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch: None,
            } => Some(Core::If(
                Box::new(self.read(cond)?),
                Box::new(self.read(then_branch)?),
                Box::new(Core::Unit),
            )),
            ExprKind::And { lhs, rhs } => Some(Core::If(
                Box::new(self.read(lhs)?),
                Box::new(self.read(rhs)?),
                Box::new(Core::Bool(false)),
            )),
            ExprKind::Or { lhs, rhs } => Some(Core::If(
                Box::new(self.read(lhs)?),
                Box::new(Core::Bool(true)),
                Box::new(self.read(rhs)?),
            )),
            ExprKind::Not(operand) => Some(Core::If(
                Box::new(self.read(operand)?),
                Box::new(Core::Bool(false)),
                Box::new(Core::Bool(true)),
            )),
            ExprKind::Bin { op, lhs, rhs } => {
                let comparison = matches!(
                    op,
                    BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte | BinOp::Eq | BinOp::Ne
                );
                self.in_comparison += usize::from(comparison);
                let operands = (self.read(lhs), self.read(rhs));
                self.in_comparison -= usize::from(comparison);
                let (mut a, mut b) = (operands.0?, operands.1?);
                if self.types.is_some() {
                    let to_float = |c: Core| Core::ToFloat(Box::new(c));
                    let generic = (comparison
                        || matches!(
                            op,
                            BinOp::Add
                                | BinOp::Sub
                                | BinOp::Mul
                                | BinOp::Div
                                | BinOp::FloorDiv
                                | BinOp::Mod
                        ))
                        && [lhs, rhs]
                            .iter()
                            .any(|e| matches!(self.node_ty(e), Some(Ty::Var(_))));
                    if !generic {
                        let division = *op == BinOp::Div;
                        let (x, y) = (
                            self.operand_ty(lhs, rhs, comparison || division)?,
                            self.operand_ty(rhs, lhs, comparison || division)?,
                        );
                        match (op, x, y) {
                            (BinOp::Div, Ty::Record(_), _) | (BinOp::Div, _, Ty::Record(_)) => {}
                            (BinOp::Div, ..) => (a, b) = (to_float(a), to_float(b)),
                            (_, Ty::Int, Ty::Int)
                                if !comparison && self.node_ty(expr) == Some(&Ty::Float) =>
                            {
                                (a, b) = (to_float(a), to_float(b));
                            }
                            (_, Ty::Int, Ty::Float) => a = to_float(a),
                            (_, Ty::Float, Ty::Int) => b = to_float(b),
                            _ => {}
                        }
                    }
                }
                Some(Core::Bin(*op, Box::new(a), Box::new(b)))
            }
            ExprKind::Var { symbol, .. } => self.var(symbol),
            ExprKind::Func { params, body } if params.is_empty() => {
                self.unary &= self.types.is_some();
                let mark = self.scope.len();
                self.scope.push(Binder::Bound(Symbol::MAX));
                self.scope.push(Binder::Bound(Symbol::MAX));
                let body = self.read(body);
                self.scope.truncate(mark);
                let pin = Core::Bin(BinOp::Eq, Box::new(Core::Var(0)), Box::new(Core::Unit));
                Some(Core::Abs(Box::new(Core::Let(
                    Box::new(pin),
                    Box::new(body?),
                ))))
            }
            ExprKind::Func { params, body } => {
                self.unary &= params.len() == 1;
                let mark = self.scope.len();
                self.scope
                    .extend(params.iter().map(|p| Binder::Bound(p.symbol)));
                let body = self.read(body);
                self.scope.truncate(mark);
                Some(
                    params
                        .iter()
                        .fold(body?, |body, _| Core::Abs(Box::new(body))),
                )
            }
            ExprKind::App { callee, args } if args.is_empty() => {
                self.unary &= self.types.is_some();
                Some(Core::App(
                    Box::new(self.read(callee)?),
                    Box::new(Core::Unit),
                ))
            }
            ExprKind::App { callee, args } => {
                self.unary &= args.len() == 1;
                let params = match self.node_ty(callee) {
                    Some(Ty::Func(params, _)) if params.len() == args.len() => Some(params.clone()),
                    _ => None,
                };
                let callee = self.read(callee)?;
                args.iter()
                    .enumerate()
                    .try_fold(callee, |callee, (i, arg)| {
                        let mut value = self.read(arg)?;
                        if let Some(params) = &params
                            && params[i] == Ty::Float
                            && self.node_ty(arg) == Some(&Ty::Int)
                        {
                            value = Core::ToFloat(Box::new(value));
                        }
                        Some(Core::App(Box::new(callee), Box::new(value)))
                    })
            }
            ExprKind::Let { .. } => self.block(expr),
            ExprKind::Record { fields } => {
                let mut seen = Vec::new();
                let mut out = Vec::new();
                for (label, value) in fields {
                    if seen.contains(label) {
                        return None;
                    }
                    seen.push(label.clone());
                    let label = self.label(label);
                    let body = self.read(value)?;
                    out.push((
                        label,
                        if is_method(value) {
                            Core::Meth(Box::new(body))
                        } else {
                            body
                        },
                    ));
                }
                Some(Core::Rec(out))
            }
            ExprKind::Field { record, label } => {
                let base = self.read(record)?;
                Some(Core::Proj(Box::new(base), self.label(label)))
            }
            ExprKind::Spread { base, fields } => {
                fields
                    .iter()
                    .try_fold(self.read(base)?, |base, (label, value)| {
                        let label = self.label(label);
                        Some(Core::Spread(
                            Box::new(base),
                            label,
                            Box::new(self.read(value)?),
                        ))
                    })
            }
            ExprKind::Tag {
                name,
                payload,
                group: Some(group),
            } => self.tag(name, payload.as_deref(), group),
            ExprKind::Match {
                scrutinee,
                arms,
                else_branch,
            } => self.match_arms(scrutinee, arms, else_branch.as_deref()),
            ExprKind::Restrict { record, labels } => {
                if labels.is_empty() {
                    self.gap = self.gap.min(Feature::EmptyRest);
                    return None;
                }
                labels.iter().try_fold(self.read(record)?, |record, label| {
                    Some(Core::Restrict(Box::new(record), self.label(label)))
                })
            }
            _ => None,
        }
    }
}

/// The type in the driver's canonical form: functions curried, record fields in
/// label order, variables numbered by first occurrence. `None` outside the
/// fragment's types.
struct Canon<'a> {
    labels: &'a [String],
    groups: &'a [Arc<Group>],
    vars: Vec<u32>,
    binders: Vec<u32>,
    open_in_rec: bool,
}

impl Canon<'_> {
    fn var(&mut self, v: u32) -> usize {
        match self.vars.iter().position(|w| *w == v) {
            Some(at) => at,
            None => {
                self.vars.push(v);
                self.vars.len() - 1
            }
        }
    }

    fn ty(&mut self, ty: &Ty, out: &mut String) -> Option<()> {
        match ty {
            Ty::Int => out.push_str("Number"),
            Ty::Float => out.push_str("Float"),
            Ty::Str => out.push_str("String"),
            Ty::Unit => out.push_str("Unit"),
            Ty::Bool => out.push_str("Bool"),
            Ty::Var(v) => match self.binders.iter().rposition(|b| b == v) {
                Some(depth) => write!(out, "m{depth}").unwrap(),
                None => write!(out, "v{}", self.var(*v)).unwrap(),
            },
            Ty::Variant(_) => self.group(ty, None, out)?,
            Ty::Rec(binder, body) if matches!(&**body, Ty::Variant(_)) => {
                self.group(body, Some(*binder), out)?
            }
            Ty::Rec(binder, body) => {
                write!(out, "(mu m{}. ", self.binders.len()).unwrap();
                self.binders.push(*binder);
                let written = self.ty(body, out);
                self.binders.pop();
                written?;
                out.push(')');
            }
            Ty::Func(params, ret) if params.is_empty() => {
                out.push_str("(Unit -> ");
                self.ty(ret, out)?;
                out.push(')');
            }
            Ty::Func(params, ret) => {
                for param in params {
                    out.push('(');
                    self.ty(param, out)?;
                    out.push_str(" -> ");
                }
                self.ty(ret, out)?;
                out.extend(std::iter::repeat_n(')', params.len()));
            }
            Ty::Record(row) => {
                let mut fields = Vec::new();
                let mut at = row;
                let tail = loop {
                    match at {
                        Row::Empty => break None,
                        Row::Var(v) => break Some(*v),
                        Row::Extend {
                            label, field, rest, ..
                        } => {
                            let id = self.labels.iter().position(|l| l == label)?;
                            fields.push((id, None, &**field));
                            at = rest;
                        }
                        Row::Maybe {
                            label,
                            pres,
                            field,
                            rest,
                            ..
                        } => {
                            let id = self.labels.iter().position(|l| l == label)?;
                            fields.push((id, Some(*pres), &**field));
                            at = rest;
                        }
                    }
                };
                fields.sort_by_key(|(id, ..)| *id);
                self.open_in_rec |= tail.is_some() && !self.binders.is_empty();
                out.push('{');
                for (i, (id, pres, field)) in fields.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    write!(out, "l{id}").unwrap();
                    if let Some(pres) = pres {
                        write!(out, "^v{}", self.var(*pres)).unwrap();
                    }
                    out.push_str(": ");
                    self.ty(field, out)?;
                }
                if let Some(v) = tail {
                    out.push_str(if fields.is_empty() { "| " } else { " | " });
                    write!(out, "v{}", self.var(v)).unwrap();
                }
                out.push('}');
            }
        }
        Some(())
    }

    /// A declared group's closed type as `(grp N T0 T1 ...)`: the group's
    /// number and the types in its parameter slots. The group's own recursion
    /// is not written, as the calculus's group type has no binder for it; a
    /// `binder` a parameter mentions (`f = program(x) do Wrap(f(x)) done`) is
    /// written as the `mu` around the group.
    fn group(&mut self, ty: &Ty, binder: Option<TypeVar>, out: &mut String) -> Option<()> {
        let Ty::Variant(row) = ty else { return None };
        let tags = closed_fields(row)?;
        let (name, group) = self.groups.iter().enumerate().find(|(_, g)| {
            g.tags.len() == tags.len()
                && g.tags.iter().all(|(t, _)| tags.iter().any(|(l, _)| l == t))
        })?;
        let mut params = vec![None; group.params];
        for (tag, pattern) in &group.tags {
            let actual = tags.iter().find(|(l, _)| l == tag)?.1;
            read_params(pattern, actual, &mut params);
        }
        let params = params.into_iter().collect::<Option<Vec<_>>>()?;
        let knot = binder.filter(|b| {
            params.iter().any(|p| {
                let mut free = BTreeSet::new();
                p.free_vars(&mut free);
                free.contains(b)
            })
        });
        if let Some(binder) = knot {
            write!(out, "(mu m{}. ", self.binders.len()).unwrap();
            self.binders.push(binder);
        }
        write!(out, "(grp {name}").unwrap();
        let mut written = Some(());
        for param in params {
            out.push(' ');
            written = written.and_then(|()| self.ty(param, out));
        }
        out.push(')');
        if knot.is_some() {
            self.binders.pop();
            out.push(')');
        }
        written
    }
}

/// The fields of a closed row, in order; `None` when it is open or has a
/// presence entry.
fn closed_fields(row: &Row) -> Option<Vec<(&str, &Ty)>> {
    let mut fields = Vec::new();
    let mut at = row;
    loop {
        match at {
            Row::Empty => return Some(fields),
            Row::Extend {
                label, field, rest, ..
            } => {
                fields.push((label.as_str(), &**field));
                at = rest;
            }
            _ => return None,
        }
    }
}

/// The parts of `actual` that stand where `pattern`, a tag's payload type in a
/// group, holds one of the group's parameters.
fn read_params<'a>(pattern: &Ty, actual: &'a Ty, params: &mut [Option<&'a Ty>]) {
    match (pattern, actual) {
        (&Ty::Var(v), _) if v < Group::SELF && Group::SELF - 1 - v < params.len() as TypeVar => {
            params[(Group::SELF - 1 - v) as usize].get_or_insert(actual);
        }
        (Ty::Record(wanted), Ty::Record(given)) => {
            if let (Some(wanted), Some(given)) = (closed_fields(wanted), closed_fields(given)) {
                for (label, field) in wanted {
                    if let Some((_, part)) = given.iter().find(|(l, _)| *l == label) {
                        read_params(field, part, params);
                    }
                }
            }
        }
        _ => {}
    }
}

/// Whether `expr` is a function whose first parameter is `self`, which is what
/// the checker reads as a method when it is a field of a record literal.
fn is_method(expr: &Expr) -> bool {
    matches!(&expr.kind, ExprKind::Func { params, .. }
        if params.first().is_some_and(|p| p.name == "self"))
}

/// What the real prelude declares of lists, for a program that writes `[a, ...r]`
/// or `[x, y]` without declaring the tags itself.
const LIST_PRELUDE: &str = "tag List = Empty | Link(_, List)\n";

/// The line for `source`, or why it is not a program of the fragment.
pub fn line(source: &str) -> Result<String, Skip> {
    let (lowered, prelude) = match lower(source) {
        Ok(lowered) if lowered.errors.is_empty() => (lowered, ""),
        _ => (
            lower_with_prelude(LIST_PRELUDE, source).map_err(|_| Skip::Rejected)?,
            LIST_PRELUDE,
        ),
    };
    if !lowered.errors.is_empty() {
        return Err(Skip::Rejected);
    }
    let checked = check_with_prelude(prelude, source);
    let errors = checked.as_ref().err();
    let flagged = |kind| errors.is_some_and(|es| es.iter().any(|e| e.kind == kind));
    let (method_flag, resource_limit) = (
        flagged(ErrorKind::MethodFlag),
        flagged(ErrorKind::ResourceLimit),
    );
    let checked = checked.ok();
    let mut reader = Reader {
        labels: Vec::new(),
        scope: Vec::new(),
        unary: true,
        types: checked.as_ref().map(|c| &c.typed.node_types),
        in_comparison: 0,
        gap: Feature::Other,
        groups: Vec::new(),
    };
    let mut core = reader
        .read(&lowered.root)
        .ok_or_else(|| Skip::OutsideFragment(feature_of(&lowered, checked.as_ref(), reader.gap)))?;
    reader.number_labels_by_name(&mut core);
    if resource_limit {
        return Err(Skip::ResourceLimit);
    }
    if method_flag {
        return Err(Skip::MethodFlag);
    }
    let recursive = checked
        .as_ref()
        .is_some_and(|checked| checked.typed.node_types.values().any(Ty::is_recursive));
    let row_knot = recursive
        && checked.as_ref().is_some_and(|checked| {
            checked.typed.node_types.values().any(|ty| {
                let mut canon = Canon {
                    labels: &reader.labels,
                    groups: &reader.groups,
                    vars: Vec::new(),
                    binders: Vec::new(),
                    open_in_rec: false,
                };
                canon.ty(ty, &mut String::new());
                canon.open_in_rec
            })
        });
    let verdict = match &checked {
        Some(checked) => {
            let mut canon = Canon {
                labels: &reader.labels,
                groups: &reader.groups,
                vars: Vec::new(),
                binders: Vec::new(),
                open_in_rec: false,
            };
            let mut text = String::from("OK ");
            canon
                .ty(&checked.typed.root_ty, &mut text)
                .ok_or(Skip::OutsideFragment(Feature::UnwritableType))?;
            text
        }
        None => "ERR".to_string(),
    };
    let mut sexp = String::new();
    core.sexp(&mut sexp);
    let mode = if row_knot {
        'K'
    } else if recursive {
        'R'
    } else if reader.unary {
        'U'
    } else {
        'N'
    };
    let text = source
        .replace('\\', "\\\\")
        .replace('\n', "\\n")
        .replace('\t', "\\t");
    Ok(format!("{mode}\t{sexp}\t{verdict}\t{text}"))
}

/// Every string literal of a Rust source: ordinary and raw, comments skipped.
fn string_literals(source: &str) -> Vec<String> {
    let bytes = source.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'/' if bytes.get(i + 1) == Some(&b'/') => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'/' if bytes.get(i + 1) == Some(&b'*') => {
                i += 2;
                while i + 1 < bytes.len() && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
                    i += 1;
                }
                i += 2;
            }
            b'\'' => {
                // A character literal such as '"' or '\'', not a lifetime.
                if bytes.get(i + 2) == Some(&b'\'') {
                    i += 3;
                } else if bytes.get(i + 1) == Some(&b'\\') && bytes.get(i + 3) == Some(&b'\'') {
                    i += 4;
                } else {
                    i += 1;
                }
            }
            b'r' if matches!(bytes.get(i + 1), Some(b'"' | b'#'))
                && (i == 0 || !bytes[i - 1].is_ascii_alphanumeric() && bytes[i - 1] != b'_') =>
            {
                let mut j = i + 1;
                while bytes.get(j) == Some(&b'#') {
                    j += 1;
                }
                if bytes.get(j) != Some(&b'"') {
                    i += 1;
                    continue;
                }
                let hashes = j - (i + 1);
                let start = j + 1;
                let closing = format!("\"{}", "#".repeat(hashes));
                match source[start..].find(&closing) {
                    Some(len) => {
                        out.push(source[start..start + len].to_string());
                        i = start + len + closing.len();
                    }
                    None => break,
                }
            }
            b'"' => {
                let mut text = String::new();
                let mut j = i + 1;
                while j < bytes.len() && bytes[j] != b'"' {
                    if bytes[j] == b'\\' {
                        j += 1;
                        match bytes.get(j) {
                            Some(b'n') => text.push('\n'),
                            Some(b't') => text.push('\t'),
                            Some(b'"') => text.push('"'),
                            Some(b'\\') => text.push('\\'),
                            Some(b'\'') => text.push('\''),
                            Some(b'\n') => {
                                while matches!(bytes.get(j + 1), Some(b' ' | b'\t' | b'\n')) {
                                    j += 1;
                                }
                            }
                            _ => {}
                        }
                        j += 1;
                    } else {
                        let ch = source[j..].chars().next().unwrap();
                        text.push(ch);
                        j += ch.len_utf8();
                    }
                }
                out.push(text);
                i = j + 1;
            }
            _ => i += 1,
        }
    }
    out
}

fn rust_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            rust_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

fn markdown_blocks(text: &str) -> Vec<String> {
    let mut blocks = Vec::new();
    let mut current: Option<String> = None;
    for l in text.lines() {
        match (&mut current, l.trim_end()) {
            (None, "```goat") => current = Some(String::new()),
            (Some(_), "```") => blocks.extend(current.take()),
            (Some(block), _) => {
                block.push_str(l);
                block.push('\n');
            }
            _ => {}
        }
    }
    blocks
}

pub struct Rng {
    state: u64,
    tape: Vec<u8>,
    pos: usize,
}

impl Rng {
    pub fn seeded(seed: u64) -> Rng {
        Rng {
            state: seed,
            tape: Vec::new(),
            pos: 0,
        }
    }

    /// Draws each choice from `tape` while it lasts, so a fuzzer that mutates
    /// the bytes mutates the choices. Past the end the stream is seeded from
    /// the tape's own bytes, so a program is still a function of its input.
    pub fn from_tape(tape: &[u8]) -> Rng {
        let seed = tape.iter().fold(0xCBF2_9CE4_8422_2325_u64, |h, b| {
            (h ^ u64::from(*b)).wrapping_mul(0x0100_0000_01B3)
        });
        Rng {
            state: seed,
            tape: tape.to_vec(),
            pos: 0,
        }
    }

    fn next(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        if let Some(&low) = self.tape.get(self.pos) {
            self.pos += 1;
            if n <= 256 {
                return usize::from(low) % n;
            }
            let high = self.tape.get(self.pos).copied().unwrap_or(0);
            self.pos += 1;
            return (usize::from(low) | usize::from(high) << 8) % n;
        }
        (self.next() % n as u64) as usize
    }
}

/// A quarter of the generated whole numbers are negative literals, chosen from
/// the number itself so the generators draw the same random stream as without.
fn negate_some(n: usize) -> String {
    if n % 4 == 3 {
        format!("-{n}")
    } else {
        n.to_string()
    }
}

/// How a generated expression must be wrapped where it is an operand.
#[derive(Clone, Copy, PartialEq)]
enum Shape {
    Plain,
    Let,
    Num,
    Proj,
}

/// Writes closed curried programs: unary functions, one argument per call. A
/// function binding gets a name used nowhere else, since goat lets a function
/// see itself and the functions of its block, which the core's `let` does not.
struct Gen {
    rng: Rng,
    scope: Vec<String>,
    functions: u32,
}

impl Gen {
    fn wrap(text: String, shape: Shape, parenthesise: &[Shape]) -> String {
        if parenthesise.contains(&shape) {
            format!("({text})")
        } else {
            text
        }
    }

    fn leaf(&mut self) -> (String, Shape) {
        match self.rng.below(3) {
            0 if !self.scope.is_empty() => (
                self.scope[self.rng.below(self.scope.len())].clone(),
                Shape::Plain,
            ),
            1 => (
                if self.rng.below(2) == 0 {
                    "true"
                } else {
                    "false"
                }
                .to_string(),
                Shape::Plain,
            ),
            _ => (negate_some(self.rng.below(1000)), Shape::Num),
        }
    }

    fn term(&mut self, depth: u32) -> (String, Shape) {
        if depth >= MAX_DEPTH {
            return self.leaf();
        }
        let depth = depth + 1;
        match self.rng.below(10) {
            0..=2 => self.leaf(),
            3 | 4 => {
                let name = format!("v{}", self.rng.below(3));
                self.scope.push(name.clone());
                let (body, _) = self.term(depth);
                self.scope.pop();
                (format!("program({name}) do {body} done"), Shape::Plain)
            }
            5 | 6 => {
                let (callee, shape) = self.term(depth);
                let (arg, _) = self.term(depth);
                let callee = Self::wrap(callee, shape, &[Shape::Let, Shape::Num, Shape::Proj]);
                (format!("{callee}({arg})"), Shape::Plain)
            }
            7 => {
                let (value, shape) = self.term(depth);
                let is_function = value.starts_with("program(") && shape == Shape::Plain;
                let name = if is_function {
                    self.functions += 1;
                    format!("fun{}", self.functions)
                } else {
                    format!("v{}", self.rng.below(3))
                };
                self.scope.push(name.clone());
                let (body, _) = self.term(depth);
                self.scope.pop();
                let value = Self::wrap(value, shape, &[Shape::Let]);
                (format!("{name} = {value}; {body}"), Shape::Let)
            }
            8 => {
                let mut labels: Vec<u64> = Vec::new();
                for _ in 0..self.rng.below(4) {
                    let label = self.rng.next() % 5;
                    if !labels.contains(&label) {
                        labels.push(label);
                    }
                }
                let fields: Vec<String> = labels
                    .iter()
                    .map(|l| format!("lab{l}: {}", self.term(depth).0))
                    .collect();
                (format!("{{{}}}", fields.join(", ")), Shape::Plain)
            }
            _ => {
                let (base, shape) = self.term(depth);
                let base = Self::wrap(base, shape, &[Shape::Let, Shape::Num]);
                (format!("{base}.lab{}", self.rng.next() % 5), Shape::Proj)
            }
        }
    }
}

/// The types the typed generator writes.
#[derive(Clone, Copy, PartialEq)]
enum Prim {
    Int,
    Float,
    Bool,
    Str,
}

const PRIMS: [Prim; 4] = [Prim::Int, Prim::Float, Prim::Bool, Prim::Str];

/// Writes closed curried programs that use the phase-1 forms, aiming each
/// subterm at a type so most programs check. Now and then an operand gets the
/// wrong type, which the checker and the model must both reject. Every compound
/// term is parenthesised, so it is safe as an operand.
struct TypedGen {
    rng: Rng,
    scope: Vec<(String, Prim)>,
    names: u32,
    /// Whether the program being written still owes one wrong-typed operand.
    fault: bool,
}

impl TypedGen {
    fn literal(&mut self, ty: Prim) -> String {
        match ty {
            Prim::Int => negate_some(self.rng.below(100)),
            Prim::Float => format!("{}.{}", self.rng.below(10), self.rng.below(10)),
            Prim::Bool => ["true", "false"][self.rng.below(2)].to_string(),
            Prim::Str => format!("\"{}\"", ["a", "b", "ab", ""][self.rng.below(4)]),
        }
    }

    fn leaf(&mut self, ty: Prim) -> String {
        let vars: Vec<String> = self
            .scope
            .iter()
            .filter(|(_, t)| *t == ty)
            .map(|(n, _)| n.clone())
            .collect();
        if !vars.is_empty() && self.rng.below(2) == 0 {
            vars[self.rng.below(vars.len())].clone()
        } else {
            self.literal(ty)
        }
    }

    fn fresh_name(&mut self) -> String {
        self.names += 1;
        format!("v{}", self.names)
    }

    fn operand(&mut self, ty: Prim, depth: u32) -> String {
        if self.fault && self.rng.below(6) == 0 {
            self.fault = false;
            let wrong = PRIMS[self.rng.below(PRIMS.len())];
            self.term(wrong, depth)
        } else {
            self.term(ty, depth)
        }
    }

    fn pick(&mut self, options: &[&str]) -> String {
        options[self.rng.below(options.len())].to_string()
    }

    fn operation(&mut self, ty: Prim, depth: u32) -> Option<String> {
        let (op, left, right) = match ty {
            Prim::Int => (self.pick(&["+", "-", "*", "//", "%"]), Prim::Int, Prim::Int),
            Prim::Float => {
                let op = self.pick(&["+", "-", "*", "/"]);
                let left = PRIMS[self.rng.below(2)];
                let mut right = PRIMS[self.rng.below(2)];
                if op != "/" && left == Prim::Int {
                    right = Prim::Float;
                }
                (op, left, right)
            }
            Prim::Bool => {
                let op = self.pick(&["<", "<=", ">", ">=", "==", "!="]);
                let side = PRIMS[self.rng.below(PRIMS.len())];
                let mixed = side == Prim::Int && self.rng.below(3) == 0;
                (op, side, if mixed { Prim::Float } else { side })
            }
            Prim::Str => return None,
        };
        let a = self.operand(left, depth);
        let b = self.operand(right, depth);
        Some(format!("({a} {op} {b})"))
    }

    fn term(&mut self, ty: Prim, depth: u32) -> String {
        if depth >= TYPED_DEPTH {
            return self.leaf(ty);
        }
        let depth = depth + 1;
        match self.rng.below(9) {
            0 | 1 => self.leaf(ty),
            2 => {
                let c = self.term(Prim::Bool, depth);
                let a = self.term(ty, depth);
                let b = self.term(ty, depth);
                format!("(if {c} then {a} else {b} done)")
            }
            3 => {
                let bound = PRIMS[self.rng.below(PRIMS.len())];
                let value = self.term(bound, depth);
                let name = self.fresh_name();
                self.scope.push((name.clone(), bound));
                let body = self.term(ty, depth);
                self.scope.pop();
                format!("({name} = {value}; {body})")
            }
            4 => {
                let param = PRIMS[self.rng.below(PRIMS.len())];
                let name = self.fresh_name();
                self.scope.push((name.clone(), param));
                let body = self.term(ty, depth);
                self.scope.pop();
                let arg_ty = if param == Prim::Float && self.rng.below(3) == 0 {
                    Prim::Int
                } else {
                    param
                };
                let arg = self.operand(arg_ty, depth);
                format!("(program({name}) do {body} done({arg}))")
            }
            _ => self.operation(ty, depth).unwrap_or_else(|| self.leaf(ty)),
        }
    }
}

/// Writes closed curried programs built from blocks of functions that call
/// themselves and each other, in any order and at any depth, with computed
/// values between them. Most bodies and uses are not aimed at a type, so the
/// checker and the model must agree on rejections too.
struct GroupGen {
    rng: Rng,
    names: u32,
    /// Whether the program being written keeps to bodies that mostly check.
    careful: bool,
}

impl GroupGen {
    fn name(&mut self, prefix: &str) -> String {
        self.names += 1;
        format!("{prefix}{}", self.names)
    }

    fn pick(&mut self, from: &[String]) -> String {
        from[self.rng.below(from.len())].clone()
    }

    fn call(&mut self, functions: &[String], argument: &str) -> String {
        format!("{}({argument})", self.pick(functions))
    }

    /// A value to pass or bind: a name, a literal, a record, or a call.
    fn value(&mut self, functions: &[String], vars: &[String]) -> String {
        match self.rng.below(8) {
            0 | 1 if !vars.is_empty() => self.pick(vars),
            2 => format!("({} // 1)", self.rng.below(10)),
            3 => "true".to_string(),
            4 => "\"s\"".to_string(),
            5 => format!("{{lab{}: {}}}", self.rng.below(2), "true"),
            6 if !functions.is_empty() => {
                let argument = format!("({} // 1)", self.rng.below(10));
                self.call(functions, &argument)
            }
            _ => "true".to_string(),
        }
    }

    fn body(&mut self, param: &str, functions: &[String], vars: &[String], depth: u32) -> String {
        let choice = if self.careful {
            [0, 1, 1, 2, 5, 8, 12][self.rng.below(7)]
        } else {
            self.rng.below(13)
        };
        match choice {
            0 => param.to_string(),
            1 | 2 => self.call(functions, param),
            3 => format!("{{lab0: {param}, lab1: {}}}", self.call(functions, param)),
            4 => {
                let inner = self.call(functions, param);
                self.call(functions, &inner)
            }
            5 | 6 => {
                let rest = self.call(functions, &format!("{param} // 2"));
                format!("(if {param} // 2 < 1 then (0 // 1) else {rest} done)")
            }
            7 => {
                let rest = self.call(functions, &format!("{param} // 2"));
                format!("(if {param} // 2 == 0 then true else {rest} done)")
            }
            8 => {
                let (a, b) = (self.call(functions, param), self.call(functions, param));
                format!("(if true then {a} else {b} done)")
            }
            9 => format!("{param}.lab0"),
            10 => {
                let argument = self.value(functions, vars);
                self.call(functions, &argument)
            }
            11 => {
                let callee = self.call(functions, param);
                format!("{callee}.lab1")
            }
            _ if depth < 2 => format!("({})", self.block(depth + 1, functions, vars)),
            _ => param.to_string(),
        }
    }

    /// A block of `count` functions and a few values, then a result that uses
    /// them. `outer` holds the functions and `vars` the names the block sees.
    fn block(&mut self, depth: u32, outer: &[String], vars: &[String]) -> String {
        let count = 1 + self.rng.below(3);
        let functions: Vec<String> = (0..count).map(|_| self.name("g")).collect();
        let all: Vec<String> = outer.iter().chain(&functions).cloned().collect();
        let values = self.rng.below(3);
        // A slot is a function (`Some`) or a value (`None`). Values mostly go
        // first, sometimes after the functions, and now and then between them.
        let mut slots: Vec<Option<usize>> = (0..count).map(Some).collect();
        let layout = self.rng.below(6);
        for _ in 0..values {
            let at = match layout {
                0..=3 => 0,
                4 => slots.len(),
                _ => self.rng.below(slots.len() + 1),
            };
            slots.insert(at, None);
        }
        let mut seen: Vec<String> = Vec::new();
        let mut bound: Vec<String> = vars.to_vec();
        let mut text = String::new();
        for slot in slots {
            match slot {
                Some(i) => {
                    let param = self.name("p");
                    let mut inside = bound.clone();
                    inside.push(param.clone());
                    let body = self.body(&param, &all, &inside, depth);
                    text.push_str(&format!(
                        "{} = program({param}) do {body} done; ",
                        functions[i]
                    ));
                    seen.push(functions[i].clone());
                }
                None => {
                    let name = self.name("v");
                    let value = self.value(&seen, &bound);
                    text.push_str(&format!("{name} = {value}; "));
                    bound.push(name);
                }
            }
        }
        let result = match self.rng.below(6) {
            0 => self.call(&functions, "(1 // 1)"),
            1 => {
                let (a, b) = (
                    self.call(&functions, "(1 // 1)"),
                    self.call(&functions, "true"),
                );
                format!("{{lab0: {a}, lab1: {b}}}")
            }
            2 => {
                let (a, b) = (
                    self.call(&functions, "(1 // 1)"),
                    self.call(&functions, "{lab0: true}"),
                );
                format!("{{lab0: {a}, lab1: {b}}}")
            }
            3 => self.pick(&functions),
            4 if bound.len() > vars.len() => self.pick(&bound),
            _ => {
                let inner = self.call(&functions, "(1 // 1)");
                self.call(&functions, &inner)
            }
        };
        text.push_str(&result);
        text
    }
}

/// Programs of spreads and rest patterns over records of three labels: a
/// function that sets or drops a label, called at records that have it and
/// records that lack it, and spreads of record literals, nested. Values are
/// numerals, booleans and strings, so a call or an update often changes a
/// field's type and the checker and the model must agree on the rejection.
struct SpreadGen {
    rng: Rng,
}

impl SpreadGen {
    const LABELS: [&'static str; 3] = ["a", "b", "c"];

    fn label(&mut self) -> &'static str {
        Self::LABELS[self.rng.below(Self::LABELS.len())]
    }

    fn value(&mut self) -> String {
        match self.rng.below(3) {
            0 => negate_some(self.rng.below(100)),
            1 => ["true", "false"][self.rng.below(2)].to_string(),
            _ => "\"s\"".to_string(),
        }
    }

    /// Distinct labels, each with a value.
    fn fields(&mut self, most: usize) -> Vec<(&'static str, String)> {
        let mut out: Vec<(&'static str, String)> = Vec::new();
        for _ in 0..self.rng.below(most + 1) {
            let label = self.label();
            if out.iter().all(|(l, _)| *l != label) {
                out.push((label, self.value()));
            }
        }
        out
    }

    fn record(&mut self, depth: u32) -> String {
        if depth == 0 || self.rng.below(2) == 0 {
            let fields = self.fields(3);
            let body: Vec<String> = fields.iter().map(|(l, v)| format!("{l}: {v}")).collect();
            return format!("{{{}}}", body.join(", "));
        }
        let base = self.record(depth - 1);
        let mut fields = self.fields(2);
        if fields.is_empty() {
            fields.push((self.label(), self.value()));
        }
        let body: Vec<String> = fields.iter().map(|(l, v)| format!("{l}: {v}")).collect();
        format!("{{...{base}, {}}}", body.join(", "))
    }

    fn program(&mut self) -> String {
        let (one, two) = (self.label(), self.label());
        let value = self.value();
        let (first, second) = (self.record(2), self.record(2));
        match self.rng.below(5) {
            0 => format!(
                "f = program(p) do {{...p, {one}: {value}}} done\n{{x: f({first}), y: f({second})}}"
            ),
            1 => format!("f = program(p) do\n  {{{one}, ...r}} = p\n  r\ndone\nf({first})"),
            2 => format!(
                "f = program(p) do\n  {{{one}, ...r}} = p\n  {{...r, {two}: {value}}}\ndone\nf({first})"
            ),
            3 => format!(
                "f = program(p) do\n  {{{one}, {two}, ...r}} = p\n  r\ndone\n{{x: f({first}), y: f({second})}}"
            ),
            _ => {
                format!("f = program(p, q) do {{...p, {one}: q.{two}}} done\nf({first}, {second})")
            }
        }
    }
}

/// Programs that take lists apart with list patterns: a `match` of several arms,
/// a destructuring from a parameter and from a literal (the lengths that fit
/// and the ones that do not), and parameters that are patterns. The patterns
/// take zero to three items and perhaps a rest name; the bodies add the items
/// up, so the results are numbers and the lowering's decision tree is what the
/// checker must type the same way the model does.
struct ListGen {
    rng: Rng,
}

impl ListGen {
    /// A pattern over the names in `pool`: the names of the items it takes,
    /// and its text. The rest name is `rest`.
    fn pattern(
        &mut self,
        pool: &[&'static str],
        rest: &'static str,
    ) -> (Vec<&'static str>, String) {
        let items = pool[..self.rng.below(pool.len() + 1)].to_vec();
        let mut parts: Vec<String> = items.iter().map(|n| (*n).to_string()).collect();
        if self.rng.below(2) == 0 {
            parts.push(format!("...{rest}"));
        }
        let trailing = if !parts.is_empty() && self.rng.below(5) == 0 {
            ","
        } else {
            ""
        };
        (items, format!("[{}{trailing}]", parts.join(", ")))
    }

    fn body(&mut self, names: &[&'static str]) -> String {
        let mut terms: Vec<String> = names.iter().map(|n| (*n).to_string()).collect();
        if terms.is_empty() || self.rng.below(3) == 0 {
            terms.push(self.rng.below(10).to_string());
        }
        terms.join(" + ")
    }

    fn literal(&mut self) -> String {
        let items: Vec<String> = (0..self.rng.below(4))
            .map(|_| self.rng.below(10).to_string())
            .collect();
        format!("[{}]", items.join(", "))
    }

    fn program(&mut self) -> String {
        const FIRST: [&str; 3] = ["a", "b", "c"];
        const SECOND: [&str; 3] = ["d", "e", "f"];
        match self.rng.below(6) {
            0 | 1 => {
                let mut arms = String::new();
                for _ in 0..1 + self.rng.below(4) {
                    let (items, pattern) = self.pattern(&FIRST, "r");
                    let body = self.body(&items);
                    arms.push_str(&format!("    {pattern} then {body}\n"));
                }
                if self.rng.below(3) == 0 {
                    arms.push_str(&format!("    else {}\n", self.rng.below(10)));
                }
                let arg = self.literal();
                format!("f = program(xs) do\n  match xs do\n{arms}  done\ndone\nf({arg})")
            }
            2 | 5 => {
                let (items, pattern) = self.pattern(&FIRST, "r");
                let body = self.body(&items);
                let arg = self.literal();
                format!("f = program(xs) do\n  {pattern} = xs\n  {body}\ndone\nf({arg})")
            }
            3 => {
                let (items, pattern) = self.pattern(&FIRST, "r");
                let body = self.body(&items);
                let value = self.literal();
                format!("{pattern} = {value}\n{body}")
            }
            _ => {
                let (first, p) = self.pattern(&FIRST, "r");
                let (second, q) = self.pattern(&SECOND, "s");
                let names: Vec<&str> = first.iter().chain(&second).copied().collect();
                let body = self.body(&names);
                let (x, y) = (self.literal(), self.literal());
                format!("f = program({p}, {q}) do {body} done\nf({x}, {y})")
            }
        }
    }
}

/// Programs the repository's sources may not hold: let-polymorphism, row
/// polymorphism, rejections, and calls with several arguments.
const HANDWRITTEN: &[&str] = &[
    "f = program(r) do s = {...r, id: program(v) do v done}\n a = r == r\n b = r == {k: 1}\n 1 done\n1",
    "f = program(r) do s = {...r, id: program(v) do v done}\n b = r == {k: 1}\n a = r == r\n 1 done\n1",
    "f = program(r, x) do s = {...r, id: x}\n a = r == r\n b = r == {k: 1}\n 1 done\nf({k: 1}, program(v) do v done)",
    "f = program(r, x) do s = {...r, id: x}\n b = r == {k: 1}\n a = r == r\n 1 done\nf({k: 1}, program(v) do v done)",
    "f = program(r, x) do s = {...r, id: x}\n a = r == r\n 1 done\nf({k: 1}, 2)",
    "f = program(r) do s = {...r, id: program(v) do v done}\n a = r == r\n t = r.id\n 1 done\n1",
    "f = program(r) do s = {...r, id: program(v) do v done}\n t = r.id\n a = r == r\n 1 done\n1",
    "f = program(r) do s = {...r, id: program(v) do v done}\n a = r == r\n 1 done\nf({k: 1})",
    "f = program(r) do s = {...r, id: program(v) do v done}\n a = r == r\n 1 done\nf({id: program(v) do v done})",
    "f = program(r) do s = {...r, id: program(v) do v done}\n a = r == r\n u = {...r, id: program(w) do w done}\n 1 done\n1",
    "f = program(r) do s = {...r, id: program(v) do v done}\n u = {...r, id: program(w) do w done}\n a = r == r\n 1 done\n1",
    "f = program(r) do s = {...r, id: program(v) do v done}\n a = r == {k: 1}\n 1 done\nf({k: 1})",
    "f = program(r, x) do s = {...r, id: x}\n a = r.id\n b = r == r\n 1 done\nf({id: 1, k: 1}, 2)",
    "f = program(r, x) do s = {...r, id: x}\n b = r == r\n a = r.id\n 1 done\nf({id: 1, k: 1}, 2)",
    "h = program(r, x) do {...r, id: x} done\nk = program(a, z) do h(a, z); a == a; a == {k: 1}; 1 done\nk({k: 1}, program(v) do v done)",
    "h = program(r, x) do {...r, id: x} done\nk = program(a, z) do h(a, z); a == {k: 1}; a == a; 1 done\nk({k: 1}, program(v) do v done)",
    "f = program(r) do g = program(x) do {...r, id: x} done\n u = g(1)\n w = g(\"s\")\n b = r == {k: 1}\n 1 done\nf({k: 1})",
    "f = program(r) do g = program(x) do {...r, id: x} done\n w = g(\"s\")\n u = g(1)\n b = r == {k: 1}\n 1 done\nf({k: 1})",
    "f = program(r) do g = program(x) do {...r, id: x} done\n u = g(1)\n w = g(\"s\")\n b = r.id\n 1 done\nf({id: 1})",
    "f = program(r) do g = program(x) do {...r, id: x} done\n w = g(\"s\")\n u = g(1)\n b = r.id\n 1 done\nf({id: 1})",
    "f = program(p, q) do x = {...p, a: {n: 1, s: \"a\"}}\n y = {...q, a: {n: \"b\", s: 2}}\n if true then p else q done done\n1",
    "f = program(p, q) do y = {...q, a: {n: \"b\", s: 2}}\n x = {...p, a: {n: 1, s: \"a\"}}\n if true then p else q done done\n1",
    "f = program(p, q) do x = {...p, a: program(v) do v done}\n y = {...q, a: 1}\n if true then p else q done done\n1",
    "f = program(p, q) do y = {...q, a: 1}\n x = {...p, a: program(v) do v done}\n if true then p else q done done\n1",
    "{x: 1.0, y: 2.0} / {x: 3.0, y: 4.0}",
    "f = program(p, q) do x = {...p, a: 1}\n y = {...q, a: \"x\"}\n if true then p else q done done\n1",
    "f = program(p, q) do y = {...q, a: \"x\"}\n x = {...p, a: 1}\n if true then p else q done done\n1",
    "f = program(p, q) do x = {...p, a: 1}\n y = {...q, a: \"x\"}\n if true then q else p done done\n1",
    "f = program(p, q) do b = p == {k: 1}\n x = {...p, a: 1}\n y = {...q, a: \"x\"}\n if true then p else q done done\n1",
    "f = program(p, q) do x = {...p, a: 1}\n y = {...q, a: \"x\"}\n if true then p else q done;\n b = p == {k: 1}\n 1 done\n1",
    "f = program(p, q) do x = {...p, a: 1}\n y = {...q, a: \"x\"}\n if true then p else q done;\n t = p.a\n t done\n1",
    "f = program(p, q) do x = {...p, a: 1}\n y = {...q, a: \"x\"}\n t = p.a\n if true then p else q done done\n1",
    "f = program(p, q) do x = {...p, a: 1}\n y = {...q, a: \"x\"}\n t = q.a\n if true then p else q done done\n1",
    "f = program(p, q, u, v) do x = {...p, a: u}\n y = {...q, a: v}\n if true then p else q done done\n1",
    "f = program(p, q) do x = {...p, a: program(v) do v done}\n y = {...q, a: \"s\"}\n if true then p else q done done\n1",
    "f = program(p, q) do x = {...p, a: 1}\n y = {...q, a: 2}\n r = if true then p else q done\n r.a done\n1",
    "f = program(p, q) do x = {...p, a: 1}\n y = {...q, a: true}\n r = if true then p else q done\n r.a done\n1",
    "f = program(p, q) do x = {...p, a: 1}\n y = {...q, a: \"x\"}\n if true then p else q done done\nf({k: 1}, {k: 2})",
    "f = program(p, q) do x = {...p, a: 1}\n y = {...q, a: \"x\"}\n if true then p else q done done\nf({a: 1}, {k: 2})",
    "{x: 1, y: 2} / {x: 3, y: 4}",
    "{x: 1.0} / {x: 2.0} / {x: 4.0}",
    "a = {x: 1.0, y: 2.0}\nb = {x: 3.0, y: 4.0}\na / b",
    "f = program(a) do a / {x: 1.0} done\nf({x: 1.0})",
    "f = program(a) do {x: 1.0} / a done\nf({x: 1.0})",
    "f = program(a) do a / a done\nf(2.0)",
    "f = program(a) do a / a done\nf({x: 1.0})",
    "f = program(a, b) do a / b done\nf({x: 1.0}, {x: 2.0})",
    "(program(a) do a / a done)({x: 1.0})",
    "(program(a) do a / a done)({x: 1})",
    "(program(a) do a / a done)(3)",
    "f = program(a) do a / a done\nf(3)",
    "f = program(a) do a / 1 done\nf({x: 1.0})",
    "f = program(a) do a / 1 done\nf(2)",
    "f = program(a) do 1 / a done\nf({x: 1.0})",
    "f = program(a) do a / 2 done\nf(2.0)",
    "f = program(a, b) do a / b done\nf(1, 2)",
    "f = program(a) do a / a done\n{p: f(2.0), q: f({x: 1.0})}",
    "{x: 9} / {x: 3}",
    "{x: 1.0} / 2.0",
    "2.0 / {x: 2.0}",
    "{x: 1.0} / {y: 2.0}",
    "{x: 1.0, y: 2.0} / {x: 3.0}",
    "{x: \"a\"} / {x: \"b\"}",
    "r = {a: 1}\n{x: r.a + 1.5, y: r.a // 2}",
    "r = {a: 1, id: program(v) do v done}\n{p: (r.id)(1), q: (r.id)(true), x: r.a + 1.5}",
    "r = {a: 1, id: program(v) do v done}\ns = {...r, b: 2}\n{p: (s.id)(1), q: (s.id)(true)}",
    "n = 3\nm = n\n{x: m + 1.5, y: m + 1}",
    "n = 3\n{x: n + 1.5, y: n // 2}",
    "id = program(v) do v done\nf = id\n{p: f(1), q: f(true)}",
    "f = program(x) do x + 1 done\ng = f\n{p: g(1), q: g(1.5)}",
    "{...{a: 1}, b: 2}",
    "math = {double: program(x) do x * 2 done}\nmath::double(5)",
    "math = {double: program(x) do x * 2 done}\nd = math::double\nd(5)",
    "pair = {first: program(a, b) do a done}\npair.first(1)",
    "{x: 1, get: program(self) do self.x done}.get()",
    "ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}\nball.moved().x",
    "lit = {a: program(self) do self.x done, b: program(self) do self.y done}\nlit.a()",
    "f = program(r) do r.m() done\nf({m: program(self) do 1 done})",
    "set_x = program(r) do {...r, x: 1} done\n{a: set_x({x: 4, z: 2}), b: set_x({y: true})}",
    "set_x = program(r) do {...r, x: 1} done\nset_x(set_x({y: true}))",
    "set_x = program(r) do {...r, x: 1} done\nset_x({x: \"s\"})",
    "{...{x: 1, y: true}, x: 2}",
    "{...{x: 1}, y: true}",
    "{...{x: 1}, x: true}",
    "{...{x: 1, y: 2}, x: 3, y: 4}",
    "{...{x: 1}, y: true, z: \"s\"}",
    "f = program(p) do {...p, a: true} done\nf({a: false, b: 1})",
    "program(p) do {...p, a: p.b} done",
    "program(p, q) do\n  x = {...p, a: 1}\n  y = {...q, a: 2}\n  if true then p else q done\ndone",
    "program(p, q) do\n  x = {...p, a: 1}\n  y = {...q, a: \"x\"}\n  if true then p else q done\ndone",
    "program(p, q) do {...p, x: q.x} done",
    "program(p) do if true then {...p, x: 1} else p done",
    "program(p) do {...{...p, a: 1}, b: true} done",
    "program(r) do q = {...r, x: 1}\nq.x done",
    "f = program(p) do {...p, x: 1} done\ng = program(q) do f(q) done\ng({y: true})",
    "program(p) do {a, ...r} = p\nr done",
    "program(p) do {a, b, ...r} = p\nr done",
    "program(p) do {a, ...r} = p\n{...r, b: a} done",
    "program(p) do {x, ...r} = p\n{...r, x: 2} done",
    "program(p) do\n  {x, ...r} = p\n  if true then r else {x: 1}\ndone",
    "program(p) do\n  {x, ...r} = p\n  {...r, x: 1}\ndone",
    "f = program(p) do\n  {x, ...r} = p\n  r\ndone\nf({x: 1, y: true, z: \"s\"})",
    "f = program(p) do\n  {x, ...r} = p\n  r\ndone\nf({y: true})",
    "f = program(p) do\n  {x, y, ...r} = p\n  {...r, y: x}\ndone\nf({x: 1, y: true, z: \"s\"})",
    "id = program(x) do x done\n{a: id(1), b: id(true)}",
    "get = program(r) do r.x done\n{a: get({x: 1, y: true}), b: get({x: false})}",
    "add = program(a, b) do {x: a, y: b} done\nadd(1, true)",
    "f = program(a, b) do a done\nf(1)",
    "program(r) do {a: r.x, b: r.y} done",
    "program(x) do x(x) done",
    "r = {x: 1}\nr.y",
    "twice = program(f) do program(x) do f(f(x)) done done\ntwice(program(n) do n done)(3)",
    "compose = program(f) do program(g) do program(x) do f(g(x)) done done done\ncompose",
    "k = program(x) do program(y) do x done done\nk(1)(true)",
    "program(f) do f(1) done",
    "program(f) do {a: f(1), b: f(true)} done",
    "p = {x: {y: 1}}\np.x.y",
    "program(r) do r.x.y done",
    "program(a) do {x: a, y: a} done",
    "pair = program(a, b) do {first: a, second: b} done\npair(1, true).second",
    "swap = program(p) do {first: p.second, second: p.first} done\nswap",
    "choose = program(a, b) do a done\nchoose(1, 2)",
    "apply = program(f, x) do f(x) done\napply(program(n) do n done, 1)",
    "1 + 1.5",
    "1.5 + 1",
    "1.5 / 2.5",
    "program(x) do x * 2 done",
    "program(x) do x * x done",
    "program(a, b) do a + b done",
    "f = program(x) do x * 2 done\n{a: f(1), b: f(1.5)}",
    "f = program(x) do x * 2 done\nf(1.5)",
    "f = program(x) do x * 2 done\nf",
    "add = program(a, b) do a + b done\n{p: add(1, 2), q: add(1.5, 2.5), r: add(1, 2.5)}",
    "f = program(x) do x + 1 done\ng = program(y) do f(y) * 2.5 done\ng(3)",
    "f = program(x) do x * 2 done\nf(\"a\")",
    "f = program(x) do x * 2 done\nf(true)",
    "if true then 1 else 2.5 done + 1",
    "7 / 2",
    "1.5 < 2",
    "\"a\" < \"b\"",
    "if true then 1 else 2 done",
    "if true then 1 else 2.5 done",
    "n = 3\nn + 1.5",
    "n = 3\nn / 2",
    "f = program(x) do x * 1.5 done\nf(2)",
    "7 // 2.0",
    "\"a\" + 1",
    "if 1 then 2 else 3 done",
    "",
    "() == ()",
    "f = program(x) do g(x) done\ng = program(y) do y done\na = f(1)\nb = f(true)\nb",
    "g = program(y) do y done\nf = program(x) do g(x) done\n{a: f(1), b: f(true)}",
    "f = program(x) do {a: g(1), b: g(true)} done\ng = program(y) do y done\nf(1)",
    "even = program(n) do if n == 0 then true else odd(n - 1) done done\nodd = program(n) do if n == 0 then false else even(n - 1) done done\neven(4)",
    "count = program(n) do if n < 1 then 0 else count(n - 1) done done\ncount(3)",
    "loop = program(x) do loop(x) done\n{a: loop(1), b: loop(true)}",
    "ping = program(x) do pong(x) done\npong = program(y) do ping(y) done\n{a: ping(1), b: pong(true)}",
    "outer = program(k) do\n  f = program(x) do g(x) done\n  g = program(y) do y done\n  {a: f(1), b: f(k)}\ndone\nouter(true)",
    "n = 1 + 2\nm = n * 2\nm",
    "id = program(x) do x done\nr = id(3)\n{a: r, b: id(true)}",
    "f = program(x) do x done\nv = f(1)\ng = program(y) do f(y) done\ng(true)",
    "f = program(x) do g(x) done\ng = program(y) do y done\na = f(1.5)\nb = f(true)\nb",
    "f = program(x) do g(x) done\ng = program(y) do y done\n{a: f(\"s\"), b: f(true)}",
    "even = program(n) do if n // 1 == 0 then true else odd(n // 2) done done\nodd = program(n) do if n // 1 == 0 then false else even(n // 2) done done\neven(4 // 1)",
    "count = program(n) do if n // 1 < 1 then 0 // 1 else count(n // 2) done done\ncount(3 // 1)",
    "total = 1 // 1 + 2 // 1\nscaled = total * 2\nscaled",
    "ping = program(x, k) do pong(x, k) done\npong = program(y, k) do ping(y, k) done\n{a: ping(true, true), b: pong(\"s\", true)}",
    "v = 71 // 88\nif v <= v then v - 3.1 else 4.0 done",
    "f = program(x) do x == x % x done\nf(90)",
    "set_x = program(r) do {...r, x: 1} done\n{a: set_x({x: 4, z: 2}), b: set_x({y: true})}",
    "f = program(p) do\n  {x, ...r} = p\n  r\ndone\nf({x: 1, y: true})",
    "same = program(a, b) do a == b done\nf = program(x) do same({p: x}, {p: x}) done\nf(1)",
    "same = program(a, b) do a == b done\nf = program(x) do same({p: x}, {p: x}) done\n{a: f(1), b: f(\"s\")}",
    "same = program(a, b) do a == b done\nf = program(x) do same({p: x, q: x}, {p: x, q: x}) done\nf(1)",
    "add = program(a, b) do a + b done\nf = program(x) do add({p: x}, {p: x}) done\nf(1)",
    "f = program(x) do {p: x} == {p: x} done\nf(1)",
    "f = program(p) do\n  {x, ...r} = p\n  {...r, x: 2}\ndone\nf({x: 1, y: true})",
    "f = program(p) do\n  {x, ...r} = p\n  {...r, x: 2}\ndone\n{a: f({x: 1, y: true}), b: f({x: \"s\", z: 3})}",
    "f = program(p) do\n  {x, ...r} = p\n  if true then r else {x: 1} done\ndone\n1",
    "program(a, b) do (if a == b then 1 else 2 done) + a.x done",
    "f = program(a, b) do (if a == b then 1 else 2 done) + a.x done\nf({x: 1, y: 2}, {x: 3, y: 4})",
    "program(q) do\n  e = q == q\n  {...q, x: 1}\ndone",
    "f = program(q) do\n  e = q == q\n  {...q, x: 1}\ndone\nf({})",
    "program(w) do\n  t = {...w, x: 1}\n  u = if true then w else {} done\n  w == w\ndone",
    "program(w) do\n  t = {...w, x: program(z) do z done}\n  u = if true then w else {} done\n  w == w\ndone",
    "f0 = program(q) do\n  v1 = {...q, x: 1}\n  q\ndone\nprogram(w) do\n  v3 = f0({y: 1})\n  {...v3, x: \"s\"}\ndone",
    "f = program(q) do\n  {...q, x: 1}\ndone\ng = program(p) do\n  {x, ...r} = p\n  f(r)\ndone\n1",
    "f0 = program(q) do\n  {...q, y: true}\ndone\nprogram(w) do\n  e0 = w.x\n  e1 = w == w\n  f0(w)\ndone",
    "program(w) do\n  t = {...w, x: program(z) do z done}\n  w == {}\ndone",
    "f0 = program(q) do\n  e = q == q\n  {...q, z: 2}\ndone\nprogram(w) do\n  f0({x: {...w, y: 1}})\ndone",
    "f0 = program(q) do\n  e = q == q\n  {...q, z: 2}\ndone\nprogram(w) do\n  v0 = w.x\n  v1 = {...v0, y: {}}\n  f0(w)\ndone",
    "f0 = program(q) do\n  {...q, z: 1}\ndone\nprogram(w) do\n  {z, ...r0} = w\n  v1 = f0(r0)\n  if true then w else v1 done\ndone",
    "f1 = program(q) do\n  {...q, z: \"s\"}\ndone\nf0 = program(q) do\n  {x, ...r} = q\n  {...r, z: 1}\ndone\nprogram(v0) do\n  {z, ...r1} = v0\n  v2 = f1(r1)\n  f0(r1)\ndone",
    "program(u) do\n  {b, ...w} = u\n  v = {a: 1, b: w}\n  if true then v else u done\ndone",
    "program(u) do\n  {b, ...w} = u\n  v = {a: 1, b: w}\n  if true then u else v done\ndone",
    "f = program(u) do\n  {b, ...w} = u\n  v = {a: 1, b: w}\n  if true then v else u done\ndone\nf({b: {}, a: 2})",
];

/// One program from generator `kind` (taken modulo the four), every choice
/// read from `tape`; the nightly fuzz target mutates the tape.
pub fn generate_from_tape(kind: u8, tape: &[u8]) -> String {
    let rng = Rng::from_tape(tape);
    match kind % 4 {
        0 => {
            Gen {
                rng,
                scope: Vec::new(),
                functions: 0,
            }
            .term(0)
            .0
        }
        1 => {
            let mut typed_gen = TypedGen {
                rng,
                scope: Vec::new(),
                names: 0,
                fault: false,
            };
            typed_gen.fault = typed_gen.rng.below(4) == 0;
            let ty = PRIMS[typed_gen.rng.below(PRIMS.len())];
            typed_gen.term(ty, 0)
        }
        2 => {
            let mut group_gen = GroupGen {
                rng,
                names: 0,
                careful: false,
            };
            group_gen.careful = group_gen.rng.below(2) == 0;
            group_gen.block(0, &[], &[])
        }
        _ => SpreadGen { rng }.program(),
    }
}

fn main() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut sources: Vec<String> = Vec::new();

    let mut examples: Vec<_> = std::fs::read_dir(root.join("examples"))
        .expect("examples/")
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|e| e == "goat"))
        .collect();
    examples.sort();
    for path in examples {
        sources.push(std::fs::read_to_string(path).expect("an example"));
    }

    sources.extend(markdown_blocks(
        &std::fs::read_to_string(root.join("docs/llm.md")).expect("docs/llm.md"),
    ));

    let mut files = Vec::new();
    rust_files(&root.join("checker"), &mut files);
    rust_files(&root.join("parser"), &mut files);
    for path in files {
        if path.ends_with("examples/core_corpus.rs") {
            continue;
        }
        let text = std::fs::read_to_string(&path).expect("a Rust source");
        sources.extend(string_literals(&text));
    }

    sources.extend(HANDWRITTEN.iter().map(|s| s.to_string()));

    for seed in SEEDS {
        let mut gen_ = Gen {
            rng: Rng::seeded(seed),
            scope: Vec::new(),
            functions: 0,
        };
        for _ in 0..GENERATED {
            gen_.functions = 0;
            sources.push(gen_.term(0).0);
        }

        let mut typed_gen = TypedGen {
            rng: Rng::seeded(seed ^ 0xA5A5),
            scope: Vec::new(),
            names: 0,
            fault: false,
        };
        for _ in 0..GENERATED_TYPED {
            typed_gen.names = 0;
            typed_gen.fault = typed_gen.rng.below(4) == 0;
            let ty = PRIMS[typed_gen.rng.below(PRIMS.len())];
            sources.push(typed_gen.term(ty, 0));
        }

        let mut group_gen = GroupGen {
            rng: Rng::seeded(seed ^ 0x5EED),
            names: 0,
            careful: false,
        };
        for _ in 0..GENERATED_GROUPS {
            group_gen.names = 0;
            group_gen.careful = group_gen.rng.below(2) == 0;
            sources.push(group_gen.block(0, &[], &[]));
        }

        let mut spread_gen = SpreadGen {
            rng: Rng::seeded(seed ^ 0x5B4E),
        };
        for _ in 0..GENERATED_SPREADS {
            sources.push(spread_gen.program());
        }

        let mut list_gen = ListGen {
            rng: Rng::seeded(seed ^ 0x0115_7A77),
        };
        for _ in 0..GENERATED_LISTS {
            sources.push(list_gen.program());
        }
    }

    if std::env::args().any(|arg| arg == "--sources") {
        for source in &sources {
            let code_points: Vec<String> = source.chars().map(|c| (c as u32).to_string()).collect();
            println!("{}", code_points.join(" "));
        }
        return;
    }

    let mut seen = HashSet::new();
    let mut skipped: BTreeMap<Skip, usize> = BTreeMap::new();
    let mut kept = 0;
    for source in &sources {
        match line(source) {
            Ok(line) => {
                if seen.insert(
                    line.rsplit_once('\t')
                        .expect("a source column")
                        .0
                        .to_string(),
                ) {
                    kept += 1;
                    println!("{line}");
                }
            }
            Err(skip) => *skipped.entry(skip).or_default() += 1,
        }
    }
    eprintln!("corpus: {kept} programs written");
    for (skip, n) in skipped {
        eprintln!("corpus: skipped {n:>6}  {}", skip.describe());
    }
}
