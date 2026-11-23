//! Heap values on the native backend: the generated allocator, reference
//! counting and drop loop, checked against the reference interpreter's
//! allocation counts and against wasm.

#[path = "../../mir/tests/common/mod.rs"]
mod common;
mod support;

use common::*;
use goat::{HostInterface, NoHost, Profile};
use goat_llvm::{EmitOptions, emit, emit_with_options};
use goat_mir::*;
use goat_native::abi::{HOST_VERSION, Instance};
use goat_native::{Library, Run, Stopped, build, clang_available};
use std::collections::BTreeMap;
use support::interpreted;

macro_rules! need_clang {
    () => {
        if !clang_available() {
            eprintln!("skipping: clang is not available");
            return;
        }
    };
}

const LIST: LayoutId = LayoutId(2);
const PAIR: LayoutId = LayoutId(3);

fn list_ty() -> MTy {
    MTy::Ptr(HeapKind::Variant(LIST))
}

/// A program with a list layout (`Empty | Link(Int, rest)`) and a record of two
/// `Int`s, after the layouts `program` gives.
fn with_lists(funcs: Vec<Func>) -> Program {
    let mut p = program(funcs);
    p.layouts.push(Layout::Variant(BTreeMap::from([
        (0, vec![]),
        (1, vec![MTy::Int, list_ty()]),
    ])));
    p.layouts.push(Layout::Record(vec![MTy::Int, MTy::Int]));
    p
}

fn embedded(mut p: Program) -> Program {
    p.profile = Profile::Embedded;
    p
}

fn list_of(items: &[i64]) -> Expr {
    items
        .iter()
        .rev()
        .fold(Expr::AllocVariant(LIST, 0, vec![]), |rest, &n| {
            Expr::AllocVariant(LIST, 1, vec![int(n), rest])
        })
}

/// Consumes the cell and recurses on the tail, using `step` for the payload.
fn fold_list(self_id: u32, step: fn(Expr, Expr) -> Expr) -> Func {
    func_with(
        vec![(0, list_ty())],
        MTy::Int,
        Expr::Switch(
            Local(0),
            vec![(0, let_(1, drop_(0), int(0)))],
            Box::new(Expr::Unpack(
                Local(0),
                1,
                vec![Local(2), Local(3)],
                Box::new(let_(
                    4,
                    Expr::Free(Local(0)),
                    step(local(2), call(self_id, vec![local(3)])),
                )),
            )),
        ),
    )
}

/// `incr(xs)`: each element plus one, in the cells it came from when it can.
fn incr() -> Func {
    func_with(
        vec![(0, list_ty())],
        list_ty(),
        Expr::Switch(
            Local(0),
            vec![(0, local(0))],
            Box::new(Expr::Unpack(
                Local(0),
                1,
                vec![Local(1), Local(2)],
                Box::new(let_(
                    3,
                    call(1, vec![local(2)]),
                    Expr::ReuseVariant(Local(0), LIST, 1, vec![add(local(1), int(1)), local(3)]),
                )),
            )),
        ),
    )
}

/// What the interpreter and the native backend both make of `p`: the same
/// value, the same allocation count, and nothing left allocated. The
/// interpreter allocates a cell for each nullary variant it builds, as the
/// `nullary` of them in `p`, where compiled code points at one static cell.
fn agree(p: &Program, nullary: u64) -> Run<NoHost> {
    assert_eq!(verify(p), Ok(()));
    let expected = goat_mir::run(p).expect("the interpreter runs it");
    assert_eq!(expected.live_allocations, 0);
    let run = native(p);
    assert_eq!(run.result, Ok(()));
    assert_eq!(run.live_allocs, 0, "the native program leaked");
    assert_eq!(
        run.allocations,
        expected.allocations as u64 - nullary,
        "allocation counts differ"
    );
    let printed = match expected.value {
        Value::Int(n) => n.to_string(),
        Value::Float(x) => goat::format_number(x),
        Value::Bool(b) => goat::format_bool(b).to_string(),
        other => panic!("unexpected root {other:?}"),
    };
    assert_eq!(run.printed, [printed]);
    run
}

fn native(p: &Program) -> Run<NoHost> {
    let ll = emit(p).expect("the program emits");
    Library::build(&ll)
        .expect("clang builds it")
        .run(NoHost)
        .expect("it runs")
}

fn library(source: &str) -> Library {
    build(
        Profile::Desktop,
        source,
        &HostInterface::new(goat_checker::PRELUDE),
    )
    .expect("program builds")
}

#[test]
fn a_record_is_built_read_and_freed() {
    need_clang!();
    let run = library("mk = program(x, y) do {x: x, y: y} done\na = mk(1.0, 2.0)\na.x + a.y")
        .run(NoHost)
        .unwrap();
    assert_eq!(run.printed, ["3"]);
    assert_eq!((run.live_allocs, run.allocations), (0, 1));
}

#[test]
fn a_record_of_constants_is_one_immortal_cell() {
    need_clang!();
    let run = library("{x: 1.0, y: 2.0}.x + {x: 1.0, y: 2.0}.y")
        .run(NoHost)
        .unwrap();
    assert_eq!(run.printed, ["3"]);
    assert_eq!((run.live_allocs, run.allocations), (0, 0));
}

#[test]
fn variants_are_built_matched_and_freed() {
    need_clang!();
    let source = "tag Pile = Nil | Cons(_, Pile)
second = program(pile) do
  match pile do
    Nil then 0
    Cons(head, rest) then
      match rest do
        Nil then head
        Cons(next, more) then head + next
      done
  done
done
answer = second(Cons(10, Cons(20, Cons(30, Nil))))
answer + 0";
    let run = library(source).run(NoHost).unwrap();
    assert_eq!(run.printed, ["30"]);
    assert_eq!((run.live_allocs, run.allocations), (0, 3));
}

#[test]
fn strings_are_read_copied_and_compared() {
    need_clang!();
    let run = library(
        "s = \"h\u{e9}llo\"\n\
         print(byte_length(s));\n\
         print(char_count(s));\n\
         print(byte_at(s, 2));\n\
         print(char_at(s, 2));\n\
         print(char_at(s, 2) == \"\u{e9}\");\n\
         char_at(s, 1)",
    )
    .run(NoHost)
    .unwrap();
    assert_eq!(run.printed, ["6", "5", "195", "\u{e9}", "true", "h"]);
    assert_eq!(run.result, Ok(()));
}

#[test]
fn a_position_outside_a_string_traps() {
    need_clang!();
    for source in [
        "byte_at(\"hi\", 3)",
        "byte_at(\"hi\", 0)",
        "char_at(\"hi\", 3)",
        "char_at(\"hi\", 0)",
        "char_at(\"hi\", -9223372036854775807)",
    ] {
        let run = library(source).run(NoHost).unwrap();
        let stopped = run.result.expect_err(source);
        assert_eq!(stopped.message, BYTE_OUT_OF_RANGE, "{source}");
    }
}

#[test]
fn a_unique_list_is_walked_and_rebuilt_in_place() {
    need_clang!();
    let main = |body: Expr| func(MTy::Int, body);
    // sum(incr([1, 2, 3])): the rebuilt list lives in the cells it came from.
    let unique = main(call(2, vec![call(1, vec![list_of(&[1, 2, 3])])]));
    let p = with_lists(vec![unique, incr(), fold_list(2, add)]);
    let run = agree(&p, 1);
    assert_eq!(run.printed, ["9"]);
    assert_eq!(run.allocations, 3);
}

#[test]
fn a_shared_list_is_copied_and_left_intact() {
    need_clang!();
    let body = let_(
        0,
        list_of(&[1, 2, 3]),
        let_(
            1,
            Expr::Dup(Local(0)),
            let_(
                2,
                call(1, vec![local(0)]),
                let_(
                    3,
                    call(2, vec![local(2)]),
                    let_(4, call(2, vec![local(0)]), add(local(3), local(4))),
                ),
            ),
        ),
    );
    let p = with_lists(vec![func(MTy::Int, body), incr(), fold_list(2, add)]);
    let run = agree(&p, 1);
    assert_eq!(run.printed, ["15"]);
    assert_eq!(run.allocations, 6);
}

#[test]
fn embedded_cells_have_the_same_size_and_behavior() {
    need_clang!();
    let body = let_(
        0,
        list_of(&[1, 2, 3]),
        let_(
            1,
            Expr::Dup(Local(0)),
            let_(
                2,
                call(1, vec![local(0)]),
                let_(
                    3,
                    call(2, vec![local(2)]),
                    let_(4, call(2, vec![local(0)]), add(local(3), local(4))),
                ),
            ),
        ),
    );
    let p = embedded(with_lists(vec![
        func(MTy::Int, body),
        incr(),
        fold_list(2, add),
    ]));
    assert_eq!(agree(&p, 1).printed, ["15"]);
}

/// `build(n)`: a list of `n` cells, by recursion.
fn build_list() -> Func {
    func_with(
        vec![(0, MTy::Int)],
        list_ty(),
        if_(
            cmp(CmpOp::Eq, local(0), int(0)),
            Expr::AllocVariant(LIST, 0, vec![]),
            Expr::AllocVariant(
                LIST,
                1,
                vec![local(0), call(1, vec![sub(local(0), int(1))])],
            ),
        ),
    )
}

#[test]
fn a_long_chain_is_dropped_by_the_loop_not_by_recursion() {
    need_clang!();
    const LEN: i64 = 20_000;
    let body = let_(0, call(1, vec![int(LEN)]), let_(1, drop_(0), int(0)));
    let p = with_lists(vec![func(MTy::Int, body), build_list()]);
    assert_eq!(verify(&p), Ok(()));
    let ll = emit(&p).unwrap();
    // Building recurses once per cell, so the program runs on a big stack.
    let run = std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(move || Library::build(&ll).unwrap().run(NoHost).unwrap())
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(run.result, Ok(()));
    assert_eq!((run.live_allocs, run.allocations), (0, LEN as u64));
}

#[test]
fn a_unique_record_is_overwritten_and_a_shared_one_is_not() {
    need_clang!();
    let bump = |shared: bool| {
        let reuse = let_(
            1,
            Expr::ReuseRecord(
                Local(0),
                RECORD,
                vec![add(Expr::Field(Local(0), 0), int(10))],
            ),
            let_(2, Expr::Field(Local(1), 0), let_(3, drop_(1), local(2))),
        );
        let body = if shared {
            let_(
                4,
                Expr::Dup(Local(0)),
                let_(
                    5,
                    reuse,
                    let_(
                        6,
                        Expr::Field(Local(0), 0),
                        let_(7, drop_(0), add(local(5), local(6))),
                    ),
                ),
            )
        } else {
            reuse
        };
        program(vec![func(MTy::Int, let_(0, alloc_record(1), body))])
    };
    let unique = agree(&bump(false), 0);
    assert_eq!((unique.printed[0].as_str(), unique.allocations), ("11", 1));
    let shared = agree(&bump(true), 0);
    assert_eq!((shared.printed[0].as_str(), shared.allocations), ("12", 2));
}

#[test]
fn sharing_is_visible_and_an_address_names_a_live_object() {
    need_clang!();
    let body = let_(
        0,
        alloc_record(5),
        let_(
            1,
            Expr::Shared(Local(0)),
            let_(
                2,
                Expr::Dup(Local(0)),
                let_(
                    3,
                    Expr::Shared(Local(0)),
                    let_(
                        4,
                        Expr::Addr(Local(0)),
                        let_(
                            5,
                            Expr::Retain(Local(4), record_ty()),
                            let_(
                                6,
                                Expr::Field(Local(5), 0),
                                let_(
                                    7,
                                    drop_(5),
                                    let_(
                                        8,
                                        drop_(0),
                                        let_(
                                            9,
                                            drop_(0),
                                            if_(
                                                local(1),
                                                int(-1),
                                                if_(local(3), local(6), int(-2)),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    for p in [
        program(vec![func(MTy::Int, body.clone())]),
        embedded(program(vec![func(MTy::Int, body)])),
    ] {
        assert_eq!(agree(&p, 0).printed, ["5"]);
    }
}

fn strings_program() -> Program {
    // s = "héllo" (6 bytes, 5 code points); c = s[2] ("é"); k = a kept copy of s.
    let body = let_(
        0,
        Expr::StrLit(DataId(0)),
        let_(
            1,
            int(2),
            let_(
                2,
                Expr::StrChar(Local(0), Local(1)),
                let_(
                    3,
                    Expr::KeepStr(Local(0)),
                    let_(
                        4,
                        Expr::KeepStr(Local(2)),
                        let_(
                            5,
                            Expr::StrEq(Local(2), Local(4)),
                            let_(
                                6,
                                add(
                                    add(Expr::StrLen(Local(2)), Expr::StrChars(Local(0))),
                                    add(Expr::StrByte(Local(0), Local(1)), Expr::StrLen(Local(3))),
                                ),
                                let_(
                                    7,
                                    drop_(2),
                                    let_(
                                        8,
                                        drop_(3),
                                        let_(
                                            9,
                                            drop_(4),
                                            let_(10, drop_(0), if_(local(5), local(6), int(0))),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    let mut p = program(vec![func(MTy::Int, body)]);
    p.data = vec!["h\u{e9}llo".as_bytes().to_vec()];
    p
}

#[test]
fn string_nodes_agree_with_the_interpreter() {
    need_clang!();
    // 2 + 5 + 195 + 6, with one copy from `char`, one from the literal, and
    // none from the kept heap string.
    let run = agree(&strings_program(), 0);
    assert_eq!(run.printed, ["208"]);
    assert_eq!(run.allocations, 2);
    agree(&embedded(strings_program()), 0);
}

#[test]
fn a_large_string_is_served_by_a_large_size_class_and_recycled() {
    need_clang!();
    let body = let_(
        0,
        Expr::StrLit(DataId(0)),
        let_(
            1,
            Expr::KeepStr(Local(0)),
            let_(
                2,
                Expr::StrLen(Local(1)),
                let_(3, drop_(1), let_(4, drop_(0), local(2))),
            ),
        ),
    );
    let mut p = program(vec![func(MTy::Int, body)]);
    p.data = vec![vec![b'x'; 300]];
    let lib = Library::build(&emit(&p).unwrap()).unwrap();
    let mut instance = Instance::new(1 << 16);
    let first = lib.run_in(&mut instance, NoHost, HOST_VERSION).unwrap();
    assert_eq!(
        (first.printed.as_slice(), first.live_allocs),
        (&["300".to_string()][..], 0)
    );
    let used = instance.heap_used();
    assert!(
        used >= 512,
        "a 312-byte request takes a 512-byte block: {used}"
    );
    for _ in 0..3 {
        lib.run_in(&mut instance, NoHost, HOST_VERSION).unwrap();
    }
    assert_eq!(instance.heap_used(), used, "freed blocks are reused");
    assert_eq!(instance.allocations(), 4);
}

#[test]
fn freed_blocks_are_reused_across_runs_of_an_instance() {
    need_clang!();
    let p = with_lists(vec![
        func(
            MTy::Int,
            call(2, vec![call(1, vec![list_of(&[1, 2, 3, 4])])]),
        ),
        incr(),
        fold_list(2, add),
    ]);
    let lib = Library::build(&emit(&p).unwrap()).unwrap();
    let mut instance = Instance::new(1 << 16);
    let first = lib.run_in(&mut instance, NoHost, HOST_VERSION).unwrap();
    assert_eq!(first.printed, ["14"]);
    let used = instance.heap_used();
    for _ in 0..5 {
        let run = lib.run_in(&mut instance, NoHost, HOST_VERSION).unwrap();
        assert_eq!(
            (run.printed.as_slice(), run.live_allocs),
            (&["14".to_string()][..], 0)
        );
    }
    assert_eq!(instance.heap_used(), used);
    assert_eq!(instance.allocations(), 24);
}

/// `r = {1, 2}; drop r; r.1`: a read through a dangling pointer, which the
/// verifier would refuse.
fn dangling_read() -> Program {
    let body = let_(
        0,
        Expr::AllocRecord(PAIR, vec![add(int(1), int(0)), add(int(2), int(0))]),
        let_(1, drop_(0), Expr::Field(Local(0), 1)),
    );
    with_lists(vec![func(MTy::Int, body)])
}

#[test]
fn poison_is_written_only_in_checked_builds() {
    need_clang!();
    let run = |poison_freed| {
        let ll = emit_with_options(
            &dangling_read(),
            EmitOptions {
                poison_freed,
                ..EmitOptions::default()
            },
        )
        .unwrap();
        Library::build(&ll).unwrap().run(NoHost).unwrap().printed
    };
    assert_eq!(run(true), [i64::from_ne_bytes([0xFE; 8]).to_string()]);
    assert_eq!(run(false), ["2"]);
}

#[test]
fn a_double_release_traps() {
    need_clang!();
    let body = let_(
        0,
        alloc_record(1),
        let_(1, drop_(0), let_(2, drop_(0), int(0))),
    );
    let p = program(vec![func(MTy::Int, body)]);
    let run = native(&p);
    let stopped = run.result.expect_err("the second release traps");
    assert_eq!(stopped.message, "a heap block was released twice");
}

#[test]
fn a_write_to_a_freed_block_traps_at_the_next_allocation() {
    need_clang!();
    // A freed block's count word is zero. `Dup` of a dangling pointer, which the
    // verifier refuses, writes a one there, and the allocator that next pops
    // the block finds it.
    let body = let_(
        0,
        alloc_record(1),
        let_(
            1,
            drop_(0),
            let_(2, Expr::Dup(Local(0)), let_(3, alloc_record(2), int(0))),
        ),
    );
    let run = native(&program(vec![func(MTy::Int, body)]));
    let stopped = run
        .result
        .expect_err("the allocator sees the written block");
    assert_eq!(stopped.message, "a freed heap block was written to");
}

#[test]
fn a_heap_that_is_too_small_traps_with_the_budget_message() {
    need_clang!();
    // build(n) holds a cell per level of recursion, 24 bytes each.
    let body = call(1, vec![int(1000)]);
    let p = with_lists(vec![
        func(MTy::Int, let_(0, body, let_(1, drop_(0), int(0)))),
        build_list(),
    ]);
    let lib = Library::build(&emit(&p).unwrap()).unwrap();
    let mut instance = Instance::new(4096);
    let run = lib.run_in(&mut instance, NoHost, HOST_VERSION).unwrap();
    assert_eq!(
        run.result,
        Err(Stopped {
            message: HEAP_BUDGET_EXHAUSTED.to_string(),
            site: None
        })
    );
    assert!(instance.is_dead());
}

#[test]
fn a_foreign_string_result_is_copied_into_the_heap() {
    need_clang!();
    let body = let_(
        0,
        Expr::StrLit(DataId(0)),
        let_(
            1,
            Expr::CallForeign(ForeignId(0), vec![Local(0)]),
            let_(
                2,
                Expr::Write(Write::Str(Local(1))),
                let_(
                    3,
                    Expr::Write(Write::End),
                    let_(
                        4,
                        Expr::StrLen(Local(1)),
                        let_(5, drop_(1), let_(6, drop_(0), local(4))),
                    ),
                ),
            ),
        ),
    );
    let mut p = program(vec![func(MTy::Int, body)]);
    p.data = vec![b"hi".to_vec()];
    p.foreign = vec![foreign_fn(
        "shout",
        vec![MTy::Ptr(HeapKind::Str)],
        MTy::Ptr(HeapKind::Str),
    )];
    assert_eq!(verify(&p), Ok(()));
    let run = Library::build(&emit(&p).unwrap())
        .unwrap()
        .run(Recorder::default())
        .unwrap();
    assert_eq!(run.printed, ["hi!", "3"]);
    assert_eq!((run.live_allocs, run.allocations), (0, 1));
    assert_eq!(run.host.calls.len(), 1);
}

#[test]
fn output_writes_reach_the_table() {
    need_clang!();
    let body = let_(
        0,
        Expr::Write(Write::Lit(DataId(0))),
        let_(
            1,
            Expr::Write(Write::Number(Box::new(float(1.5)))),
            let_(
                2,
                Expr::Write(Write::Number(Box::new(int(7)))),
                let_(3, Expr::Write(Write::End), int(0)),
            ),
        ),
    );
    let mut p = program(vec![func(MTy::Int, body)]);
    p.data = vec![b"n=".to_vec()];
    assert_eq!(verify(&p), Ok(()));
    let run = native(&p);
    assert_eq!(run.printed, ["n=1.57", "0"]);
}

/// Source programs without loops (the native backend has no tail calls yet),
/// run by the interpreter, by wasm and natively on both profiles.
const CORPUS: &[&str] = &[
    "mk = program(x, y) do {x: x, y: y} done\na = mk(1.0, 2.0)\nb = mk(3.0, 4.0)\nc = a + b\nc.x + c.y",
    "mk = program(x, y) do {x: x, y: y} done\na = mk(1.0, 2.0)\nb = a + a\nb.x + a.x",
    "mk = program(x, y) do {x: x, y: y} done\nstep = program(q) do {p: q.p + q.v, v: q.v * {x: 0.5, y: 0.5}} done\n\
     a = step({p: mk(1.0, 2.0), v: mk(3.0, 4.0)})\nb = step(a)\nb.p.x + b.p.y + b.v.x",
    "s = \"h\u{e9}llo\"\nbyte_length(s) + char_count(s) + byte_at(s, 3)",
    "s = \"h\u{e9}llo\"\nchar_at(s, 2)",
    "tag Shape = Disc(_) | Block(_) | Dot\n\
     area = program(s) do match s do Disc(r) then r * r Block(w) then w * w Dot then 0.0 done done\n\
     area(Disc(3.0)) + area(Block(2.0)) + area(Dot)",
    "tag Pile = Nil | Cons(_, Pile)\n\
     two = program(p) do match p do Nil then 0 Cons(a, r) then match r do Nil then a Cons(b, m) then a * b done done done\n\
     answer = two(Cons(6, Cons(7, Nil)))\nanswer + 0",
    "tag Pile = Nil | Cons(_, Pile)\n\
     head = program(p) do match p do Nil then \"none\" Cons(a, r) then a done done\n\
     first = head(Cons(\"first\", Cons(\"second\", Nil)))\nfirst",
];

#[test]
fn the_interpreter_wasm_and_native_agree() {
    need_clang!();
    for profile in [Profile::Desktop, Profile::Embedded] {
        for source in CORPUS {
            let host = HostInterface::new(goat_checker::PRELUDE);
            let (expected, live) = interpreted(profile, source);
            let (wasm, _) = goat::compile_for(profile, source, &host).expect("compiles");
            let wasm = goat::native::run(&wasm).expect("wasm runs");
            let run = build(profile, source, &host)
                .unwrap_or_else(|e| panic!("{source}: {e}"))
                .run(NoHost)
                .unwrap();
            assert_eq!(run.result, Ok(()), "{source}");
            assert_eq!(wasm.printed, expected, "wasm on {profile:?}: {source}");
            assert_eq!(run.printed, expected, "native on {profile:?}: {source}");
            // A string result stays allocated for the host to read, so it counts.
            assert_eq!(wasm.live_allocs as usize, live, "wasm on {source}");
            assert_eq!(run.live_allocs as usize, live, "native on {source}");
        }
    }
}

#[test]
fn a_particle_step_makes_the_allocations_the_interpreter_counts() {
    need_clang!();
    // The #544 benchmark's step, applied to unrolled records: the benchmark's own
    // `spawn` and `change_each` loop by tail call, which the native backend
    // does not lower yet.
    let source = "mk = program(x, y) do {x: x, y: y} done
step = program(q) do
  p = q.p + q.v
  v = q.v * {x: 0.999, y: 0.999}
  {p: p, v: {x: v.x, y: v.y}}
done
a = {p: mk(1.0, 2.0), v: mk(3.0, 4.0)}
b = step(step(step(a)))
b.p.x + b.p.y + b.v.x + b.v.y";
    let host = HostInterface::new(goat_checker::PRELUDE);
    let checked = goat_checker::check(source).unwrap();
    let program = goat_mir::mono_for(&checked, Profile::Desktop).unwrap();
    let expected = goat_mir::run(&program).unwrap();
    let run = build(Profile::Desktop, source, &host)
        .unwrap()
        .run(NoHost)
        .unwrap();
    assert_eq!(run.live_allocs, 0);
    assert_eq!(run.allocations, expected.allocations as u64);
    // Two literals, then per step a new velocity and a new particle.
    assert_eq!(run.allocations, 2 + 3 * 2 + 1);
}
