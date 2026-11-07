#[path = "../../mir/tests/common/mod.rs"]
mod common;

use common::*;
use goat_mir::*;
use goat_wasm::{EmitError, emit};

fn emit_valid(p: &Program) -> Vec<u8> {
    assert_eq!(verify(p), Ok(()));
    let bytes = emit(p).expect("program emits");
    wasmparser::Validator::new_with_features(
        wasmparser::WasmFeatures::default() | wasmparser::WasmFeatures::TAIL_CALL,
    )
    .validate_all(&bytes)
    .expect("module validates");
    bytes
}

fn wat(p: &Program) -> String {
    wasmprinter::print_bytes(emit_valid(p)).expect("prints")
}

/// The text of function `index`, up to the next function.
fn func_body(text: &str, index: u32) -> &str {
    let start = text
        .find(&format!("(func (;{index};)"))
        .expect("function exists");
    let rest = &text[start..];
    let len = rest[1..].find("(func (;").map_or(rest.len(), |n| n + 1);
    &rest[..len]
}

fn golden(name: &str, p: &Program) {
    let actual = wat(p);
    let path = format!("{}/tests/golden/{name}.wat", env!("CARGO_MANIFEST_DIR"));
    if std::env::var_os("UPDATE_GOLDEN").is_some() {
        std::fs::write(&path, &actual).unwrap();
    }
    let expected = std::fs::read_to_string(&path).expect("golden file exists");
    assert_eq!(
        actual, expected,
        "run with UPDATE_GOLDEN=1 to refresh {path}"
    );
}

fn arithmetic() -> Program {
    let body = let_(
        0,
        bin_float(FloatOp::Add, float(1.5), float(2.5)),
        bin_float(FloatOp::Mul, local(0), float(2.0)),
    );
    program(vec![func(MTy::Float, body)])
}

fn conditional() -> Program {
    let body = let_(
        0,
        float(3.0),
        if_(
            cmp(CmpOp::Lt, local(0), float(5.0)),
            bin_float(FloatOp::Sub, local(0), float(1.0)),
            Expr::Trap("unreachable branch".into()),
        ),
    );
    program(vec![func(MTy::Float, body)])
}

fn fib() -> Program {
    let n = || local(0);
    let fib_body = if_(
        cmp(CmpOp::Lt, n(), int(2)),
        n(),
        add(
            call(1, vec![sub(n(), int(1))]),
            call(1, vec![sub(n(), int(2))]),
        ),
    );
    program(vec![
        func(MTy::Int, call(1, vec![int(10)])),
        func_with(vec![(0, MTy::Int)], MTy::Int, fib_body),
    ])
}

#[test]
fn arithmetic_matches_golden() {
    golden("arithmetic", &arithmetic());
}

#[test]
fn conditional_matches_golden() {
    golden("conditional", &conditional());
}

#[test]
fn recursive_fib_matches_golden() {
    golden("fib", &fib());
}

#[test]
fn comparison_roots_print_bool() {
    let ints = program(vec![func(MTy::Bool, cmp(CmpOp::Ge, int(3), int(2)))]);
    let floats = program(vec![func(
        MTy::Bool,
        cmp(CmpOp::Ne, float(1.0), float(2.0)),
    )]);
    for p in [ints, floats] {
        let text = wat(&p);
        assert!(text.contains("call 1"), "{text}");
    }
}

#[test]
fn every_comparison_operator_validates() {
    use CmpOp::*;
    for op in [Eq, Ne, Lt, Le, Gt, Ge] {
        emit_valid(&program(vec![func(MTy::Bool, cmp(op, int(1), int(2)))]));
        emit_valid(&program(vec![func(
            MTy::Bool,
            cmp(op, float(1.0), float(2.0)),
        )]));
    }
}

#[test]
fn unit_root_prints_nothing() {
    let p = program(vec![func(MTy::Unit, Expr::Const(Const::Unit))]);
    let text = wat(&p);
    assert!(
        !text.contains("call 0") && !text.contains("call 1"),
        "{text}"
    );
}

#[test]
fn unit_values_are_erased_through_let_and_calls() {
    let side_effect = func(MTy::Unit, Expr::Const(Const::Unit));
    let root = func(
        MTy::Float,
        let_(0, call(1, vec![]), let_(1, local(0), float(7.0))),
    );
    emit_valid(&program(vec![root, side_effect]));
}

#[test]
fn trap_in_value_position_validates() {
    let body = bin_float(FloatOp::Add, float(1.0), Expr::Trap("boom".into()));
    emit_valid(&program(vec![func(MTy::Float, body)]));
    let both = if_(
        boolean(true),
        Expr::Trap("a".into()),
        Expr::Trap("b".into()),
    );
    emit_valid(&program(vec![func(MTy::Float, both)]));
}

#[test]
fn module_shape() {
    let text = wat(&arithmetic());
    for expected in [
        "(import \"goat\" \"print_number\" (func (;0;) (type 0) (param f64)))",
        "(import \"goat\" \"print_bool\" (func (;1;) (type 1) (param i32)))",
        "(memory (;0;) 1)",
        "(global (;0;) (mut i32) i32.const 232)",
        "(global (;1;) (mut i32) i32.const 0)",
        "(export \"goat_alloc\" (func 4))",
        "(export \"goat_live_allocs\" (func 6))",
        "(export \"memory\" (memory 0))",
        "(export \"goat_entry\" (func 3))",
        "(data (;0;) (i32.const 8) \"\")",
    ] {
        assert!(text.contains(expected), "missing {expected}\n{text}");
    }
}

#[test]
fn heap_starts_after_the_aligned_data_segment() {
    let mut p = arithmetic();
    p.data = vec![vec![0; 13]];
    let text = wat(&p);
    assert!(
        text.contains("(global (;0;) (mut i32) i32.const 264)"),
        "{text}"
    );
}

#[test]
fn memory_covers_data_segments_past_one_page() {
    let mut p = arithmetic();
    p.data = vec![vec![0; 3 * 65536]];
    let text = wat(&p);
    assert!(text.contains("(memory (;0;) 4)"), "{text}");
}

#[test]
fn unsupported_heap_objects_and_bad_callees_are_rejected() {
    let reuse = program(vec![func(
        MTy::Int,
        let_(
            0,
            Expr::AllocVariant(VARIANT, 0, vec![]),
            Expr::Unpack(Local(0), 0, vec![], Box::new(int(0))),
        ),
    )]);
    assert!(matches!(emit(&reuse), Err(EmitError::Unsupported(_))));
    let not_a_closure = program(vec![func(MTy::Int, call_closure(int(0), vec![]))]);
    assert!(matches!(emit(&not_a_closure), Err(EmitError::Malformed(_))));
}

fn closures(funcs: Vec<Func>, sig_params: Vec<MTy>) -> Program {
    with_closures(program(funcs), sig_params)
}

/// `double(x) = x * 2`, taking and dropping its environment.
fn double() -> Func {
    closure_fn(
        vec![(0, MTy::Int)],
        1,
        vec![],
        MTy::Int,
        let_(2, drop_(1), mul(local(0), int(2))),
    )
}

/// `\x -> x + k` with `k` captured.
fn add_k() -> Func {
    closure_fn(
        vec![(0, MTy::Int)],
        1,
        vec![MTy::Int],
        MTy::Int,
        let_(
            2,
            Expr::Capture(0),
            let_(3, drop_(1), add(local(0), local(2))),
        ),
    )
}

fn apply_double() -> Program {
    let apply = func_with(
        vec![(0, closure_ty(0)), (1, MTy::Int)],
        MTy::Int,
        call_closure(local(0), vec![local(1)]),
    );
    let main = func(
        MTy::Int,
        call(2, vec![Expr::MakeClosure(FuncId(1), vec![]), int(21)]),
    );
    closures(vec![main, double(), apply], vec![MTy::Int])
}

fn record_of_functions() -> Program {
    let main = func(
        MTy::Int,
        let_(
            0,
            Expr::AllocRecord(
                FNS,
                vec![
                    Expr::MakeClosure(FuncId(1), vec![]),
                    Expr::MakeClosure(FuncId(2), vec![int(10)]),
                ],
            ),
            let_(
                1,
                call_closure(Expr::Field(Local(0), 0), vec![int(7)]),
                let_(
                    2,
                    call_closure(Expr::Field(Local(0), 1), vec![local(1)]),
                    let_(3, drop_(0), local(2)),
                ),
            ),
        ),
    );
    closures(vec![main, double(), add_k()], vec![MTy::Int])
}

fn capturing_a_record() -> Program {
    let body = closure_fn(
        vec![(0, MTy::Int)],
        1,
        vec![record_ty()],
        MTy::Int,
        let_(
            2,
            Expr::Capture(0),
            let_(
                3,
                Expr::Field(Local(2), 0),
                let_(4, drop_(2), let_(5, drop_(1), add(local(3), local(0)))),
            ),
        ),
    );
    let main = func(
        MTy::Int,
        let_(
            0,
            alloc_record(7),
            let_(
                1,
                Expr::MakeClosure(FuncId(1), vec![local(0)]),
                let_(
                    2,
                    Expr::Dup(Local(1)),
                    let_(
                        3,
                        call_closure(local(1), vec![int(5)]),
                        let_(
                            4,
                            call_closure(local(1), vec![int(1)]),
                            add(local(3), local(4)),
                        ),
                    ),
                ),
            ),
        ),
    );
    closures(vec![main, body], vec![MTy::Int])
}

/// `go(n, acc) = if n == 0 then acc else go(n - 1, acc + k)` through `env`.
fn tail_recursive_closure() -> Program {
    let go = closure_fn(
        vec![(0, MTy::Int), (1, MTy::Int)],
        2,
        vec![MTy::Int],
        MTy::Int,
        if_(
            cmp(CmpOp::Eq, local(0), int(0)),
            let_(3, drop_(2), local(1)),
            let_(
                4,
                Expr::Capture(0),
                Expr::TailCall(
                    Callee::Closure(Box::new(local(2))),
                    vec![sub(local(0), int(1)), add(local(1), local(4))],
                ),
            ),
        ),
    );
    let main = func(
        MTy::Int,
        let_(
            0,
            Expr::MakeClosure(FuncId(1), vec![int(3)]),
            call_closure(local(0), vec![int(1000), int(0)]),
        ),
    );
    closures(vec![main, go], vec![MTy::Int, MTy::Int])
}

fn tail_recursive_direct() -> Program {
    let count = func_with(
        vec![(0, MTy::Int), (1, MTy::Int)],
        MTy::Int,
        if_(
            cmp(CmpOp::Eq, local(0), int(0)),
            local(1),
            Expr::TailCall(
                Callee::Direct(FuncId(1)),
                vec![sub(local(0), int(1)), add(local(1), int(2))],
            ),
        ),
    );
    program(vec![
        func(MTy::Int, call(1, vec![int(1000000), int(0)])),
        count,
    ])
}

fn point_sum() -> Program {
    let mut p = program(vec![func(
        MTy::Int,
        let_(
            0,
            Expr::AllocRecord(LayoutId(2), vec![int(3), int(4)]),
            let_(
                1,
                add(Expr::Field(Local(0), 0), Expr::Field(Local(0), 1)),
                let_(2, drop_(0), local(1)),
            ),
        ),
    )]);
    p.layouts.push(Layout::Record(vec![MTy::Int, MTy::Int]));
    p
}

#[test]
fn standalone_record_matches_golden() {
    golden("point_sum", &point_sum());
}

#[test]
fn allocator_runtime_is_exported_and_records_allocate_and_free_through_it() {
    let text = wat(&point_sum());
    for expected in [
        "(export \"goat_alloc\" (func 4))",
        "(export \"goat_live_allocs\" (func 6))",
    ] {
        assert!(text.contains(expected), "missing {expected}\n{text}");
    }
    let root = func_body(&text, 2);
    assert!(
        root.contains("call 4"),
        "allocates through goat_alloc\n{root}"
    );
    assert!(
        root.contains("call 7"),
        "releases through drop_loop\n{root}"
    );
    assert!(
        func_body(&text, 7).contains("call 5"),
        "drop_loop frees the block\n{text}"
    );
    assert!(
        func_body(&text, 5).contains("memory.fill"),
        "free poisons the block\n{text}"
    );
}

#[test]
fn apply_double_matches_golden() {
    golden("apply_double", &apply_double());
}

#[test]
fn static_closure_is_immortal_and_indexed_through_the_table() {
    let text = wat(&apply_double());
    for expected in [
        "(table (;0;) 2 2 funcref)",
        "(elem (;0;) (table 0) (i32.const 0) func",
        "call_indirect (type 4)",
        "(data (;0;) (i32.const 8) \"\\ff\\ff\\ff\\ff\\00\\00\\00\\00",
    ] {
        assert!(text.contains(expected), "missing {expected}\n{text}");
    }
}

#[test]
fn a_function_value_used_twice_shares_one_static_closure() {
    let mut p = apply_double();
    p.funcs[0].body = add(
        call(2, vec![Expr::MakeClosure(FuncId(1), vec![]), int(1)]),
        call(2, vec![Expr::MakeClosure(FuncId(1), vec![]), int(2)]),
    );
    let text = wat(&p);
    let root = func_body(&text, 2);
    assert_eq!(root.matches("i32.const 8\n").count(), 2, "{text}");
    assert!(!root.contains("i32.const 24\n"), "{text}");
}

#[test]
fn record_of_functions_validates() {
    let text = wat(&record_of_functions());
    assert_eq!(text.matches("call_indirect").count(), 3, "{text}");
}

#[test]
fn closure_capturing_a_record_validates() {
    emit_valid(&capturing_a_record());
}

#[test]
fn tail_calls_through_a_closure_become_return_call_indirect() {
    let text = wat(&tail_recursive_closure());
    assert!(text.contains("return_call_indirect"), "{text}");
}

#[test]
fn direct_tail_recursion_becomes_return_call() {
    let text = wat(&tail_recursive_direct());
    assert!(text.contains("return_call 3"), "{text}");
}

fn mono_program(src: &str) -> Program {
    let checked = goat_checker::check(src).expect("program type-checks");
    mono(&checked).expect("program monomorphizes")
}

#[test]
fn mono_capturing_closure_matches_golden() {
    let p = mono_program("add = program(a) do program(b) do a + b done done  add(1)(2)");
    golden("capturing_closure", &p);
}

const STR: MTy = MTy::Ptr(HeapKind::Str);

fn string_root() -> Program {
    let mut p = program(vec![func(STR, Expr::StrLit(DataId(0)))]);
    p.data = vec![b"hi".to_vec()];
    p
}

#[test]
fn string_root_matches_golden() {
    golden("string", &string_root());
}

#[test]
fn string_literals_are_immortal_objects_in_the_data_segment() {
    let mut p = program(vec![func(STR, Expr::StrLit(DataId(1)))]);
    p.data = vec![b"hi".to_vec(), b"hello world".to_vec()];
    let text = wat(&p);
    let object = |rc: &str, len: &str, bytes: &str, pad: &str| format!("{rc}{len}{bytes}{pad}");
    let first = object(
        "\\ff\\ff\\ff\\ff\\00\\00\\00\\00",
        "\\02\\00\\00\\00",
        "hi",
        "\\00\\00",
    );
    let second = object(
        "\\ff\\ff\\ff\\ff\\00\\00\\00\\00",
        "\\0b\\00\\00\\00",
        "hello world",
        "\\00",
    );
    assert!(
        text.contains(&format!("{first}{second}")),
        "objects are 8-aligned and adjacent\n{text}"
    );
    assert!(
        func_body(&text, 3).contains("i32.const 24"),
        "second literal address\n{text}"
    );
    assert!(
        text.contains("(global (;0;) (mut i32) i32.const 272)"),
        "{text}"
    );
}

#[test]
fn print_string_is_imported_only_for_a_string_root() {
    let with = wat(&string_root());
    assert!(
        with.contains("(import \"goat\" \"print_string\" (func (;2;) (type 1) (param i32)))"),
        "{with}"
    );
    assert!(with.contains("call 2"), "{with}");
    for other in [arithmetic(), point_sum(), apply_double()] {
        assert!(!wat(&other).contains("print_string"));
    }
}

#[test]
fn string_programs_shift_every_function_index_by_the_extra_import() {
    let mut p = program(vec![
        func(STR, call(1, vec![])),
        func(STR, Expr::StrLit(DataId(0))),
    ]);
    p.data = vec![b"hi".to_vec()];
    let text = wat(&p);
    assert!(
        text.contains("call 4"),
        "callee is func 1 + 3 imports\n{text}"
    );
    assert!(text.contains("(export \"goat_entry\" (func 5))"), "{text}");
}

#[test]
fn string_programs_index_closure_bodies_past_three_imports() {
    let mut p = apply_double();
    p.funcs[0] = func(
        STR,
        let_(
            0,
            call(2, vec![Expr::MakeClosure(FuncId(1), vec![]), int(21)]),
            Expr::StrLit(DataId(0)),
        ),
    );
    p.data = vec![b"hi".to_vec()];
    let text = wat(&p);
    assert!(
        text.contains("call 5"),
        "apply is func 2 + 3 imports\n{text}"
    );
    assert!(
        text.contains("(i32.const 0) func 11 4"),
        "table holds the noop helper (func 11) and double (func 1 + 3 imports)\n{text}"
    );
}

#[test]
fn dropping_a_string_local_emits() {
    let body = let_(
        0,
        Expr::StrLit(DataId(0)),
        let_(1, drop_(0), Expr::StrLit(DataId(0))),
    );
    let mut p = program(vec![func(STR, body)]);
    p.data = vec![b"hi".to_vec()];
    emit_valid(&p);
}

#[test]
fn a_missing_data_entry_is_malformed() {
    let p = program(vec![func(STR, Expr::StrLit(DataId(0)))]);
    assert!(matches!(emit(&p), Err(EmitError::Malformed(_))));
}

#[test]
fn only_a_string_heap_root_is_printable() {
    let p = program(vec![func(record_ty(), alloc_record(1))]);
    assert!(matches!(emit(&p), Err(EmitError::Unsupported(_))));
}

#[test]
fn mono_string_programs_emit_valid_modules() {
    for src in [
        "\"hi\"",
        "s = \"hi\"  s",
        "id = program(x) do x done  id(\"hi\")",
        "pick = program(b) do if b then \"hi\" else \"yo\" done done  pick(true)",
    ] {
        let text = wat(&mono_program(src));
        assert!(text.contains("print_string"), "{src}\n{text}");
    }
}

const LENGTH: &str = "length = program(xs) do match xs do Empty then 0 \
                      Link(first, rest) then 1 + length(rest) done done ";

#[test]
fn mono_variant_length_matches_golden() {
    golden(
        "variant_length",
        &mono_program(&format!("{LENGTH} length(Link(1, Empty))")),
    );
}

#[test]
fn variant_programs_validate() {
    for src in [
        "tag Circle Circle(5)",
        "tag Circle match Circle(5) do Circle(r) then r else 0 done",
        "tag A tag B f = program(s) do match s do A then 1 B then 2 done done f(B)",
        "tag Leaf tag Node size = program(t) do match t do Leaf then 1 \
         Node(l, r) then size(l) + size(r) done done size(Node(Leaf, Leaf))",
        "map = program(f, xs) do match xs do Empty then Empty \
         Link(x, rest) then Link(f(x), map(f, rest)) done done \
         map(program(n) do n + 1 done, Link(1, Empty))",
        "tag Pair f = program(p) do match p do Pair(a, b) then a + b done done f(Pair(1, 2))",
    ] {
        emit_valid(&mono_program(src));
    }
}

#[test]
fn nullary_tags_are_immortal_cells_in_the_data_segment() {
    let text = wat(&mono_program(&format!("{LENGTH} length(Link(1, Empty))")));
    assert!(
        text.contains(
            "(data (;0;) (i32.const 8) \"\\ff\\ff\\ff\\ff\\00\\00\\00\\00\\00\\00\\00\\00\\00\\00\\00\\00\")"
        ),
        "{text}"
    );
}

#[test]
fn a_trap_calls_the_host_with_its_message_before_halting() {
    let text = wat(&mono_program("x = 1\nfirst([]) + x"));
    assert!(text.contains("(import \"goat\" \"trap\""), "{text}");
    assert!(text.contains("first of an empty list"), "{text}");
    assert!(text.contains("global.set 3"), "{text}");
    assert!(text.contains("(export \"goat_site\""), "{text}");
    assert!(text.contains("(@custom \"goat.sites\""), "{text}");
}

#[test]
fn a_program_that_cannot_trap_imports_no_trap() {
    let text = wat(&mono_program("1 + 2"));
    assert!(!text.contains("\"goat\" \"trap\""), "{text}");
}

#[test]
fn matching_a_variant_branches_on_its_tag_through_a_table() {
    let text = wat(&mono_program(&format!("{LENGTH} length(Link(1, Empty))")));
    assert!(text.contains("br_table"), "{text}");
}
