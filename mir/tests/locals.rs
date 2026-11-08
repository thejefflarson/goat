//! The `locals` table mono records on each function must agree with the type
//! a walk over the function's body gives the same binder.

mod common;

use common::infer_locals;
use goat_checker::check;
use goat_mir::*;
use std::fs;
use std::path::Path;

fn assert_table_matches_walk(name: &str, program: &Program) {
    let mut walked = program.clone();
    infer_locals(&mut walked);
    for (i, (func, walked)) in program.funcs.iter().zip(&walked.funcs).enumerate() {
        for (local, ty) in &func.locals {
            if let Some(found) = walked.locals.get(local) {
                assert_eq!(found, ty, "{name}: func {i}, local {}", local.0);
            }
        }
    }
}

#[test]
fn mono_locals_agree_with_a_walk_of_every_example() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples");
    let mut checked = 0;
    for entry in fs::read_dir(dir).expect("examples dir") {
        let path = entry.expect("entry").path();
        if path.extension().is_none_or(|e| e != "goat") {
            continue;
        }
        let name = path.display().to_string();
        let src = fs::read_to_string(&path).expect("example source");
        let Ok(c) = check(&src) else { continue };
        let program = mono(&c).expect("example lowers");
        assert_table_matches_walk(&name, &program);
        checked += 1;
    }
    assert!(checked > 10, "only {checked} examples were checked");
}

#[test]
fn mono_records_a_type_for_every_pointer_binder() {
    let src = "tag Box\nb = Box(1)\nr = {x: 1, y: \"s\"}\nmatch b do Box(n) then r.y done";
    let program = mono(&check(src).expect("checks")).expect("lowers");
    assert_table_matches_walk("inline", &program);
    let entry = &program.funcs[0];
    assert!(
        entry.locals.values().any(|t| t.is_ptr()),
        "{:?}",
        entry.locals
    );
}

#[test]
fn a_printed_function_is_bound_at_its_closure_type() {
    let program = mono(&check("print(program(x) do x done)").expect("checks")).expect("lowers");
    assert_table_matches_walk("print function", &program);
    assert_eq!(verify(&program), Ok(()));
}

#[test]
fn only_a_non_string_pointer_root_is_discarded() {
    let discarded = [
        MTy::Ptr(HeapKind::Record(LayoutId(0))),
        MTy::Ptr(HeapKind::Variant(LayoutId(0))),
        MTy::Ptr(HeapKind::Closure(SigId(0))),
        MTy::Ptr(HeapKind::List(LayoutId(0))),
    ];
    let kept = [
        MTy::Int,
        MTy::Float,
        MTy::Bool,
        MTy::Unit,
        MTy::Ptr(HeapKind::Str),
    ];
    assert!(discarded.iter().all(|t| t.is_discarded_root()));
    assert!(kept.iter().all(|t| !t.is_discarded_root()));
}
