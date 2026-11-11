//! A call through a dot passes the record first: `r.f(a)` is `(r.f)(r, a)`
//! (ADR 0031).

use goat_checker::captures::for_each_node;
use goat_checker::check_with_prelude;
use goat_checker::hir::ExprKind;
use goat_checker::lower::{DotCall, RECEIVER_NAME, ReceiverKind, lower};

fn type_of(source: &str) -> String {
    match check_with_prelude("", source) {
        Ok(checked) => checked.typed.root_ty.to_string(),
        Err(errors) => panic!("should check: {source}\n{errors:?}"),
    }
}

fn first_error(source: &str) -> String {
    match check_with_prelude("", source) {
        Ok(_) => panic!("should not check: {source}"),
        Err(errors) => errors[0].message.clone(),
    }
}

#[test]
fn a_dot_call_with_no_arguments_passes_the_record() {
    assert_eq!(
        type_of("r = {x: 1, f: program(self) do self.x done}\nr.f()"),
        "Number"
    );
}

#[test]
fn a_dot_call_passes_the_record_before_its_arguments() {
    let source = "r = {x: 1, f: program(self, a, b) do self.x + a + b done}\nr.f(2, 3)";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_parenthesised_projection_calls_without_the_record() {
    assert_eq!(
        type_of("r = {f: program(x) do x done};\n(r.f)(true)"),
        "Bool"
    );
    let message = first_error("r = {f: program(x) do x done}\nr.f(true)");
    assert!(message.contains("argument"), "{message}");
}

#[test]
fn a_bare_projection_stays_a_field_access() {
    let record = "r = {x: 1, f: program(self) do self.x done}\n";
    assert_eq!(type_of(&format!("{record}r.x")), "Number");
    check_with_prelude("", &format!("{record}r.f")).expect("checks");
}

#[test]
fn a_path_receiver_repeats_through_every_field() {
    assert_eq!(
        type_of("a = {b: {n: 5, c: program(self, x) do self.n + x done}}\na.b.c(1)"),
        "Number"
    );
    assert_eq!(
        type_of("o = {inner: {x: 4, y: program(self) do self.x done}}\no.inner.y()"),
        "Number"
    );
}

#[test]
fn only_the_call_right_after_an_access_is_a_dot_call() {
    let source = "r = {n: 1, f: program(self, x) do program(y) do self.n + x + y done done}\n\
                  r.f(1)(2)";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_negated_dot_call_negates_the_result() {
    let source = "r = {n: 1, f: program(self, x) do self.n + x done};\n-r.f(2)";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_computed_receiver_is_bound_once_to_a_hidden_name() {
    let lowered =
        lower("make = program() do {f: program(s) do 0 done} done\nmake().f()").expect("parses");
    let mut calls_of_make = 0;
    let mut hidden_binders = 0;
    for_each_node(&lowered.root, &mut |e| match &e.kind {
        ExprKind::App { callee, .. } if matches!(&callee.kind, ExprKind::Var { name, .. } if name == "make") =>
        {
            calls_of_make += 1;
        }
        ExprKind::Let { name, .. } if name == RECEIVER_NAME => hidden_binders += 1,
        _ => {}
    });
    assert_eq!((calls_of_make, hidden_binders), (1, 1));
}

#[test]
fn a_computed_receiver_has_one_fixed_type_so_it_cannot_take_itself() {
    let message = first_error("make = program() do {f: program(s) do 0 done} done\nmake().f()");
    assert!(message.contains("infinite type"), "{message}");
}

fn dot_calls(source: &str) -> Vec<DotCall> {
    lower(source)
        .expect("parses")
        .dot_calls
        .into_values()
        .collect()
}

#[test]
fn the_side_table_records_each_dot_call() {
    assert_eq!(
        dot_calls("r = {o: {f: program(s) do 0 done}}\nr.o.f()"),
        [DotCall {
            receiver_text: "r.o".into(),
            label: "f".into(),
            receiver_kind: ReceiverKind::Path,
        }]
    );
    assert_eq!(
        dot_calls("mk = program() do {f: program(s) do 0 done} done\nmk().f()"),
        [DotCall {
            receiver_text: "mk()".into(),
            label: "f".into(),
            receiver_kind: ReceiverKind::Computed,
        }]
    );
    assert!(dot_calls("r = {f: program(s) do 0 done}\n(r.f)(1)").is_empty());
}
