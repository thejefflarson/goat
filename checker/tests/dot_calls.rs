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

fn first_diagnostic(source: &str) -> (String, String) {
    let Err(errors) = check_with_prelude("", source) else {
        panic!("should not check: {source}")
    };
    let span = errors[0].span;
    (
        errors[0].message.clone(),
        source[span.start..span.end].to_string(),
    )
}

#[test]
fn a_method_with_no_parameter_for_the_record_says_so() {
    let source = "ball = {x: 1, moved: program() do 0 done}\nball.moved()";
    assert_eq!(
        first_diagnostic(source),
        (
            "`ball.moved()` hands `ball` to `moved` as its first argument, but `moved` has no parameter for it. \
             Add one first, like `program(self) do … done`, or write `(ball.moved)()` to call it without `ball`."
                .to_string(),
            "ball.moved()".to_string()
        )
    );
}

#[test]
fn a_method_missing_only_self_names_how_many_it_takes() {
    let source = "ball = {x: 1, moved: program(dt) do dt done}\nball.moved(2)";
    assert_eq!(
        first_diagnostic(source),
        (
            "`ball.moved()` hands `ball` to `moved` as its first argument, but `moved` takes only 1 argument. \
             Add `self` first, like `program(self, …)`, or write `(ball.moved)()` to call it without `ball`."
                .to_string(),
            "ball.moved(2)".to_string()
        )
    );
}

#[test]
fn passing_the_receiver_again_says_the_dot_already_did() {
    let source = "ball = {x: 1, moved: program(self) do self.x done}\nball.moved(ball)";
    assert_eq!(
        first_diagnostic(source),
        (
            "`ball.moved(ball)` already hands `ball` over: the dot does it. Write `ball.moved()`."
                .to_string(),
            "ball.moved(ball)".to_string()
        )
    );
}

#[test]
fn a_count_that_is_off_by_more_than_the_receiver_counts_it() {
    let source = "ball = {x: 1, moved: program(self, dt) do dt done}\nball.moved(1, 2, 3)";
    assert_eq!(
        first_diagnostic(source),
        (
            "`ball.moved(…)` hands `ball` to `moved` first, so it passes 4 arguments, but `moved` takes 2."
                .to_string(),
            "ball.moved(1, 2, 3)".to_string()
        )
    );
}

#[test]
fn a_computed_receiver_may_take_itself() {
    let source = "make = program() do {f: program(s) do 0 done} done\nmake().f()";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_method_whose_type_would_contain_itself_is_named_without_type_variables() {
    let source = "f = program(x) do x.m(x.m) done  1";
    let (message, covered) = first_diagnostic(source);
    assert_eq!(
        message,
        "`x.m(…)` hands `x` to `m`, but then the type of `m` would have to contain itself."
    );
    assert_eq!(covered, "x.m(x.m)");
    assert!(!message.contains('μ') && !message.contains("infinite"));
}

#[test]
fn a_call_that_is_not_a_dot_call_keeps_the_plain_count_message() {
    let (message, _) = first_diagnostic("r = {f: program(x) do x done};\n(r.f)(1, 2)");
    assert_eq!(message, "function expects 1 argument(s) but got 2");
}

fn dot_calls(source: &str) -> Vec<(String, DotCall)> {
    let mut calls: Vec<_> = lower(source)
        .expect("parses")
        .dot_calls
        .into_values()
        .map(|call| {
            (
                source[call.receiver.start..call.receiver.end].to_string(),
                call,
            )
        })
        .collect();
    calls.sort_by_key(|(_, call)| call.receiver.end);
    calls
}

#[test]
fn the_side_table_records_each_dot_call() {
    let [(receiver, call)] = &dot_calls("r = {o: {f: program(s) do 0 done}}\nr.o.f()")[..] else {
        panic!("one dot call")
    };
    assert_eq!(
        (receiver.as_str(), call.label.as_str(), call.receiver_kind),
        ("r.o", "f", ReceiverKind::Path)
    );
    let [(receiver, call)] =
        &dot_calls("mk = program() do {f: program(s) do 0 done} done\nmk().f()")[..]
    else {
        panic!("one dot call")
    };
    assert_eq!(
        (receiver.as_str(), call.label.as_str(), call.receiver_kind),
        ("mk()", "f", ReceiverKind::Computed)
    );
    assert!(dot_calls("r = {f: program(s) do 0 done}\n(r.f)(1)").is_empty());
}

#[test]
fn a_dot_call_chain_records_each_receiver_as_a_span_of_the_prefix() {
    let links = 200;
    let binding = "r = {f: program(s) do s done}\n";
    let source = format!("{binding}r{}", ".f()".repeat(links));
    let calls = dot_calls(&source);
    assert_eq!(calls.len(), links);
    let start = binding.len();
    for (k, (_, call)) in calls.iter().enumerate() {
        assert_eq!(
            (call.receiver.start, call.receiver.end),
            (start, start + 1 + 4 * k)
        );
    }
}

fn plain_apps(source: &str) -> Vec<(String, usize)> {
    let mut apps = Vec::new();
    for_each_node(&lower(source).expect("parses").root, &mut |e| {
        if let ExprKind::App { callee, args } = &e.kind
            && let ExprKind::Field { record, label } = &callee.kind
            && let ExprKind::Var { name, .. } = &record.kind
        {
            apps.push((format!("{name}.{label}"), args.len()));
        }
    });
    apps
}

#[test]
fn a_take_call_lowers_to_the_parenthesised_projection_call() {
    let record = "t = {double: program(x) do x * 2 done};\n";
    let taken = format!("{record}t::double(5)");
    let parenthesised = format!("{record}(t.double)(5)");
    assert_eq!(plain_apps(&taken), [("t.double".to_string(), 1)]);
    assert_eq!(plain_apps(&taken), plain_apps(&parenthesised));
    assert!(dot_calls(&taken).is_empty());
    assert_eq!(type_of(&taken), type_of(&parenthesised));
}

#[test]
fn a_take_on_a_method_passes_the_record_explicitly() {
    let record = "ball = {x: 1, moved: program(self) do self.x done}\n\
                  other = {x: 10}\n";
    let call = format!("{record}ball::moved(other)");
    assert_eq!(plain_apps(&call), [("ball.moved".to_string(), 1)]);
    assert_eq!(type_of(&call), "Number");
    let message = first_error(&format!("{record}ball::moved()"));
    assert_eq!(message, "function expects 1 argument(s) but got 0");
}

#[test]
fn a_bare_take_is_the_function_value() {
    let record = "r = {f: program(x) do x done}\n";
    assert_eq!(type_of(&format!("{record}g = r::f\ng(true)")), "Bool");
}

#[test]
fn a_take_of_a_data_field_says_to_read_it_with_a_dot() {
    for (source, label) in [
        ("r = {x: 1}\nr::x", "x"),
        ("r = {x: 1}\nr::x(2)", "x"),
        ("r = {name: \"goat\"}\nr::name", "name"),
        ("r = {inner: {x: 1}}\nr::inner", "inner"),
    ] {
        let (message, quoted) = first_diagnostic(source);
        assert_eq!(
            message,
            format!("`{label}` isn't a function, so read it with `r.{label}`"),
            "{source}"
        );
        assert_eq!(quoted, format!("r::{label}"), "{source}");
    }
}

#[test]
fn a_take_on_a_path_receiver_quotes_the_whole_receiver() {
    let (message, quoted) = first_diagnostic("a = {b: {n: 1}}\na.b::n");
    assert_eq!(message, "`n` isn't a function, so read it with `a.b.n`");
    assert_eq!(quoted, "a.b::n");
}

#[test]
fn a_take_whose_field_type_is_decided_later_is_not_an_error() {
    assert_eq!(
        type_of("call = program(r) do r::f(1) done\ncall({f: program(x) do x done})"),
        "Number"
    );
}
