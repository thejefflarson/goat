//! A tag written without a payload takes whatever it is given, a fresh type at
//! each construction, so a group of such tags is generic and a kid can define
//! a list in pure goat. Every tag is in a closed group; a lone tag is a group
//! of one.

use goat_checker::{GoatError, PRELUDE, check, check_with_prelude};

fn errors_of(source: &str) -> Vec<GoatError> {
    match check(source) {
        Ok(_) => panic!("should not check: {source}"),
        Err(errors) => errors,
    }
}

fn first_error(source: &str) -> (String, String) {
    let error = errors_of(source).remove(0);
    let text = source[error.span.start..error.span.end].to_string();
    (error.message, text)
}

fn type_of(source: &str) -> String {
    check(source)
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .typed
        .root_ty
        .to_string()
}

const PILE: &str = "tag Pile = Nil | Cons \
    size = program(xs) do match xs do Nil then 0 Cons(head, rest) then 1 + size(rest) done done ";

#[test]
fn one_user_list_function_counts_numbers_and_words() {
    let both = format!("{PILE} size(Cons(1, Cons(2, Nil))) + size(Cons(\"a\", Nil))");
    assert_eq!(type_of(&both), "Number");
}

#[test]
fn a_user_list_may_hold_lists() {
    let nested = format!("{PILE} size(Cons(Cons(1, Nil), Cons(Cons(2, Nil), Nil)))");
    assert_eq!(type_of(&nested), "Number");
}

#[test]
fn a_user_list_never_mixes_element_types_where_it_is_walked() {
    let source = format!("{PILE} size(Cons(1, Cons(\"a\", Nil)))");
    let (message, text) = first_error(&source);
    assert!(message.contains("type mismatch"), "{message}");
    assert!(text.starts_with("size("), "{text}");
}

#[test]
fn a_function_over_a_user_list_keeps_the_element_type() {
    let source = "tag Pile = Nil | Cons \
        first_or = program(xs, fallback) do match xs do Nil then fallback Cons(head, rest) then head done done \
        first_or(Cons(1, Nil), 0) + first_or(Nil, 5)";
    assert_eq!(type_of(source), "Number");
    let mixed = "tag Pile = Nil | Cons \
        first_or = program(xs, fallback) do match xs do Nil then fallback Cons(head, rest) then head done done \
        first_or(Cons(1, Nil), \"none\")";
    assert!(errors_of(mixed)[0].message.contains("type mismatch"));
}

#[test]
fn a_maybe_holds_one_value_of_any_type() {
    let source = "tag Maybe = Nothing | Just \
        or_else = program(m, fallback) do match m do Nothing then fallback Just(v) then v done done \
        or_else(Just(3), 0) + or_else(Nothing, 1)";
    assert_eq!(type_of(source), "Number");
    let words = "tag Maybe = Nothing | Just \
        or_else = program(m, fallback) do match m do Nothing then fallback Just(v) then v done done \
        or_else(Just(\"hi\"), \"\")";
    assert_eq!(type_of(words), "String");
    let wrong = "tag Maybe = Nothing | Just \
        or_else = program(m, fallback) do match m do Nothing then fallback Just(v) then v done done \
        or_else(Just(3), \"\")";
    assert!(errors_of(wrong)[0].message.contains("type mismatch"));
}

#[test]
fn a_user_tree_is_generic_in_what_it_holds() {
    let source = "tag Tree = Leaf | Node \
        total = program(t) do match t do Leaf then 0 Node(l, v, r) then total(l) + v + total(r) done done \
        count = program(t) do match t do Leaf then 0 Node(l, v, r) then count(l) + 1 + count(r) done done \
        total(Node(Leaf, 1, Node(Leaf, 2, Leaf))) + count(Node(Leaf, \"a\", Leaf))";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_match_over_a_user_group_handles_every_tag() {
    let (message, _) = first_error(
        "tag Pile = Nil | Cons \
         size = program(xs) do match xs do Cons(head, rest) then 1 + size(rest) done done \
         size(Cons(1, Nil))",
    );
    assert!(message.contains("`Nil`"), "{message}");
    let covered = "tag Pile = Nil | Cons \
         size = program(xs) do match xs do Cons(head, rest) then 1 + size(rest) else 0 done done \
         size(Cons(1, Nil))";
    assert!(check(covered).is_ok());
}

#[test]
fn a_tag_used_with_no_argument_has_no_payload_at_that_use() {
    assert_eq!(type_of("tag Light = Red | Green Red"), "[Red, Green]");
    let source = "tag Light = Red | Green \
        f = program(l) do match l do Red then 1 Green then 2 done done \
        f(Red) + f(Green)";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_group_with_written_payloads_keeps_them() {
    let (message, _) = first_error("tag Shot = Miss | Hit(Int) Hit(\"far\")");
    assert!(message.contains("type mismatch"), "{message}");
    assert!(type_of("tag Shot = Miss | Hit(Int) Hit(3)").contains("Hit: Number"));
}

#[test]
fn a_lone_tag_is_a_group_of_one() {
    assert_eq!(type_of("tag Done Done"), "[Done]");
    assert_eq!(type_of("tag Boxed Boxed(1)"), "[Boxed: Number]");
    assert_eq!(type_of("tag Boxed Boxed(\"a\")"), "[Boxed: String]");
}

#[test]
fn two_lone_tags_never_mix() {
    let (message, text) = first_error("tag Ping tag Pong if 1 < 2 then Ping else Pong done");
    assert!(message.contains("not allowed here"), "{message}");
    assert_eq!(text, "Pong");
    assert_eq!(
        type_of("tag Ping | Pong if 1 < 2 then Ping else Pong done"),
        "[Ping, Pong]"
    );
}

#[test]
fn a_lone_tag_and_a_list_never_mix() {
    let (message, _) = first_error("tag Stop if 1 < 2 then [1, 2] else Stop done");
    assert!(message.contains("not allowed here"), "{message}");
}

#[test]
fn a_lone_tag_match_needs_no_else() {
    let source = "tag Done f = program(d) do match d do Done then 1 done done f(Done)";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_tag_the_host_provides_cannot_be_declared_again() {
    for (source, tag) in [
        ("tag Circle 1", "Circle"),
        ("tag Mine | Tick 1", "Tick"),
        ("tag Light = Up | Stop 1", "Up"),
    ] {
        let (message, text) = first_error(source);
        assert_eq!(
            message,
            format!(
                "`{tag}` is a tag the host already provides; use it as it is, or pick another name for yours"
            )
        );
        assert_eq!(text, tag);
    }
}

#[test]
fn two_groups_never_share_a_tag_name() {
    for source in [
        "tag A = Red | Green tag B = Red | Blue 1",
        "tag Red tag Red 1",
        "tag Red tag B = Red | Blue 1",
        "tag Empty 1",
    ] {
        let (message, _) = first_error(source);
        assert!(message.starts_with("duplicate tag"), "{source}: {message}");
    }
}

#[test]
fn the_host_families_stay_open() {
    let source = "s = Tick(5) \
        narrow = program(v) do match v do Tick(r) then r done done \
        wide = program(v) do match v do Tick(r) then r PointerUp(p) then p.x done done \
        narrow(s) + wide(s)";
    assert!(check_with_prelude(PRELUDE, source).is_ok());
}

#[test]
fn a_program_with_no_prelude_has_no_list_syntax_and_says_so() {
    for source in [
        "[1, 2]",
        "[]",
        "match 1 do [] then 0 else 1 done",
        "[a] = [1] a",
    ] {
        let errors = check_with_prelude("", source).err().expect("an error");
        assert!(
            errors[0].message.contains("tag List = Empty | Link"),
            "{source}: {errors:?}"
        );
    }
    assert!(check_with_prelude("", "tag List = Empty | Link [1, 2]").is_ok());
    assert!(check_with_prelude("", "1 + 2").is_ok());
}

#[test]
fn a_function_may_be_a_payload_and_still_runs_through_the_checker() {
    let source = "tag Box = B match B(program(x) do x + 1 done) do B(g) then g(41) done";
    assert_eq!(type_of(source), "Number");
    let (message, _) =
        first_error("tag Box = B B(program(x) do x done) == B(program(x) do x done)");
    assert!(message.contains("function"), "{message}");
}

#[test]
fn a_tag_used_with_a_different_arity_at_two_uses_is_two_types() {
    assert!(check("tag P = Pr f = Pr(1) g = Pr(1, 2) 1").is_ok());
    let (message, _) = first_error("tag P = Pr if 1 < 2 then Pr(1) else Pr(1, 2) done");
    assert!(message.contains("type mismatch"), "{message}");
}

#[test]
fn a_group_holding_itself_under_a_record_checks() {
    let source = "tag Tree = Leaf | Node \
        grow = program(n, t) do if n < 1 then t else grow(n - 1, Node({kids: t})) done done \
        x = grow(3, Leaf) 1";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_user_group_named_like_the_list_has_the_lists_element_rule() {
    let (message, text) = first_error("tag List = Empty | Link xs = [1, \"a\"] 1");
    assert!(message.contains("duplicate tag"), "{message}: {text}");
    let source = "xs = [1, \"a\"] 1";
    let errors = check_with_prelude(PRELUDE, source).err().expect("an error");
    assert!(
        errors[0]
            .message
            .starts_with("a list holds one kind of thing"),
        "{errors:?}"
    );
}

#[test]
fn a_tag_whose_payload_nothing_constrains_prints_as_the_bare_tag() {
    assert_eq!(
        type_of("tag Light = Red | Green | Amber Green"),
        "[Red, Green, Amber]"
    );
    assert_eq!(
        type_of("tag Maybe = Nothing | Just Nothing"),
        "[Nothing, Just]"
    );
    assert_eq!(
        type_of("tag Maybe = Nothing | Just Just(1)"),
        "[Nothing, Just: Number]"
    );
    let pile = type_of("tag Pile = Nil | Cons Nil");
    assert_eq!(pile, "[Nil, Cons]");
    let function = type_of(
        "tag Maybe = Nothing | Just or_else = program(m, d) do match m do Nothing then d Just(v) then v done done or_else",
    );
    assert!(
        function.contains("Just: "),
        "a shared payload still prints: {function}"
    );
}

#[test]
fn an_error_naming_an_unused_payload_leaves_it_out() {
    let (message, _) = first_error(
        "tag Light = Red | Green | Amber f = program(l) do match l do Red then 1 Green then 2 done done f(Amber)",
    );
    assert!(!message.contains(": t"), "{message}");
    assert!(message.contains("Amber"), "{message}");
}
