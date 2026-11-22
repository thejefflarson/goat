//! A `_` in a tag payload leaves that slot's type to each use: a fresh type at
//! every construction, the same throughout one value, because the group's own
//! name inside its payload carries the same slots. A tag written without
//! parentheses has no payload. Every tag is in a closed group; a lone tag is a
//! group of one.

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

const PILE: &str = "tag Pile = Nil | Cons(_, Pile) \
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
    let mixed = format!("{PILE} size(Cons(Cons(1, Nil), Cons(Cons(\"a\", Nil), Nil)))");
    assert!(errors_of(&mixed)[0].message.contains("type mismatch"));
}

#[test]
fn mixing_item_types_is_caught_where_the_pile_is_built() {
    let source = "tag Pile = Nil | Cons(_, Pile) xs = Cons(1, Cons(\"a\", Nil)) 1";
    let errors = errors_of(source);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].message,
        "a `Pile` holds one kind of thing; this is a String but the earlier items are Numbers"
    );
    assert_eq!(
        &source[errors[0].span.start..errors[0].span.end],
        "Cons(\"a\", Nil)"
    );
}

#[test]
fn the_third_item_is_the_one_blamed() {
    let source = "tag Pile = Nil | Cons(_, Pile) xs = Cons(1, Cons(2, Cons(true, Nil))) 1";
    let errors = errors_of(source);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].message.contains("this is a Bool"), "{errors:?}");
}

#[test]
fn a_function_over_a_user_list_keeps_the_element_type() {
    let source = "tag Pile = Nil | Cons(_, Pile) \
        first_or = program(xs, fallback) do match xs do Nil then fallback Cons(head, rest) then head done done \
        first_or(Cons(1, Nil), 0) + first_or(Nil, 5)";
    assert_eq!(type_of(source), "Number");
    let mixed = "tag Pile = Nil | Cons(_, Pile) \
        first_or = program(xs, fallback) do match xs do Nil then fallback Cons(head, rest) then head done done \
        first_or(Cons(1, Nil), \"none\")";
    assert!(errors_of(mixed)[0].message.contains("type mismatch"));
}

#[test]
fn a_maybe_holds_one_value_of_any_type() {
    let or_else = "tag Maybe = Nothing | Just(_) \
        or_else = program(m, fallback) do match m do Nothing then fallback Just(v) then v done done ";
    assert_eq!(
        type_of(&format!(
            "{or_else} or_else(Just(3), 0) + or_else(Nothing, 1)"
        )),
        "Number"
    );
    assert_eq!(
        type_of(&format!("{or_else} or_else(Just(\"hi\"), \"\")")),
        "String"
    );
    let wrong = format!("{or_else} or_else(Just(3), \"\")");
    assert!(errors_of(&wrong)[0].message.contains("type mismatch"));
}

#[test]
fn a_tree_has_one_slot_type_throughout() {
    let tree = "tag Tree = Leaf | Node(Tree, _, Tree) \
        count = program(t) do match t do Leaf then 0 Node(l, v, r) then count(l) + 1 + count(r) done done ";
    let good = format!(
        "{tree} count(Node(Leaf, 1, Node(Leaf, 2, Leaf))) + count(Node(Leaf, \"a\", Leaf))"
    );
    assert_eq!(type_of(&good), "Number");
    let source = format!("{tree} t = Node(Leaf, 1, Node(Leaf, \"a\", Leaf)) 1");
    let (message, text) = first_error(&source);
    assert_eq!(
        message,
        "a `Tree` holds one kind of thing; this is a String but the earlier items are Numbers"
    );
    assert_eq!(text, "Node(Leaf, \"a\", Leaf)");
}

#[test]
fn two_slots_may_differ_from_each_other_but_not_along_the_value() {
    let pairs = "tag Pairs = End | More(_, _, Pairs) ";
    assert!(
        check(&format!(
            "{pairs} x = More(1, \"a\", More(2, \"b\", End)) 1"
        ))
        .is_ok()
    );
    let (message, _) = first_error(&format!(
        "{pairs} x = More(1, \"a\", More(\"x\", \"b\", End)) 1"
    ));
    assert!(message.contains("holds one kind of thing"), "{message}");
    let (message, _) = first_error(&format!("{pairs} x = More(1, \"a\", More(2, 3, End)) 1"));
    assert!(
        message.contains("this is a Number but the earlier items are Strings"),
        "{message}"
    );
}

#[test]
fn a_slot_may_sit_beside_a_written_type() {
    let shots = "tag Shots = Miss | Hit(Int, _) ";
    assert!(check(&format!("{shots} Hit(3, \"far\")")).is_ok());
    assert!(check(&format!("{shots} Hit(3, 4)")).is_ok());
    let (message, _) = first_error(&format!("{shots} Hit(\"3\", 4)"));
    assert!(message.contains("type mismatch"), "{message}");
}

#[test]
fn a_slot_may_sit_inside_a_record_or_a_list_type() {
    let points = "tag Path = Stop | Go({x: _, y: _}, Path) ";
    assert!(
        check(&format!(
            "{points} x = Go({{x: 1, y: 2}}, Go({{x: 3, y: 4}}, Stop)) 1"
        ))
        .is_ok()
    );
    assert!(
        check(&format!(
            "{points} x = Go({{x: 1, y: 2}}, Go({{x: \"a\", y: 4}}, Stop)) 1"
        ))
        .is_err()
    );
    let bag = "tag Bag(_, [_]) ";
    assert!(check(&format!("{bag} Bag(1, [2, 3])")).is_ok());
    assert!(check(&format!("{bag} Bag(1, [\"a\"])")).is_ok());
    assert!(check("tag Bag([_]) Bag([1, 2])").is_ok());
    assert!(check("tag Bag([Int]) Bag([\"a\"])").is_err());
}

#[test]
fn a_match_over_a_user_group_handles_every_tag() {
    let (message, _) = first_error(
        "tag Pile = Nil | Cons(_, Pile) \
         size = program(xs) do match xs do Cons(head, rest) then 1 + size(rest) done done \
         size(Cons(1, Nil))",
    );
    assert!(message.contains("`Nil`"), "{message}");
    let covered = "tag Pile = Nil | Cons(_, Pile) \
         size = program(xs) do match xs do Cons(head, rest) then 1 + size(rest) else 0 done done \
         size(Cons(1, Nil))";
    assert!(check(covered).is_ok());
}

#[test]
fn a_tag_without_parentheses_has_no_payload() {
    assert_eq!(
        type_of("tag Light = Red | Green | Amber Green"),
        "[Red, Green, Amber]"
    );
    let (message, _) = first_error("tag Light = Red | Green Red(1)");
    assert!(message.contains("type mismatch"), "{message}");
    let (message, _) = first_error(
        "tag Light = Red | Green f = program(l) do match l do Red(n) then n else 0 done done f(Red)",
    );
    assert!(message.contains("type mismatch"), "{message}");
    let source = "tag Light = Red | Green \
        f = program(l) do match l do Red then 1 Green then 2 done done \
        f(Red) + f(Green)";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn a_group_with_written_payloads_keeps_them() {
    let (message, _) = first_error("tag Shot = Miss | Hit(Int) Hit(\"far\")");
    assert!(message.contains("type mismatch"), "{message}");
    assert_eq!(
        type_of("tag Shot = Miss | Hit(Int) Hit(3)"),
        "[Miss, Hit: Number]"
    );
}

#[test]
fn a_lone_tag_is_a_group_of_one() {
    assert_eq!(type_of("tag Done Done"), "[Done]");
    assert_eq!(type_of("tag Boxed(_) Boxed(1)"), "[Boxed: Number]");
    assert_eq!(type_of("tag Boxed(_) Boxed(\"a\")"), "[Boxed: String]");
    let (message, _) = first_error("tag Done Done(1)");
    assert!(message.contains("type mismatch"), "{message}");
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
            errors[0]
                .message
                .contains("tag List = Empty | Link(_, List)"),
            "{source}: {errors:?}"
        );
    }
    assert!(check_with_prelude("", "tag List = Empty | Link(_, List) [1, 2]").is_ok());
    assert!(check_with_prelude("", "1 + 2").is_ok());
}

#[test]
fn a_function_may_be_a_payload() {
    let source = "tag Box(_) match Box(program(x) do x + 1 done) do Box(g) then g(41) done";
    assert_eq!(type_of(source), "Number");
    let (message, _) =
        first_error("tag Box(_) Box(program(x) do x done) == Box(program(x) do x done)");
    assert!(message.contains("function"), "{message}");
}

#[test]
fn a_tag_used_with_a_different_arity_at_two_uses_is_an_error() {
    let (message, _) = first_error("tag P(_) if 1 < 2 then P(1) else P(1, 2) done");
    assert!(message.contains("type mismatch"), "{message}");
    assert!(check("tag P(_) f = P(1) g = P(1, 2) 1").is_ok());
}

#[test]
fn a_group_holding_itself_under_a_record_checks() {
    let source = "tag Tree = Leaf | Node({kids: Tree}) \
        grow = program(n, t) do if n < 1 then t else grow(n - 1, Node({kids: t})) done done \
        x = grow(3, Leaf) 1";
    assert_eq!(type_of(source), "Number");
}

#[test]
fn recursion_at_two_element_types_checks() {
    let source =
        format!("{PILE} size(Cons(1, Nil)) + size(Cons(\"a\", Nil)) + size(Cons([1], Nil))");
    assert_eq!(type_of(&source), "Number");
}

#[test]
fn the_built_in_list_keeps_its_own_wording() {
    let errors = check_with_prelude(PRELUDE, "xs = [1, \"a\"] 1")
        .err()
        .expect("an error");
    assert_eq!(
        errors[0].message,
        "a list holds one kind of thing; this is a String but the earlier items are Numbers"
    );
}

#[test]
fn a_tag_whose_payload_nothing_constrains_prints_as_the_bare_tag() {
    assert_eq!(
        type_of("tag Maybe = Nothing | Just(_) Nothing"),
        "[Nothing, Just]"
    );
    assert_eq!(
        type_of("tag Maybe = Nothing | Just(_) Just(1)"),
        "[Nothing, Just: Number]"
    );
    assert!(type_of("tag Pile = Nil | Cons(_, Pile) Nil").ends_with("[Nil, Cons: {0: t1, 1: t0}]"));
    let function = type_of(
        "tag Maybe = Nothing | Just(_) or_else = program(m, d) do match m do Nothing then d Just(v) then v done done or_else",
    );
    assert!(
        function.contains("Just: "),
        "a shared payload still prints: {function}"
    );
}

#[test]
fn an_error_naming_an_unused_slot_leaves_it_out() {
    let (message, _) = first_error(
        "tag Light = Red | Green(_) | Amber f = program(l) do match l do Red then 1 Green(n) then 2 done done f(Amber)",
    );
    assert!(!message.contains(": t"), "{message}");
    assert!(message.contains("Amber"), "{message}");
}

#[test]
fn a_tag_declared_with_a_payload_is_not_written_bare() {
    for (source, message) in [
        (
            "tag Maybe = Nothing | Just(_) x = Just 1",
            "`Just` takes a value: write `Just(…)`",
        ),
        (
            "tag P = End | More(_, _, P) x = More 1",
            "`More` takes 3 values: write `More(…, …, …)`",
        ),
        (
            "tag Hit(_) x = Hit 1",
            "`Hit` takes a value: write `Hit(…)`",
        ),
        (
            "tag Maybe = Nothing | Just(_) match Nothing do Nothing then 0 Just then 1 done",
            "`Just` takes a value: write `Just(…)`",
        ),
    ] {
        let (found, text) = first_error(source);
        assert_eq!(found, message, "{source}");
        assert!(["Just", "More", "Hit"].contains(&text.as_str()), "{text}");
    }
}

#[test]
fn an_int_and_a_float_in_one_slot_widen_like_list_items() {
    let pile = "tag Pile = Nil | Cons(_, Pile) ";
    assert!(check(&format!("{pile} x = Cons(7 // 2, Cons(2.5, Nil)) 1")).is_ok());
    assert!(check(&format!("{pile} x = Cons(2.5, Cons(7 // 2, Nil)) 1")).is_ok());
    assert!(check_with_prelude(PRELUDE, "xs = [7 // 2, 2.5] 1").is_ok());
    let (message, _) = first_error(&format!("{pile} x = Cons(7 // 2, Cons(\"a\", Nil)) 1"));
    assert!(message.contains("holds one kind of thing"), "{message}");
}

#[test]
fn only_the_slot_that_mixes_widens_and_a_written_slot_never_does() {
    let pairs = "tag P = End | More(_, _, P) ";
    assert!(
        check(&format!(
            "{pairs} x = More(7 // 2, 1, More(2.5, 5 // 2, End)) 1"
        ))
        .is_ok()
    );
    assert!(check(&format!("{pairs} x = More(1, 7 // 2, More(2, 2.5, End)) 1")).is_ok());
    let shots = "tag Shots = Miss | Hit(Int, _) ";
    assert!(check(&format!("{shots} x = Hit(7 // 2, 2.5) 1")).is_ok());
    assert!(check(&format!("{shots} x = Hit(2.5, 1) 1")).is_err());
}

#[test]
fn an_empty_or_misshapen_positional_payload_is_a_spanned_error() {
    for (source, text) in [
        ("x = Link({}) 1", "Link({})"),
        ("tag Pair = P(_, Int) x = P({}) 1", "P({})"),
        ("tag Pile = Nil | Cons(_, Pile) x = Cons({}) 1", "Cons({})"),
        ("x = Link({}, {}) 1", "{}"),
        ("x = DictNode({}) 1", "DictNode({})"),
    ] {
        let errors = errors_of(source);
        let error = &errors[0];
        assert!(!error.message.is_empty(), "{source}");
        assert_eq!(&source[error.span.start..error.span.end], text, "{source}");
    }
}

#[test]
fn more_slots_than_a_group_allows_is_a_spanned_error() {
    let slots = |n: usize| format!("tag T = A({}) 1", vec!["_"; n].join(", "));
    assert!(check(&slots(256)).is_ok());
    let (message, text) = first_error(&slots(4200));
    assert!(message.contains("at most 256"), "{message}");
    assert_eq!(text, "_");
    let lists = format!("tag T = A({}, [_]) 1", vec!["_"; 4096].join(", "));
    assert!(check(&lists).is_err());
}
