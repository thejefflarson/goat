//! A `_` in a tag payload leaves its type to each use, so a list or a maybe
//! written in pure goat runs for any element type, through the interpreter and
//! wasm.

#[allow(dead_code)]
mod support;

use support::run;

const PILE: &str = "tag Pile = Nil | Cons(_, Pile) \
    size = program(xs) do match xs do Nil then 0 Cons(head, rest) then 1 + size(rest) done done ";

#[test]
fn one_size_counts_a_pile_of_numbers_and_a_pile_of_words() {
    let src = format!(
        "{PILE} print(size(Cons(1, Cons(2, Nil)))); print(size(Cons(\"a\", Nil))); \
         print(size(Cons([1], Cons([], Nil))));"
    );
    assert_eq!(run(&src), "2\n1\n2");
}

#[test]
fn a_maybe_unwraps_for_any_type() {
    let src = "tag Maybe = Nothing | Just(_) \
        or_else = program(m, fallback) do match m do Nothing then fallback Just(v) then v done done \
        print(or_else(Just(3), 0)); print(or_else(Nothing, 7)); print(or_else(Just(\"hi\"), \"\"));";
    assert_eq!(run(src), "3\n7\nhi");
}

#[test]
fn a_user_tree_sums_what_it_holds() {
    let src = "tag Tree = Leaf | Node(Tree, _, Tree) \
        total = program(t) do match t do Leaf then 0 Node(l, v, r) then total(l) + v + total(r) done done \
        print(total(Node(Node(Leaf, 1, Leaf), 2, Node(Leaf, 3, Leaf))));";
    assert_eq!(run(src), "6");
}

#[test]
fn a_lone_tag_with_a_payload_per_use_runs() {
    let src = "tag Boxed(_) \
        print(Boxed(1)); print(Boxed(\"a\"));";
    assert_eq!(run(src), "Boxed(1)\nBoxed(\"a\")");
}

#[test]
fn a_group_holding_itself_under_a_record_runs() {
    let src = "tag Tree = Leaf | Node({kids: Tree}) \
        depth = program(t) do match t do Leaf then 0 Node(n) then 1 + depth(n.kids) done done \
        grow = program(n, t) do if n < 1 then t else grow(n - 1, Node({kids: t})) done done \
        print(depth(grow(5, Leaf)));";
    assert_eq!(run(src), "5");
}

#[test]
fn a_two_slot_group_runs_with_different_types_in_its_slots() {
    let src = "tag Pairs = End | More(_, _, Pairs) \
        count = program(p) do match p do End then 0 More(a, b, rest) then 1 + count(rest) done done \
        print(count(More(1, \"a\", More(2, \"b\", End))));";
    assert_eq!(run(src), "2");
}

#[test]
fn the_my_list_example_runs() {
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../examples/my_list.goat"
    ))
    .unwrap();
    assert_eq!(run(&src), "3\n2\n60");
}
