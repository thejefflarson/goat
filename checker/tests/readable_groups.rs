//! A recursive group prints by its name and the types in its `_` slots, in an
//! error and wherever the editor shows a type: never as `μ` or a raw type
//! variable.

use goat_checker::check;

const PILE: &str = "tag Pile = Nil | Cons(_, Pile)\n";
const MATCH_PILE: &str = "f = program(p) do match p do Nil then 0 Cons(a, b) then a done done\n";

fn error_of(source: &str) -> String {
    check(source).err().expect("an error")[0].message.clone()
}

fn type_of(source: &str) -> String {
    let checked = check(source).expect("checks");
    checked.typed.show(&checked.typed.root_ty)
}

#[test]
fn a_list_in_an_error_is_list_of_its_item() {
    assert_eq!(
        error_of("1 + [1, 2]"),
        "type mismatch: expected `Number`, found `List(Number)`"
    );
    assert_eq!(
        error_of("1 + [\"a\"]"),
        "type mismatch: expected `Number`, found `List(String)`"
    );
}

#[test]
fn an_unsettled_slot_is_a_letter() {
    assert!(error_of("Empty + 1").contains("`List(a)`"));
}

#[test]
fn a_user_group_prints_by_its_name_and_slots() {
    assert!(error_of(&format!("{PILE}Cons(1, Nil) + 1")).contains("`Pile(Number)`"));
    assert!(error_of(&format!("{PILE}Cons(\"a\", Nil) + 1")).contains("`Pile(String)`"));
}

#[test]
fn an_expected_group_is_named_where_a_match_wrote_its_tags() {
    assert_eq!(
        error_of(&format!("{PILE}{MATCH_PILE}f(1)")),
        "type mismatch: expected `Pile(Number)`, found `Number`"
    );
}

#[test]
fn a_group_without_slots_prints_bare() {
    let tree = "tag Tree = Leaf | Node({left: Tree, right: Tree})\n";
    assert_eq!(
        error_of(&format!("{tree}Node({{left: 1, right: Leaf}})")),
        "type mismatch: expected `Tree`, found `Number`"
    );
    assert!(error_of("tag Shape = Dot | Sq(Number)\nDot + 1").contains("`Shape`"));
}

#[test]
fn a_type_shown_to_the_editor_follows_the_same_form() {
    let source = "f = program(l) do match l do Empty then 0 Link(a, b) then a + 1 done done\nf";
    assert_eq!(type_of(source), "(List(Number)) -> Number");
    assert_eq!(type_of("[1, 2]"), "List(Number)");
    assert_eq!(type_of(&format!("{PILE}Cons(\"a\", Nil)")), "Pile(String)");
}
