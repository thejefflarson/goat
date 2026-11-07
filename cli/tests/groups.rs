//! Grouped `tag` declarations (ADR 0016) run through the interpreter and wasm
//! like any other closed variant.

#[allow(dead_code)]
mod support;

use support::run;

#[test]
fn an_exhaustive_match_over_a_declared_group_runs() {
    let src = "tag Light = Red | Green | Amber \
               seconds = program(l) do match l do Red then 30 Green then 25 Amber then 5 done done \
               print(seconds(Red) + seconds(Green) + seconds(Amber));";
    assert_eq!(run(src), "60");
}

#[test]
fn a_group_with_payloads_runs() {
    let src = "tag Shape = Circle(Number) | Rect(Number, Number) | Dot \
               area = program(s) do match s do \
                 Circle(r) then 3 * r * r \
                 Rect(w, h) then w * h \
                 Dot then 0 \
               done done \
               print(area(Circle(2)) + area(Rect(3, 4)) + area(Dot));";
    assert_eq!(run(src), "24");
}

#[test]
fn a_recursive_group_runs() {
    let src = "tag Tree = Leaf | Node({left: Tree, right: Tree}) \
               size = program(t) do match t do \
                 Leaf then 0 \
                 Node(n) then 1 + size(n.left) + size(n.right) \
               done done \
               print(size(Node({left: Node({left: Leaf, right: Leaf}), right: Leaf})));";
    assert_eq!(run(src), "2");
}

#[test]
fn a_group_value_can_flow_through_a_record_and_a_list() {
    let src = "tag Light = Red | Green \
               name = program(l) do match l do Red then 1 Green then 2 done done \
               lights = [Red, Green, Red] \
               total = program(xs) do match xs do \
                 [] then 0 \
                 [x, ...rest] then name(x) + total(rest) \
               done done \
               print(total(lights));";
    assert_eq!(run(src), "4");
}
