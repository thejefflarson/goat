//! `dict()` is an AVL tree written in the prelude. These run it through the
//! interpreter and wasm, which must agree and leave nothing allocated.

#[allow(dead_code)]
mod support;

use support::run;

#[test]
fn set_get_has_and_size() {
    let src = r#"
scores = dict().set("ana", 3).set("bo", 5)
found = match scores.get("ana") do
  Found(n) then n
  Missing then 0 - 1
done
absent = match scores.get("cy") do
  Found(n) then n
  Missing then 0 - 1
done
print(found);
print(absent);
print(scores.has("bo"));
print(scores.has("cy"));
print(scores.size());
print(dict().size())
"#;
    assert_eq!(run(src), "3\n-1\ntrue\nfalse\n2\n0");
}

#[test]
fn setting_a_key_again_replaces_its_value() {
    let src = r#"
d = dict().set("a", 1).set("a", 2)
print(d.size());
print(d.values())
"#;
    assert_eq!(run(src), "1\n[2]");
}

#[test]
fn keys_and_values_come_in_key_order() {
    let src = r#"
d = dict().set(5, "e").set(1, "a").set(3, "c").set(4, "d").set(2, "b")
print(d.keys());
print(d.values())
"#;
    assert_eq!(
        run(src),
        "[1, 2, 3, 4, 5]\n[\"a\", \"b\", \"c\", \"d\", \"e\"]"
    );
}

#[test]
fn each_visits_entries_in_key_order() {
    let src = r#"
d = dict().set("b", 2).set("c", 3).set("a", 1)
d.each(program(k, v) do print(k) done);
d.each(program(k, v) do print(v) done)
"#;
    assert_eq!(run(src), "a\nb\nc\n1\n2\n3");
}

#[test]
fn updates_leave_the_old_dictionary_whole() {
    let src = r#"
old = dict().set(1, "one").set(2, "two")
more = old.set(3, "three")
fewer = old.remove(1)
print(old.keys());
print(more.keys());
print(fewer.keys())
"#;
    assert_eq!(run(src), "[1, 2]\n[1, 2, 3]\n[2]");
}

#[test]
fn removing_a_missing_key_changes_nothing() {
    let src = r#"
d = dict().set(1, 1).set(2, 2)
print(d.remove(9).keys());
print(dict().set(1, 1).remove(1).size())
"#;
    assert_eq!(run(src), "[1, 2]\n0");
}

// A function that takes a dictionary and calls both `set` and `remove` on it
// makes the checker's types too large, so these thread the dictionary through
// one binding per step in the source text instead.
fn steps(calls: impl Iterator<Item = String>) -> String {
    let mut src = String::from("d0 = dict()\n");
    for (n, call) in calls.enumerate() {
        src.push_str(&format!("d{} = d{n}{call}\n", n + 1));
    }
    src
}

#[test]
fn removing_every_key_one_at_a_time_leaves_it_empty() {
    let sets = (1..=60).map(|i| format!(".set({}, {i})", (i * 7) % 61));
    let removes = (0..=60).map(|i| format!(".remove({i})"));
    let src = format!(
        "{}print(d60.size());\nprint(d121.size());\nprint(d121.keys())",
        steps(sets.chain(removes))
    );
    assert_eq!(run(&src), "60\n0\n[]");
}

#[test]
fn removal_keeps_the_remaining_keys_in_order_and_balanced() {
    let sets = (1..=200).map(|i| format!(".set({i}, {i})"));
    let removes = (1..=100).map(|i| format!(".remove({})", i * 2));
    let src = format!(
        "{}print(d300.size());\nprint(sum(d300.keys()));\nprint(first(d300.keys()));\nprint(dict_height(d300.tree) <= 10)",
        steps(sets.chain(removes))
    );
    assert_eq!(run(&src), "100\n10000\n1\ntrue");
}

#[test]
fn dict_by_orders_keys_with_the_function_it_is_given() {
    let src = r#"
backwards = dict_by(program(a, b) do a > b done).set(2, "b").set(3, "c").set(1, "a")
print(backwards.keys());
print(backwards.values());
match backwards.get(3) do
  Found(v) then print(v)
  Missing then print("none")
done
"#;
    assert_eq!(run(src), "[3, 2, 1]\n[\"c\", \"b\", \"a\"]\nc");
}

#[test]
fn dict_by_can_compare_a_part_of_each_key() {
    let src = r#"
by_age = dict_by(program(a, b) do a.age < b.age done)
d = by_age.set({age: 9, name: "Zed"}, 1).set({age: 3, name: "Amy"}, 2)
print(change_each(d.keys(), program(p) do p.name done))
"#;
    assert_eq!(run(src), "[\"Amy\", \"Zed\"]");
}

#[test]
fn dictionaries_hold_any_key_that_orders() {
    let src = r#"
d = dict().set([2, 1], "x").set([1, 9], "y")
print(d.values());
e = dict().set(1.5, true).set(0.5, false)
print(e.keys())
"#;
    assert_eq!(run(src), "[\"y\", \"x\"]\n[0.5, 1.5]");
}

#[test]
fn a_dictionary_can_be_a_function_argument_and_a_record_field() {
    let src = r#"
add_all = program(d, n) do if n == 0 then d else add_all(d.set(n, n), n - 1) done done
holder = {names: add_all(dict(), 3)}
print(holder.names.keys())
"#;
    assert_eq!(run(src), "[1, 2, 3]");
}

// 7919 is coprime to 10007, so `i * 7919 % 10007` visits 10,000 distinct keys
// in a scattered order.
const BIG: &str = r#"
key = program(i) do (i * 7919) % 10007 done
fill = program(d, i, n) do
  if i > n then d else fill(d.set(key(i), i), i + 1, n) done
done
hits = program(d, i, n, total) do
  if i > n then total
  else hits(d, i + 1, n, total + match d.get(key(i)) do
    Found(v) then if v == i then 1 else 0 done
    Missing then 0
  done) done
done
ascending = program(xs) do
  match xs do
    [a, ...rest] then
      match rest do
        [b, ...more] then if a < b then ascending(rest) else false done
        [] then true
      done
    [] then true
  done
done
d = fill(dict(), 1, 10000)
"#;

#[test]
fn a_helper_may_call_set_and_remove_on_the_dictionary_it_takes() {
    let src = r#"
change = program(d, k, add) do if add then d.set(k, 1) else d.remove(k) done done
fill = program(d) do d.set(1, 10).set(2, 20) done
drain = program(d) do d.remove(1) done
both = program(d) do d.set(1, 10).remove(1) done
print(change(dict(), "a", true).size());
print(change(dict().set("a", 2), "a", false).size());
print(drain(fill(dict())).keys());
print(both(dict()).size())
"#;
    assert_eq!(run(src), "1\n0\n[2]\n0");
}

#[test]
fn ten_thousand_keys_insert_look_up_and_stay_balanced() {
    let src = format!(
        "{BIG}print(d.size());\nprint(hits(d, 1, 10000, 0));\nprint(dict_height(d.tree) <= 19)"
    );
    assert_eq!(run(&src), "10000\n10000\ntrue");
}

#[test]
fn ten_thousand_keys_come_out_sorted() {
    let src = format!(
        "{BIG}keys = d.keys()\nprint(first(keys));\nprint(item(keys, 10000));\nprint(ascending(keys));\nprint(length(d.values()))"
    );
    assert_eq!(run(&src), "1\n10006\ntrue\n10000");
}
