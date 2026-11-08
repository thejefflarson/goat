use chumsky_slice::{Expr, Item, parse_items};

fn names(items: &[Item]) -> Vec<&str> {
    items
        .iter()
        .filter_map(|i| match i {
            Item::Let(n, _) => Some(n.as_str()),
            _ => None,
        })
        .collect()
}

fn show(src: &str) {
    let (items, errs) = parse_items(src);
    eprintln!("--- {src:?}\n  items: {items:?}\n  errors: {errs:?}");
}

#[test]
fn valid_program() {
    let src = "area = shape.size * 2 + 1;\ntotal = match shape do\n  Circle(r) then r * r\n  Square(s) then s * s\n  else -1\ndone;\nf(area, total)";
    let (items, errs) = parse_items(src);
    assert!(errs.is_empty(), "{errs:?}");
    assert_eq!(names(&items), ["area", "total"]);
    let Item::Let(
        _,
        Expr::Match {
            arms, otherwise, ..
        },
    ) = &items[1]
    else {
        panic!("{items:?}")
    };
    assert_eq!(arms.len(), 2);
    assert!(otherwise.is_some());
}

#[test]
fn missing_value_keeps_the_binding_and_the_rest() {
    let src = "a = ;\nb = 2;\nb";
    show(src);
    let (items, errs) = parse_items(src);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert_eq!(names(&items), ["a", "b"]);
    assert_eq!(items.len(), 3);
}

#[test]
fn dangling_equals_at_eof() {
    let (items, errs) = parse_items("a = ");
    show("a = ");
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert_eq!(names(&items), ["a"]);
}

#[test]
fn trailing_operator() {
    let src = "x = 1 + ; y = 2 * ; z = 3";
    show(src);
    let (items, errs) = parse_items(src);
    assert!(!errs.is_empty());
    assert_eq!(names(&items), ["x", "y", "z"]);
}

#[test]
fn match_with_no_arms_and_no_done() {
    let src = "match x do";
    show(src);
    let (items, errs) = parse_items(src);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(
        matches!(items.as_slice(), [Item::Expr(Expr::Match { .. })]),
        "the match survives: {items:?}"
    );
}

#[test]
fn arm_without_a_body() {
    let src = "match s do\n  Circle(r) then\ndone";
    show(src);
    let (items, errs) = parse_items(src);
    assert!(!errs.is_empty());
    eprintln!("arm-without-body items: {items:?}");
}

#[test]
fn arm_missing_then() {
    let src = "match s do\n  Circle(r) r * r\n  Square(s) then s\ndone";
    show(src);
    let (items, errs) = parse_items(src);
    assert!(!errs.is_empty());
    let arms = items.iter().find_map(|i| match i {
        Item::Expr(Expr::Match { arms, .. }) => Some(arms.len()),
        _ => None,
    });
    eprintln!("arm-missing-then: arms recovered = {arms:?}");
}

#[test]
fn unterminated_match_does_not_swallow_following_bindings() {
    let src = "m = match x do\n  A then 1\ny = 2;\ny";
    show(src);
    let (items, errs) = parse_items(src);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert_eq!(names(&items), ["m", "y"]);
}

#[test]
fn an_unrecovered_error_loses_the_whole_tree() {
    // The unclosed `(` has no matching recovery point: chumsky reports the
    // errors it saw but returns no output at all, so the four bindings that
    // rowan-slice keeps are gone. Recovery is opt-in per combinator.
    let src = "a = ;\nb = (1 + ;\nc = match z do\n  X then done;\nd = 4";
    show(src);
    let (items, errs) = parse_items(src);
    assert!(errs.len() >= 2);
    assert!(items.is_empty(), "{items:?}");
}

#[test]
fn unclosed_parens_are_slow_but_finish() {
    // Recovery re-scans for the matching `)` at every nesting level, so cost
    // grows roughly cubically (examples/nesting.rs: 2000 deep takes ~50s).
    // 100 deep stays in the milliseconds.
    let src = "(".repeat(100);
    let (_, errs) = parse_items(&src);
    assert!(!errs.is_empty());
}
