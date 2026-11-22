//! A list pattern fixes a length, so it takes apart only a list literal of
//! that length; anything else is told to use `match`.

use goat_checker::check_with_prelude;

fn blame(source: &str) -> (String, String) {
    let errors = check_with_prelude(goat_checker::PRELUDE, source)
        .err()
        .unwrap_or_else(|| panic!("should not check: {source}"));
    let error = &errors[0];
    (
        source[error.span.start..error.span.end].to_string(),
        error.message.clone(),
    )
}

fn match_advice(name: &str) -> String {
    format!(
        "a list can be any length, so take it apart with `match`: `match {name} do [] then … [x, ...rest] then … done`"
    )
}

#[test]
fn a_list_parameter_pattern_is_told_to_use_match() {
    assert_eq!(
        blame("f = program([a, b]) do a done f([1, 2])"),
        ("[a, b]".to_string(), match_advice("xs"))
    );
    assert_eq!(
        blame("f = program([x, ...rest]) do x done f([1])").1,
        match_advice("xs")
    );
}

#[test]
fn a_destructure_of_a_named_list_names_it_in_the_advice() {
    assert_eq!(
        blame("ys = [1, 2] [a, b] = ys a"),
        ("[a, b]".to_string(), match_advice("ys"))
    );
    assert_eq!(
        blame("f = program(xs) do [a, ...r] = xs a done f([1])").1,
        match_advice("xs")
    );
}

#[test]
fn a_destructure_of_a_computed_list_uses_xs_in_the_advice() {
    assert_eq!(blame("[a, b] = reverse([1, 2]) a").1, match_advice("xs"));
}

#[test]
fn a_literal_of_the_wrong_length_says_how_long_it_is() {
    assert_eq!(
        blame("[a, b] = [1, 2, 3] a"),
        (
            "[a, b]".to_string(),
            "this list has 3 items but the pattern takes 2".to_string()
        )
    );
    assert_eq!(
        blame("[a, b, ...r] = [1] a").1,
        "this list has 1 item but the pattern takes at least 2"
    );
}

#[test]
fn a_literal_of_the_right_length_still_destructures() {
    for source in [
        "[a, b] = [1, 2] a",
        "[a, ...r] = [1, 2, 3] r",
        "[a, ...r] = [1] r",
    ] {
        check_with_prelude(goat_checker::PRELUDE, source)
            .unwrap_or_else(|e| panic!("{source}: {e:?}"));
    }
}
