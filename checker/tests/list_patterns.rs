//! A list pattern takes apart any list. Only a list literal has a length the
//! checker knows, so only it is checked for fit here; any other length is
//! checked when the program runs.

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

#[test]
fn a_pattern_takes_apart_any_list() {
    for source in [
        "f = program([a, b]) do a done f([1, 2])",
        "f = program([x, ...rest]) do x done f([1])",
        "ys = [1, 2] [a, b] = ys a",
        "f = program(xs) do [a, ...r] = xs a done f([1])",
        "[a, b] = reverse([1, 2]) a",
        "f = program([a], [b, ...c]) do a + b done f([1], [2, 3])",
    ] {
        check_with_prelude(goat_checker::PRELUDE, source)
            .unwrap_or_else(|e| panic!("{source}: {e:?}"));
    }
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
    assert_eq!(
        blame("[a] = [] a").1,
        "this list is empty but the pattern takes 1"
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
