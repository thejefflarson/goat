//! The goat type checker: parse → lower (name resolution) → Hindley-Milner
//! inference. The entry point is [`check`].

pub mod captures;
pub mod error;
pub mod hir;
pub mod infer;
pub mod kinds;
pub mod lower;
mod order;
pub mod query;
pub mod ty;
pub mod vocab;

pub use captures::Target;
pub use error::GoatError;
pub use hir::Expr;
pub use infer::Typed;
pub use ty::Ty;
pub use vocab::Vocab;

use hir::Symbol;
use std::collections::{HashMap, HashSet};

/// A successfully checked program: its name-resolved tree and inferred types.
pub struct Checked {
    pub root: Expr,
    pub typed: Typed,
    /// What each function literal captures, in `Capture` index order.
    pub captures: HashMap<Target, Vec<Symbol>>,
    /// Set when the program defines `init`, `update` and `draw`; its root then
    /// ends in the record of those three values.
    pub interactive: Option<hir::Interactive>,
    /// The host vocabulary the program was checked against.
    pub vocab: Vocab,
}

/// The standard library: the definitions every program starts with, whatever its host.
pub const STDLIB: &str = include_str!("../../prelude/prelude.goat");

/// The `foreign` declarations of the turtle host.
pub const TURTLE_VOCAB: &str = include_str!("../../prelude/turtle.goat");

/// The built-in definitions every program starts with under the turtle host.
pub const PRELUDE: &str = concat!(
    include_str!("../../prelude/prelude.goat"),
    "\n",
    include_str!("../../prelude/turtle.goat"),
    "\n",
    include_str!("../../prelude/turtle_keys.goat"),
);

/// Parse, name-resolve, and type-check `source` with the prelude in scope.
///
/// Returns every diagnostic found. Lowering (name resolution) and inference
/// errors are reported together; parse errors are returned without the rest. The
/// binding-order check runs only on a program that type-checks.
pub fn check(source: &str) -> Result<Checked, Vec<GoatError>> {
    check_with_prelude(PRELUDE, source)
}

/// Like [`check`], with `prelude` standing in for the built-in one. The program
/// is checked against the turtle's vocabulary, so a prelude that offers
/// interactive programs must define its decoders, as [`PRELUDE`] does.
pub fn check_with_prelude(prelude: &str, source: &str) -> Result<Checked, Vec<GoatError>> {
    check_with_vocab(prelude, &Vocab::turtle(), source)
}

/// Like [`check_with_prelude`], against the vocabulary of a host: the events
/// `update` may handle, the shapes `draw` may return and the keys they carry.
/// `prelude` must already hold the goat source of `vocab`'s decoders.
pub fn check_with_vocab(
    prelude: &str,
    vocab: &Vocab,
    source: &str,
) -> Result<Checked, Vec<GoatError>> {
    vocab.validate().map_err(|message| {
        vec![GoatError::new(
            hir::Span::new(0, 0),
            format!("the host's vocabulary is invalid: {message}"),
        )]
    })?;
    let lowered = lower::lower_with_vocab(prelude, vocab, source)?;
    if !lowered.errors.is_empty() {
        return Err(lowered.errors);
    }
    let mut typed = infer::infer_program(&lowered.root, lowered.interactive.as_ref(), vocab)?;
    typed.warnings.splice(0..0, lowered.warnings);
    let generalized = typed
        .schemes
        .iter()
        .filter(|(_, scheme)| !scheme.vars.is_empty())
        .map(|(symbol, _)| *symbol)
        .collect();
    let captures = captures::capture_sets(&lowered.root, &generalized);
    // Order is judged on the names the source writes: a function still uses a
    // generalized value it names, however mono later lowers that value.
    let named = captures::capture_sets(&lowered.root, &HashSet::new());
    let errors = order::check(&lowered.root, &named);
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(Checked {
        root: lowered.root,
        typed,
        captures,
        interactive: lowered.interactive,
        vocab: vocab.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// These tests count nodes, type variables and warnings, so they run
    /// without the standard prelude.
    fn check(source: &str) -> Result<Checked, Vec<GoatError>> {
        check_with_prelude("", source)
    }

    /// The inferred type of a program, as a string, or the first error message.
    fn type_of(source: &str) -> Result<String, String> {
        match check(source) {
            Ok(checked) => Ok(checked.typed.root_ty.to_string()),
            Err(errors) => Err(errors[0].message.clone()),
        }
    }

    /// Like [`type_of`], naming `Int` and `Float` where `Display` says `Number`.
    fn exact_type_of(source: &str) -> String {
        check(source)
            .expect("checks")
            .typed
            .root_ty
            .exact()
            .to_string()
    }

    fn warnings_of(source: &str) -> Vec<GoatError> {
        check(source).expect("checks").typed.warnings
    }

    /// The one error's message and the source text its span covers.
    fn spanned_error(source: &str) -> (String, String) {
        let errors = check(source).err().expect("should not check");
        assert_eq!(errors.len(), 1, "{errors:?}");
        let span = errors[0].span;
        (
            errors[0].message.clone(),
            source[span.start..span.end].to_string(),
        )
    }

    const SHAPE: &str = "tag Shape = Disc(Number) | Square(Number) | Dot ";

    #[test]
    fn a_grouped_match_covering_every_tag_needs_no_else() {
        let src = format!(
            "{SHAPE} area = program(s) do match s do \
               Disc(r) then r Square(w) then w * w Dot then 0 done done \
             area(Disc(2))"
        );
        assert_eq!(type_of(&src).unwrap(), "Number");
    }

    #[test]
    fn a_grouped_tag_builds_the_closed_group() {
        let ty = type_of(&format!("{SHAPE} Dot")).unwrap();
        assert_eq!(ty, "[Disc: Number, Square: Number, Dot]");
    }

    #[test]
    fn a_grouped_match_missing_a_tag_is_a_spanned_error() {
        let src = format!("{SHAPE} match Dot do Disc(r) then r Square(w) then w done");
        let (message, text) = spanned_error(&src);
        assert!(message.contains("doesn't handle `Dot`"), "{message}");
        assert_eq!(text, "Dot");
    }

    #[test]
    fn a_number_or_string_literal_match_with_else_checks() {
        assert_eq!(
            type_of("f = program(n) do match n do 0 then 10 1 then 20 else 30 done done f(1)")
                .unwrap(),
            "Number"
        );
        assert_eq!(
            type_of("match \"go\" do \"go\" then 1 \"stop\" then 2 else 3 done").unwrap(),
            "Number"
        );
    }

    #[test]
    fn a_bool_match_covering_both_values_needs_no_else() {
        assert_eq!(
            type_of("match 1 < 2 do true then 1 false then 2 done").unwrap(),
            "Number"
        );
    }

    #[test]
    fn a_literal_match_without_else_is_a_spanned_error() {
        for src in [
            "match 1 do 0 then 1 done",
            "match \"a\" do \"a\" then 1 done",
            "match 1 < 2 do true then 1 done",
            "match 1 < 2 do true then 1 true then 2 done",
        ] {
            let (message, text) = spanned_error(src);
            assert!(message.contains("needs an `else`"), "{message}");
            assert!(src.contains(&text), "{text}");
        }
    }

    #[test]
    fn a_match_mixing_scalar_types_is_a_spanned_error() {
        let (message, text) = spanned_error("match 1 do 0 then 1 \"a\" then 2 else 3 done");
        assert!(message.contains("different types"), "{message}");
        assert_eq!(text, "\"a\"");
        let (message, _) = spanned_error("tag A match A do A then 1 2 then 2 else 3 done");
        assert!(message.contains("can't mix"), "{message}");
    }

    #[test]
    fn a_literal_arm_of_the_wrong_type_for_the_scrutinee_is_an_error() {
        let err = type_of("match 1 do \"a\" then 1 else 2 done").unwrap_err();
        assert!(err.contains("type mismatch"), "{err}");
    }

    #[test]
    fn tag_and_list_matches_keep_their_single_type_rule() {
        let err = type_of("tag A match A do A then 1 [] then 2 else 3 done").unwrap_err();
        assert!(err.contains("can't mix"), "{err}");
        let err = type_of("match [] do [] then 1 A then 2 else 3 done").unwrap_err();
        assert!(err.contains("can't mix"), "{err}");
    }

    #[test]
    fn a_grouped_match_may_still_have_an_else() {
        let src = format!("{SHAPE} match Dot do Disc(r) then r else 0 done");
        assert_eq!(type_of(&src).unwrap(), "Number");
    }

    #[test]
    fn an_arm_for_a_tag_outside_the_group_is_an_error() {
        let src = format!("{SHAPE} tag Stray match Dot do Stray then 1 else 0 done");
        let err = type_of(&src).unwrap_err();
        assert!(err.contains("matches `Stray`"), "{err}");
    }

    #[test]
    fn a_grouped_payload_is_checked_against_the_declaration() {
        let (message, text) = spanned_error(&format!("{SHAPE} Disc(\"big\")"));
        assert!(message.contains("Number"), "{message}");
        assert_eq!(text, "Disc(\"big\")");
    }

    #[test]
    fn a_tag_in_two_groups_is_a_spanned_duplicate_error() {
        for src in [
            "tag A | B tag B | C 1",
            "tag A | A 1",
            "tag Light = Up | Stop 1",
            "tag Empty | Full 1",
            "tag Tick | Tock 1",
        ] {
            let (message, text) = spanned_error(src);
            assert!(message.starts_with("duplicate tag"), "{src}: {message}");
            assert!(
                ["B", "A", "Up", "Empty", "Tick"].contains(&text.as_str()),
                "{text}"
            );
        }
    }

    #[test]
    fn a_flat_tag_may_not_join_a_group() {
        let (message, text) = spanned_error("tag A tag B | A 1");
        assert!(message.starts_with("duplicate tag `A`"), "{message}");
        assert_eq!(text, "A");
    }

    #[test]
    fn a_recursive_group_is_a_recursive_type() {
        let src = "tag Tree = Leaf | Node({left: Tree, right: Tree}) \
                   depth = program(t) do match t do \
                     Leaf then 0 \
                     Node(n) then 1 + depth(n.left) \
                   done done \
                   depth(Node({left: Node({left: Leaf, right: Leaf}), right: Leaf}))";
        let checked = check(src).expect("checks");
        assert_eq!(checked.typed.root_ty.to_string(), "Number");
        let tree = type_of("tag Tree = Leaf | Node({left: Tree, right: Tree}) Leaf").unwrap();
        assert!(tree.starts_with("μ"), "{tree}");
    }

    #[test]
    fn a_recursive_group_rejects_a_payload_of_the_wrong_shape() {
        let src = "tag Tree = Leaf | Node({left: Tree, right: Tree}) Node({left: 1, right: Leaf})";
        assert!(type_of(src).is_err());
    }

    #[test]
    fn a_payload_naming_an_unknown_type_is_a_spanned_error() {
        let (message, text) = spanned_error("tag Box(Widget) 1");
        assert!(
            message.contains("a tag payload can't be `Widget`"),
            "{message}"
        );
        assert_eq!(text, "Widget");
        let (message, _) = spanned_error("tag Bag(Number, [Number]) | Empty2 1");
        assert!(message.contains("a list"), "{message}");
    }

    #[test]
    fn several_payload_types_make_a_record_payload() {
        let src = "tag Pair(Number, String) | Nothing match Pair(1, \"a\") do \
                     Pair(n, s) then n Nothing then 0 done";
        assert_eq!(type_of(src).unwrap(), "Number");
    }

    #[test]
    fn a_flat_tag_stays_open() {
        let src = "tag A tag B match A do A then 1 else 2 done";
        assert_eq!(type_of(src).unwrap(), "Number");
    }

    #[test]
    fn match_binders_record_their_types() {
        let checked = check(
            "length = program(xs) do match xs do Empty then 0 \
             Link(first, rest) then 1 + length(rest) done done length(Link(1, Empty))",
        )
        .expect("checks");
        let mut types: Vec<String> = checked
            .typed
            .binder_types
            .values()
            .map(|t| t.to_string())
            .collect();
        types.sort();
        assert_eq!(types.len(), 2);
        assert!(types.iter().any(|t| t.starts_with("μt")), "{types:?}");
        assert!(types.iter().any(|t| !t.starts_with("μt")), "{types:?}");
    }

    fn errors_of(source: &str) -> Vec<GoatError> {
        check(source).err().expect("an error")
    }

    #[test]
    fn a_pattern_head_must_be_a_declared_tag() {
        let src = "match Empty do Dow then 1 else 0 done";
        let errors = errors_of(src);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].message.starts_with("unknown tag `Dow`"));
        assert!(errors[0].message.contains("did you mean `Down`?"));
        assert_eq!(&src[errors[0].span.start..errors[0].span.end], "Dow");
    }

    #[test]
    fn constructing_an_undeclared_tag_is_an_unknown_name() {
        let errors = errors_of("Ball(5)");
        assert_eq!(errors[0].message, "unknown name `Ball`");
        let errors = errors_of("tag Ball ball(5)");
        assert!(errors[0].message.contains("did you mean the tag `Ball`?"));
    }

    #[test]
    fn capitalization_does_not_decide_what_a_tag_is() {
        assert_eq!(type_of("tag up up(1)").unwrap(), "[up: Number | t1]");
        assert_eq!(type_of("tag A tag B 1").unwrap(), "Number");
        assert_eq!(
            type_of("tag Foo f = program(Foo) do Foo(1) done f(program(x) do x done)").unwrap(),
            "Number"
        );
        assert_eq!(
            type_of("tag Foo Foo = program(x) do x done Foo(2)").unwrap(),
            "Number"
        );
    }

    #[test]
    fn tag_is_reserved_only_as_a_whole_word() {
        assert_eq!(type_of("tagline = 1 tagline").unwrap(), "Number");
        assert!(check("tag = 1 tag").is_err());
    }

    #[test]
    fn a_tag_declared_in_the_prelude_is_in_scope_for_the_program() {
        let checked = check_with_prelude("tag Mine", "Mine").expect("checks");
        assert_eq!(checked.typed.root_ty.to_string(), "[Mine | t0]");
        assert!(check_with_prelude("", "Mine").is_err());
    }

    #[test]
    fn constructing_a_tag_gives_an_open_row() {
        assert_eq!(
            type_of("tag Circle Circle(5)").unwrap(),
            "[Circle: Number | t1]"
        );
        assert_eq!(type_of("Empty").unwrap(), "[Empty | t0]");
        let link = type_of("Link(1, Empty)").unwrap();
        assert!(
            link.starts_with("[Link: {0: Number, 1: [Empty | t"),
            "{link}"
        );
    }

    #[test]
    fn branches_building_different_tags_merge_into_one_open_row() {
        let src = "tag Circle tag Square if true then Circle(1) else Square(2) done";
        let ty = type_of(src).unwrap();
        assert!(ty.starts_with("[Circle: Number, Square: Number | "), "{ty}");
    }

    #[test]
    fn match_types_to_its_arm_bodies() {
        assert_eq!(
            type_of("tag Circle match Circle(5) do Circle(r) then r else 0 done").unwrap(),
            "Number"
        );
        assert_eq!(
            type_of("tag Full match Empty do Empty then true Full then false done").unwrap(),
            "Bool"
        );
    }

    #[test]
    fn match_without_else_closes_the_row() {
        let src = "tag Circle tag Square area = program(s) do match s do Circle(r) then r * 2 Square(w) then w * 2 done done area";
        assert_eq!(
            type_of(src).unwrap(),
            "([Circle: Number, Square: Number]) -> Number"
        );
    }

    #[test]
    fn match_with_else_keeps_the_row_open() {
        let src =
            "tag Circle area = program(s) do match s do Circle(r) then r * 2 else 0 done done area";
        let ty = type_of(src).unwrap();
        assert!(ty.starts_with("([Circle: Number | t"), "{ty}");
    }

    #[test]
    fn open_tag_fits_a_closed_match_but_a_stranger_does_not() {
        let area = "tag Circle tag Square area = program(s) do match s do Circle(r) then r Square(w) then w done done ";
        assert_eq!(
            type_of(&format!("tag Circle {area} area(Circle(1))")).unwrap(),
            "Number"
        );
        assert_eq!(
            type_of(&format!("tag Square {area} area(Square(1))")).unwrap(),
            "Number"
        );
        let err = type_of(&format!("tag Triangle {area} area(Triangle(1))")).unwrap_err();
        assert!(err.contains("`Triangle`"), "{err}");
    }

    #[test]
    fn closed_row_flows_through_an_else_free_match() {
        let src = "tag A tag B pick = program(s) do match s do A then 1 B then 2 done done \
                   x = pick(A) y = pick(B) x + y";
        assert_eq!(type_of(src).unwrap(), "Number");
    }

    #[test]
    fn arm_bodies_must_agree() {
        let err =
            type_of("tag Circle match Circle(5) do Circle(r) then r else true done").unwrap_err();
        assert!(err.contains("type mismatch"), "{err}");
        let err = type_of(
            "tag Circle tag Square match Circle(5) do Circle(r) then r Square(w) then true done",
        )
        .unwrap_err();
        assert!(err.contains("type mismatch"), "{err}");
    }

    #[test]
    fn match_missing_a_tag_is_an_error() {
        let err =
            type_of("tag Circle tag Square match Circle(1) do Square(w) then w done").unwrap_err();
        assert!(err.contains("doesn't handle `Circle`"), "{err}");
        let src = "tag A tag B f = program(s) do \
                     first = match s do A then 1 B then 2 done \
                     match s do A then 1 done \
                   done";
        let err = type_of(src).unwrap_err();
        assert!(err.contains("doesn't handle `B`"), "{err}");
    }

    #[test]
    fn match_arm_for_an_impossible_tag_is_an_error() {
        let src = "tag A tag B tag C f = program(s) do \
                     first = match s do A then 1 B then 2 done \
                     match s do C then 3 else 4 done \
                   done";
        let err = type_of(src).unwrap_err();
        assert!(err.contains("matches `C`"), "{err}");
        assert!(err.contains("`A` or `B`"), "{err}");
    }

    #[test]
    fn duplicate_arm_is_an_error() {
        let err = type_of("tag A match A do A then 1 A then 2 else 3 done").unwrap_err();
        assert!(err.contains("repeats `A`"), "{err}");
    }

    #[test]
    fn match_on_a_non_variant_is_an_error() {
        let err = type_of("tag A match 1 do A then 0 else 1 done").unwrap_err();
        assert!(err.contains("built from tags"), "{err}");
    }

    #[test]
    fn payload_mismatch_between_construction_and_pattern_is_an_error() {
        let err = type_of("tag Circle match Circle(5) do Circle then 0 else 1 done").unwrap_err();
        assert!(err.contains("type mismatch"), "{err}");
        let err = type_of("tag Circle match Circle(5) do Circle(a) then a + true else 1 done")
            .unwrap_err();
        assert!(err.contains("type mismatch"), "{err}");
    }

    #[test]
    fn multi_argument_payload_binds_positional_fields() {
        let src = "tag Pair match Pair(1, true) do Pair(a, b) then if b then a else 0 done done";
        assert_eq!(type_of(src).unwrap(), "Number");
    }

    #[test]
    fn variant_errors_are_spanned() {
        let src = "tag Circle tag Square match Circle(1) do Square(w) then w done";
        let Err(errors) = check(src) else {
            panic!("expected an error");
        };
        assert_eq!(&src[errors[0].span.start..errors[0].span.end], "Circle(1)");
    }

    #[test]
    fn constructed_but_never_matched_tag_warns() {
        let src = "tag Cirle tag Circle match Cirle(5) do Circle(r) then r else 0 done";
        let warnings = warnings_of(src);
        assert_eq!(warnings.len(), 1);
        assert_eq!(
            warnings[0].message,
            "tag `Cirle` is constructed but never matched anywhere"
        );
        assert_eq!(
            &src[warnings[0].span.start..warnings[0].span.end],
            "Cirle(5)"
        );
    }

    #[test]
    fn matched_tags_do_not_warn_and_each_tag_warns_once() {
        assert!(
            warnings_of("tag Circle match Circle(5) do Circle(r) then r else 0 done").is_empty()
        );
        assert!(warnings_of("1 + 2").is_empty());
        let warnings = warnings_of("tag Oops x = Oops(1) y = Oops(2) 0");
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].span.start, 13);
    }

    const LENGTH: &str = "length = program(xs) do match xs do Empty then 0 \
         Link(first, rest) then 1 + length(rest) done done ";

    /// The name of the first `μ` binder in a printed type.
    fn binder(ty: &str) -> &str {
        let start = ty.find('μ').expect("a recursive type") + 'μ'.len_utf8();
        &ty[start..ty[start..].find('.').unwrap() + start]
    }

    #[test]
    fn a_list_length_function_infers_a_recursive_variant() {
        let ty = type_of(&format!("{LENGTH} length")).unwrap();
        let t = binder(&ty);
        assert!(
            ty.starts_with(&format!("(μ{t}. [Empty, Link: {{0: t")),
            "{ty}"
        );
        assert!(ty.ends_with(&format!(", 1: {t}}}]) -> Number")), "{ty}");
    }

    const SUM: &str = "sum = program(xs) do match xs do [] then 0 \
         [first, ...rest] then first + sum(rest) done done ";

    #[test]
    fn list_patterns_infer_the_same_recursive_variant_as_tag_patterns() {
        let from_tags = type_of(&format!("{LENGTH} length")).unwrap();
        let from_lists = type_of(
            "length = program(xs) do match xs do [] then 0 \
             [first, ...rest] then 1 + length(rest) done done length",
        )
        .unwrap();
        assert_eq!(from_lists, from_tags);
    }

    #[test]
    fn list_literals_type_as_links_ending_in_empty() {
        let ty = type_of("[]").unwrap();
        assert_eq!(ty, type_of("Empty").unwrap());
        let ty = type_of("[1, 2]").unwrap();
        assert_eq!(ty, type_of("Link(1, Link(2, Empty))").unwrap());
        assert_eq!(type_of(&format!("{SUM} sum([1, 2, 3])")).unwrap(), "Number");
        assert_eq!(type_of(&format!("{SUM} sum([])")).unwrap(), "Number");
    }

    #[test]
    fn nested_lists_check_and_flow_through_recursive_functions() {
        let total = "total = program(xss) do match xss do [] then 0 \
                     [xs, ...more] then sum(xs) + total(more) done done ";
        let src = format!("{SUM} {total} total([[1, 2], [], [3]])");
        assert_eq!(type_of(&src).unwrap(), "Number");
    }

    #[test]
    fn a_list_of_the_wrong_element_type_is_a_spanned_type_error() {
        let src = format!("{SUM} sum([1, true])");
        let errors = check(&src).err().expect("a type error");
        assert!(errors[0].span.start >= SUM.len(), "{:?}", errors[0]);
    }

    #[test]
    fn a_fixed_length_pattern_rejects_a_list_that_may_be_longer() {
        let errors = check("[a, b] = [1, 2, 3] a").err().expect("an error");
        assert!(errors[0].message.contains("doesn't handle"), "{errors:?}");
        assert!(check("[a, b] = [1, 2] a").is_ok());
        assert!(
            check("f = program(xs) do match xs do [a, b] then a else 0 done done f([1])").is_ok()
        );
    }

    #[test]
    fn a_recursive_function_is_polymorphic_in_its_elements() {
        let src = format!(
            "{LENGTH} length(Link(1, Link(2, Empty))) + length(Link(true, Empty)) + length(Empty)"
        );
        assert_eq!(type_of(&src).unwrap(), "Number");
    }

    #[test]
    fn a_tree_recurses_through_both_children() {
        let src = "tag Leaf tag Node size = program(t) do match t do Leaf then 0 \
                   Node(l, r) then 1 + size(l) + size(r) done done size";
        let ty = type_of(src).unwrap();
        let t = binder(&ty);
        assert_eq!(
            ty,
            format!("(μ{t}. [Leaf, Node: {{0: {t}, 1: {t}}}]) -> Number")
        );
    }

    #[test]
    fn building_a_recursive_value_types_as_an_open_recursive_variant() {
        let src =
            "build = program(n) do if n < 1 then Empty else Link(n, build(n - 1)) done done build";
        let ty = type_of(src).unwrap();
        let t = binder(&ty);
        assert!(
            ty.starts_with(&format!(
                "(Number) -> μ{t}. [Empty, Link: {{0: Number, 1: {t}}} | t"
            )),
            "{ty}"
        );
    }

    #[test]
    fn a_recursive_value_matches_through_nested_unfoldings() {
        let src = format!(
            "{LENGTH} second = program(xs) do match xs do Empty then 0 \
             Link(a, r) then match r do Empty then 0 Link(b, s) then length(s) done done done \
             second(Link(1, Link(2, Link(3, Empty))))"
        );
        assert_eq!(type_of(&src).unwrap(), "Number");
    }

    #[test]
    fn a_recursion_with_no_base_case_still_has_a_type() {
        let src = "tag Next f = program(xs) do match xs do Next(n) then f(n) done done f";
        let ty = type_of(src).unwrap();
        let t = binder(&ty);
        assert!(ty.starts_with(&format!("(μ{t}. [Next: {t}]) -> t")), "{ty}");
        let two = "tag Next f = program(xs) do match xs do Next(n) then match n do Next(m) then f(m) done done done f";
        assert!(type_of(two).is_ok());
    }

    #[test]
    fn a_function_returning_its_own_wrapped_result_is_recursive() {
        let ty = type_of("tag Wrap f = program(x) do Wrap(f(x)) done f").unwrap();
        let t = binder(&ty);
        assert!(ty.contains(&format!("μ{t}. [Wrap: {t} | t")), "{ty}");
    }

    #[test]
    fn two_recursive_types_unify() {
        let src = format!(
            "{LENGTH} both = program(xs, ys) do a = length(xs) b = length(ys) \
             if true then xs else ys done done both"
        );
        assert!(type_of(&src).is_ok());
    }

    #[test]
    fn rebuilding_a_scrutinee_ties_the_row_itself() {
        let src = "f = program(xs) do \
                     z = match xs do Empty then 0 else 1 done \
                     match xs do Empty then Link(1, xs) else xs done \
                   done f";
        let ty = type_of(src).unwrap();
        let t = binder(&ty);
        assert!(
            ty.starts_with(&format!("(μ{t}. [Empty, Link: {{0: Number, 1: {t}}} | t")),
            "{ty}"
        );
        let after_empty = "f = program(xs) do \
                     z = match xs do Empty then 0 else 1 done \
                     if true then xs else Link(1, xs) done \
                   done f";
        assert!(type_of(after_empty).is_ok());
    }

    #[test]
    fn a_cycle_outside_a_variant_tag_is_still_infinite() {
        for src in [
            "f = program(x) do x(x) done f",
            "tag Wrap f = program(x) do Wrap(x(x)) done f",
            "f = program(x) do {a: x(x)} done f",
            "f = program(r) do if true then r else {a: r} done done f",
        ] {
            let err = type_of(src).unwrap_err();
            assert!(err.contains("infinite type"), "{src}: {err}");
        }
    }

    #[test]
    fn a_recursive_variant_still_rejects_the_wrong_shape() {
        for tail in ["3", "Wrong", "Link(1, 2)", "Link(true, Empty) + 1"] {
            let src = format!("{LENGTH} length(Link(1, {tail}))");
            assert!(type_of(&src).is_err(), "{src}");
        }
        let err = type_of(&format!("{LENGTH} length(Link(1, Wrong))")).unwrap_err();
        assert!(err.contains("`Wrong`"), "{err}");
    }

    #[test]
    fn a_recursive_program_type_checks_with_no_unused_tag_warning() {
        let src = format!("{LENGTH} length(Link(1, Empty))");
        assert!(warnings_of(&src).is_empty());
    }

    #[test]
    fn recursive_types_survive_in_schemes_and_node_types() {
        let checked = check(&format!("{LENGTH} length")).unwrap();
        let scheme = checked.typed.schemes.values().next().unwrap();
        let printed = scheme.ty.to_string();
        assert!(printed.contains('μ'), "{printed}");
        assert!(
            checked
                .typed
                .node_types
                .values()
                .any(|t| t.to_string().contains('μ')),
            "no node carries the recursive type"
        );
    }

    #[test]
    fn calling_a_non_function_is_a_clear_error() {
        assert!(type_of("1(2)").unwrap_err().contains("is not a function"));
        // the sequencing-mistake shape: `(…)` right after an expression
        assert!(
            type_of("x = 1 (2)")
                .unwrap_err()
                .contains("is not a function")
        );
        // a real call still works
        assert_eq!(type_of("f = program(x) do x done f(1)").unwrap(), "Number");
    }

    #[test]
    fn capturing_closures_type_check() {
        let curried = "add = program(a) do program(b) do a + b done done add(1)(2)";
        assert_eq!(type_of(curried).unwrap(), "Number");

        let recursive = "outer = program(n) do \
                           go = program(k) do if k < 1 then 0 else n + go(k - 1) done done \
                           go(3) \
                         done \
                         outer(10)";
        assert_eq!(type_of(recursive).unwrap(), "Number");

        let polymorphic_apply = "apply = program(f, x) do f(x) done \
                                 n = 10 \
                                 t = true \
                                 addn = program(x) do x + n done \
                                 pick = program(b) do if t then b else false done done \
                                 if apply(pick, true) then apply(addn, 1) else 0 done";
        assert_eq!(type_of(polymorphic_apply).unwrap(), "Number");

        let record_of_functions = "k = 10 \
                                   r = {f: program(x) do x + k done, g: program(x) do x * k done}; \
                                   (r.f)(3) + (r.g)(2)";
        assert_eq!(type_of(record_of_functions).unwrap(), "Number");
    }

    #[test]
    fn capturing_closures_reject_ill_typed_calls() {
        assert!(type_of("add = program(a) do program(b) do a + b done done add(1)(true)").is_err());
        assert!(type_of("k = 10 f = program(x) do x + k done f(true)").is_err());
    }

    #[test]
    fn literals() {
        assert_eq!(type_of("1").unwrap(), "Number");
        assert_eq!(type_of("1.5").unwrap(), "Number");
        assert_eq!(type_of("\"hi\"").unwrap(), "String");
        assert_eq!(type_of("true").unwrap(), "Bool");
        assert_eq!(type_of("").unwrap(), "Unit");
    }

    #[test]
    fn a_literal_with_a_point_or_an_exponent_is_a_float() {
        assert_eq!(exact_type_of("3"), "Int");
        assert_eq!(exact_type_of("007"), "Int");
        for float in ["3.0", "3.5", "1e3", "2.5E-2", ".5", "5."] {
            assert_eq!(exact_type_of(float), "Float", "{float}");
        }
    }

    #[test]
    fn a_whole_number_too_big_for_an_int_is_an_error() {
        let (message, shown) = spanned_error("9223372036854775808");
        assert!(message.contains("too big"), "{message}");
        assert_eq!(shown, "9223372036854775808");
        assert_eq!(exact_type_of("9223372036854775807"), "Int");
    }

    #[test]
    fn an_int_beside_a_float_widens_to_a_float() {
        assert_eq!(exact_type_of("3 + 1.5"), "Float");
        assert_eq!(exact_type_of("1.5 + 3"), "Float");
        assert_eq!(exact_type_of("n = 3  n + 1.5"), "Float");
        assert_eq!(exact_type_of("2 * 3"), "Int");
        assert_eq!(type_of("3 < 4.5").unwrap(), "Bool");
        assert_eq!(type_of("1 == 1.0").unwrap(), "Bool");
    }

    #[test]
    fn division_is_always_a_float() {
        assert_eq!(exact_type_of("7 / 2"), "Float");
        assert_eq!(exact_type_of("4 / 2"), "Float");
        assert_eq!(
            exact_type_of("half = program(n) do n / 2 done  half(3)"),
            "Float"
        );
        assert_eq!(
            exact_type_of("{x: 9, y: 8} / {x: 3, y: 2}"),
            "{x: Float, y: Float}"
        );
    }

    #[test]
    fn a_numeric_function_works_at_both_int_and_float() {
        let add = "add = program(a, b) do a + b done ";
        assert_eq!(exact_type_of(&format!("{add} add(1, 2)")), "Int");
        assert_eq!(exact_type_of(&format!("{add} add(1.5, 2)")), "Float");
        let both = format!("{add} a = add(1, 2)  b = add(1.5, 2)  {{a: a, b: b}}");
        assert_eq!(exact_type_of(&both), "{a: Int, b: Float}");
        let scale = "scale = program(x) do x * 2 done  a = scale(3)  b = scale(1.5) {a: a, b: b}";
        assert_eq!(exact_type_of(scale), "{a: Int, b: Float}");
    }

    #[test]
    fn a_shared_number_is_a_float_once_anything_needs_a_float() {
        assert_eq!(exact_type_of("n = 3  a = n + 1.5  n"), "Float");
        assert_eq!(exact_type_of("n = 3  a = n / 2  n"), "Int");
    }

    #[test]
    fn a_foreign_int_meets_a_float_only_by_widening() {
        let count = "count = foreign \"m\" \"count\" () -> Int\n";
        let take = "take = foreign \"m\" \"take\" (Int) -> Unit\n";
        assert_eq!(exact_type_of(&format!("{count}count()")), "Int");
        assert_eq!(exact_type_of(&format!("{count}count() + 1")), "Int");
        assert_eq!(exact_type_of(&format!("{count}count() + 1.5")), "Float");
        assert_eq!(exact_type_of(&format!("{count}count() / 2")), "Float");
        assert_eq!(type_of(&format!("{take}take(3)")).unwrap(), "Unit");
        assert_eq!(
            type_of(&format!("{take}take(1.5)")).unwrap_err(),
            "type mismatch: expected `Int`, found `Float`"
        );
        assert_eq!(
            type_of(&format!("{take}take(2.0)")).unwrap_err(),
            "type mismatch: expected `Int`, found `Float`"
        );
    }

    #[test]
    fn floor_division_and_remainder_are_ints() {
        assert_eq!(exact_type_of("7 // 2"), "Int");
        assert_eq!(exact_type_of("7 % 2"), "Int");
        assert_eq!(exact_type_of("7 // 2 * 3 % 4"), "Int");
        let halve = "halve = program(n) do n // 2 done ";
        assert_eq!(exact_type_of(&format!("{halve} halve(9)")), "Int");
        assert_eq!(exact_type_of("n = 7  m = n // 2  n"), "Int");
    }

    #[test]
    fn floor_division_and_remainder_reject_a_float() {
        for (source, operand) in [
            ("7.5 // 2", "7.5"),
            ("7 // 2.0", "2.0"),
            ("7 % 2.5", "2.5"),
            ("1e3 % 7", "1e3"),
            ("x = 2.5  7 // x", "x"),
            ("(7 / 2) // 2", "7 / 2"),
        ] {
            let (message, shown) = spanned_error(source);
            assert!(message.contains("needs whole numbers"), "{message}");
            assert!(message.contains("round"), "{message}");
            assert_eq!(shown, operand, "{source}");
        }
        let halve = "halve = program(n) do n // 2 done ";
        assert_eq!(
            type_of(&format!("{halve} halve(2.5)")).unwrap_err(),
            "type mismatch: expected `Int`, found `Float`"
        );
        assert_eq!(
            type_of("\"a\" // 2").unwrap_err(),
            "type mismatch: expected `Number`, found `String`"
        );
    }

    #[test]
    fn floor_division_binds_like_multiplication() {
        assert_eq!(exact_type_of("1 + 7 // 2"), "Int");
        assert_eq!(exact_type_of("1.5 + 7 // 2"), "Float");
        assert_eq!(exact_type_of("7 // 2 + 0.5"), "Float");
    }

    #[test]
    fn an_int_argument_widens_to_a_float_parameter() {
        let take = "take = foreign \"m\" \"take\" (Number) -> Unit\n";
        let scale = "scale = program(x) do x * 1.5 done\n";
        assert_eq!(type_of(&format!("{take}take(7 // 2)")).unwrap(), "Unit");
        assert_eq!(type_of(&format!("{take}take(2.5)")).unwrap(), "Unit");
        assert_eq!(exact_type_of(&format!("{scale}scale(7 // 2)")), "Float");
        assert_eq!(
            type_of(&format!("{take}take(true)")).unwrap_err(),
            "type mismatch: expected `Number`, found `Bool`"
        );
    }

    #[test]
    fn diagnostics_say_number() {
        assert_eq!(
            type_of("1 + true").unwrap_err(),
            "type mismatch: expected `Number`, found `Bool`"
        );
        assert_eq!(
            type_of("1.5 + true").unwrap_err(),
            "type mismatch: expected `Number`, found `Bool`"
        );
        assert_eq!(
            type_of("true < 1").unwrap_err(),
            "type mismatch: expected `Number`, found `Bool`"
        );
        assert_eq!(
            type_of("if 1 then 2 else 3 done").unwrap_err(),
            "type mismatch: expected `Bool`, found `Number`"
        );
        assert_eq!(
            type_of("\"a\" / 2").unwrap_err(),
            "`/` needs numbers or records of numbers, but this is `String`"
        );
    }

    #[test]
    fn arithmetic_and_comparison() {
        assert_eq!(type_of("1 + 2 * 3").unwrap(), "Number");
        assert_eq!(type_of("1 < 2").unwrap(), "Bool");
        assert_eq!(type_of("(1 + 2) < 3").unwrap(), "Bool");
    }

    #[test]
    fn arithmetic_rejects_non_numbers() {
        assert!(type_of("1 + true").is_err());
        assert!(type_of("\"a\" * 2").is_err());
    }

    #[test]
    fn declaration_binds_and_sequences() {
        assert_eq!(type_of("x = 1 x + 2").unwrap(), "Number");
        assert_eq!(type_of("x = 1").unwrap(), "Number");
    }

    #[test]
    fn unknown_name_is_an_error() {
        assert_eq!(type_of("x + 1").unwrap_err(), "unknown name `x`");
    }

    #[test]
    fn identity_function_is_polymorphic() {
        // `program(x) do x done` : (t) -> t
        let ty = type_of("program(x) do x done").unwrap();
        assert!(ty.contains("->"), "expected a function type, got {ty}");
        // applied to a number, yields a number
        assert_eq!(
            type_of("id = program(x) do x done id(1)").unwrap(),
            "Number"
        );
    }

    #[test]
    fn let_polymorphism() {
        // The same identity binding is used at two different types.
        let src = "id = program(x) do x done a = id(1) b = id(true) b";
        assert_eq!(type_of(src).unwrap(), "Bool");
    }

    #[test]
    fn function_application_checks_arguments() {
        assert_eq!(
            type_of("add = program(a, b) do a + b done add(1, 2)").unwrap(),
            "Number"
        );
        // wrong argument type
        assert!(type_of("add = program(a, b) do a + b done add(1, true)").is_err());
        // wrong arity
        assert!(type_of("add = program(a, b) do a + b done add(1)").is_err());
    }

    #[test]
    fn recursion_checks() {
        // A recursive countdown: program(n) do if n < 1 then 0 else count(n - 1) done done
        let src = "count = program(n) do if n < 1 then 0 else count(n - 1) done done count(5)";
        assert_eq!(type_of(src).unwrap(), "Number");
    }

    #[test]
    fn records_infer_and_access() {
        assert_eq!(type_of("{x: 1, y: 2}").unwrap(), "{x: Number, y: Number}");
        assert_eq!(type_of("p = {x: 1, y: true} p.x").unwrap(), "Number");
        assert_eq!(type_of("p = {x: 1, y: true} p.y").unwrap(), "Bool");
        // nested records
        assert_eq!(
            type_of("line = {from: {x: 0}, to: {x: 10}} line.to.x").unwrap(),
            "Number"
        );
    }

    #[test]
    fn record_field_errors() {
        // accessing a field the record does not have
        assert!(type_of("p = {x: 1} p.z").is_err());
        // a field used as the wrong type
        assert!(type_of("p = {x: 1} p.x + true").is_err());
    }

    #[test]
    fn record_field_access_is_row_polymorphic() {
        // `program(p) do p.x done` accepts any record with an `x` field, so it
        // applies to records of different shapes.
        let src = "getx = program(p) do p.x done \
                   a = getx({x: 1, y: 2}) \
                   b = getx({x: 9, z: true}) \
                   a + b";
        assert_eq!(type_of(src).unwrap(), "Number");
    }

    #[test]
    fn conditional_branches_must_agree() {
        assert_eq!(type_of("if true then 1 else 2 done").unwrap(), "Number");
        assert!(type_of("if true then 1 else false done").is_err());
        assert!(type_of("if 1 then 2 else 3 done").is_err());
    }

    /// The contract mono relies on: a let-bound symbol's scheme, `Var`
    /// use sites typed at their instantiation, and the generalized body still
    /// mentioning the scheme's quantified variable.
    #[test]
    fn schemes_and_instantiated_node_types() {
        use crate::hir::ExprKind;
        use crate::ty::Ty;

        let checked = check("id = program(x) do x done\na = id(1)\nb = id(true)\nb").unwrap();
        let typed = &checked.typed;

        let hir::ExprKind::Let {
            symbol: id_sym,
            value: id_value,
            rest: Some(rest_a),
            ..
        } = &checked.root.kind
        else {
            panic!("expected `id` let");
        };
        let hir::ExprKind::Let {
            value: a_value,
            rest: Some(rest_b),
            ..
        } = &rest_a.kind
        else {
            panic!("expected `a` let");
        };
        let hir::ExprKind::Let { value: b_value, .. } = &rest_b.kind else {
            panic!("expected `b` let");
        };

        let scheme = &typed.schemes[id_sym];
        assert_eq!(scheme.vars.len(), 1);
        let quantified = scheme.vars[0];
        assert_eq!(
            scheme.ty,
            Ty::Func(vec![Ty::Var(quantified)], Box::new(Ty::Var(quantified)))
        );

        let callee_ty = |call: &crate::hir::Expr| {
            let ExprKind::App { callee, .. } = &call.kind else {
                panic!("expected a call");
            };
            assert!(matches!(&callee.kind, ExprKind::Var { symbol, .. } if symbol == id_sym));
            typed.node_types[&callee.id].to_string()
        };
        assert_eq!(callee_ty(a_value), "(Number) -> Number");
        assert_eq!(callee_ty(b_value), "(Bool) -> Bool");

        let ExprKind::Func { body, .. } = &id_value.kind else {
            panic!("expected a function");
        };
        assert_eq!(typed.node_types[&body.id], Ty::Var(quantified));
    }

    #[test]
    fn calls_on_any_callee() {
        let src = "vec = {add: program(p, q) do p.x + q.x done}; (vec.add)({x: 1}, {x: 2})";
        assert_eq!(type_of(src).unwrap(), "Number");
        // chained calls and accesses nest left to right
        assert_eq!(
            type_of("f = program(x) do program(y) do x + y done done f(1)(2)").unwrap(),
            "Number"
        );
        assert_eq!(
            type_of("a = {b: {c: program(x) do x done}}; (a.b.c)(1)").unwrap(),
            "Number"
        );
        // a call result can be accessed
        assert_eq!(
            type_of("f = program() do {x: true} done f().x").unwrap(),
            "Bool"
        );
        // a grouped expression is not a call
        assert_eq!(type_of("(1 + 2) < 3").unwrap(), "Bool");
        // calling a non-function is a checker error, not a panic
        assert!(type_of("1(2)").is_err());
    }

    #[test]
    fn negation_and_subtraction() {
        assert_eq!(type_of("-3").unwrap(), "Number");
        assert_eq!(type_of("--3").unwrap(), "Number");
        assert_eq!(type_of("a = 1 1 - a").unwrap(), "Number");
        // `5 -1` is the subtraction `5 - 1`, never `5` followed by `-1`
        assert_eq!(type_of("5 -1").unwrap(), "Number");
        assert_eq!(type_of("5 - -1").unwrap(), "Number");
        // negation binds tighter than `*` and applies to a whole postfix chain
        assert_eq!(type_of("p = {x: 2} 3 * -p.x").unwrap(), "Number");
        assert!(type_of("-true").is_err());
    }

    #[test]
    fn duplicate_record_labels_are_rejected() {
        let err = type_of("{x: 1, x: 2}").unwrap_err();
        assert!(err.contains("duplicate") && err.contains("`x`"), "{err}");
        assert!(type_of("{x: 1, y: 2}").is_ok());
    }

    #[test]
    fn empty_string_and_lenient_literals() {
        assert_eq!(type_of("\"\"").unwrap(), "String");
        assert_eq!(type_of(".5").unwrap(), "Number");
        assert_eq!(type_of("007").unwrap(), "Number");
        assert_eq!(type_of("{x: 1,}").unwrap(), "{x: Number}");
        assert_eq!(type_of("f = program(a) do a done f(1,)").unwrap(), "Number");
    }

    #[test]
    fn mismatch_reads_expected_then_found_on_the_offending_span() {
        let errors = check("1 + true").err().expect("type error");
        assert_eq!(
            errors[0].message,
            "type mismatch: expected `Number`, found `Bool`"
        );
        assert_eq!((errors[0].span.start, errors[0].span.end), (4, 8));
        assert_eq!(
            type_of("add = program(a, b) do a + b done add(1, true)").unwrap_err(),
            "type mismatch: expected `Number`, found `Bool`"
        );
    }

    #[test]
    fn reusing_a_parameter_at_two_types_names_the_parameter() {
        assert_eq!(
            type_of("use = program(m) do a = m.id + 1\n if m.id then 1 else 2 done done use(1)")
                .unwrap_err(),
            "`m` is a parameter, so m.id can only be used at one type here; bind it with `=` instead"
        );
        assert_eq!(
            type_of("both = program(f) do a = f(1)\n b = f(true)\n b done").unwrap_err(),
            "`f` is a parameter, so it can only be used at one type here; bind it with `=` instead"
        );
        assert_eq!(
            type_of("use2 = program(g) do a = g({x: 1})\n b = g({x: 2, y: 3})\n b done use2(1)")
                .unwrap_err(),
            "`g` is a parameter, so it can only be used at one type here; bind it with `=` instead"
        );
    }

    #[test]
    fn ordinary_mismatches_and_bound_functions_keep_their_messages() {
        assert_eq!(
            type_of("1 + true").unwrap_err(),
            "type mismatch: expected `Number`, found `Bool`"
        );
        assert_eq!(
            type_of("f = program(x) do x done\n a = f(1)\n b = f(true)\n b").unwrap(),
            "Bool"
        );
        assert_eq!(
            type_of("f = program(n) do n + 1 done\n g = program(h) do h(true) done\n g(f)")
                .unwrap_err(),
            "type mismatch: expected `Number`, found `Bool`"
        );
    }

    #[test]
    fn missing_field_is_reported_as_missing() {
        assert_eq!(
            type_of("{x: 1}.y").unwrap_err(),
            "record is missing field `y`"
        );
    }

    #[test]
    fn conditional_without_else_must_be_unit() {
        assert_eq!(
            type_of("if true then 1 done").unwrap_err(),
            "type mismatch: expected `Unit`, found `Number`"
        );
        assert_eq!(
            type_of("nop = program() do done if true then nop() done").unwrap(),
            "Unit"
        );
    }

    #[test]
    fn mutual_recursion_works_in_either_order() {
        let even_first = "is_even = program(n) do if n < 1 then true else is_odd(n - 1) done done \
                          is_odd = program(n) do if n < 1 then false else is_even(n - 1) done done \
                          is_even(4)";
        let odd_first = "is_odd = program(n) do if n < 1 then false else is_even(n - 1) done done \
                         is_even = program(n) do if n < 1 then true else is_odd(n - 1) done done \
                         is_even(4)";
        assert_eq!(type_of(even_first).unwrap(), "Bool");
        assert_eq!(type_of(odd_first).unwrap(), "Bool");
    }

    #[test]
    fn mutual_recursion_rejects_ill_typed_calls() {
        let src = "f = program(n) do g(true) done g = program(n) do n + 1 done f(1)";
        assert!(type_of(src).is_err());
    }

    #[test]
    fn value_bindings_shadow() {
        assert_eq!(
            type_of("score = 1 score = score + 1 score").unwrap(),
            "Number"
        );
        assert_eq!(
            type_of("score = score + 1").unwrap_err(),
            "unknown name `score`"
        );
        assert_eq!(
            type_of("ones = Link(1, ones)").unwrap_err(),
            "unknown name `ones`"
        );
        assert_eq!(
            type_of("ones = {a: ones}").unwrap_err(),
            "unknown name `ones`"
        );
    }

    #[test]
    fn duplicate_parameter_is_an_error() {
        assert_eq!(
            type_of("program(a, a) do a done").unwrap_err(),
            "duplicate parameter `a`"
        );
    }

    /// The single error of a program rejected for use before definition: its
    /// message and the source text its span covers.
    fn order_error(source: &str) -> (String, &str) {
        let errors = check(source).err().expect("rejected");
        assert_eq!(errors.len(), 1, "{errors:?}");
        let span = errors[0].span;
        (errors[0].message.clone(), &source[span.start..span.end])
    }

    #[test]
    fn function_run_before_a_value_it_reads_is_rejected() {
        let src = "f = program() do g() done  x = f()  m = 5  g = program() do m done  x";
        let errors = check(src).err().expect("rejected");
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].message, "`f` uses `m` before it is defined");
        assert_eq!(errors[0].span.start, src.find("f()  m").unwrap());
        assert_eq!(errors[0].span.end, errors[0].span.start + 1);
    }

    #[test]
    fn function_value_taken_before_a_value_it_reads_is_rejected() {
        let src = "f = program() do g() done  h = f  m = 5  g = program() do m done  h()";
        assert_eq!(
            order_error(src),
            ("`f` uses `m` before it is defined".to_string(), "f")
        );
    }

    #[test]
    fn program_literal_built_before_a_value_it_reads_is_rejected() {
        let src = "apply = program(h) do h() done \
                   z = apply(program() do g() done) \
                   m = 5 \
                   g = program() do m done \
                   z";
        assert_eq!(
            order_error(src),
            (
                "this program uses `m` before it is defined".to_string(),
                "program() do g() done"
            )
        );
    }

    #[test]
    fn order_is_checked_in_every_scope() {
        let src = "outer = program() do \
                     f = program() do g() done \
                     x = f() \
                     m = 5 \
                     g = program() do m done \
                     x \
                   done \
                   outer()";
        assert_eq!(
            order_error(src),
            ("`f` uses `m` before it is defined".to_string(), "f")
        );
    }

    #[test]
    fn function_run_before_a_generalized_value_it_reads_is_rejected() {
        let src = "f = program() do g() done  x = f()  \
                   m = {y: program(s) do s done}  \
                   g = program() do (m.y)(1) done  x";
        assert_eq!(
            order_error(src),
            ("`f` uses `m` before it is defined".to_string(), "f")
        );
    }

    #[test]
    fn functions_may_run_once_their_values_are_defined() {
        for src in [
            "f = program() do g() done  m = 5  g = program() do m done  f()",
            "m = 5  f = program() do g() done  g = program() do m done  f()",
            "m = 5  g = program() do m done  f = program() do g() done  f()",
            "f = program() do g() done  m = 5  g = program() do m done  x = f()  x",
            "g = program() do 0 done  m = 5  x = f()  f = program() do m done  x",
            "f = program() do g() done  g = program() do 1 done  f()",
            "m = 5  f = program() do g() done  h = f  g = program() do m done  h()",
            "outer = program() do \
               f = program() do g() done \
               m = 5 \
               g = program() do m done \
               f() \
             done \
             outer()",
        ] {
            assert_eq!(type_of(src).unwrap(), "Number", "{src}");
        }
    }

    #[test]
    fn mutual_recursion_with_earlier_values_still_checks() {
        let src = "limit = 4 \
                   is_even = program(n) do if n < 1 then true else is_odd(n - 1) done done \
                   is_odd = program(n) do if n < 1 then false else is_even(n - 1) done done \
                   is_even(limit)";
        assert_eq!(type_of(src).unwrap(), "Bool");
    }

    #[test]
    fn mutual_recursion_spans_a_destructure() {
        let src = "is_even = program(n) do if n < 1 then true else is_odd(n - 1) done done \
                   {a} = {a: 1} \
                   is_odd = program(n) do if n < 1 then false else is_even(n - 1) done done \
                   is_even(a + 3)";
        assert_eq!(type_of(src).unwrap(), "Bool");
    }

    fn chain(n: usize) -> String {
        vec!["1"; n].join(" + ")
    }

    #[test]
    fn deeply_nested_expression_is_a_clean_error() {
        let Err(errors) = check(&chain(100_000)) else {
            panic!("expected an error");
        };
        assert_eq!(errors[0].message, "expression nested too deeply");
        assert_eq!(errors[0].span.start, 0);
    }

    #[test]
    fn moderately_nested_expression_still_checks() {
        assert_eq!(type_of(&chain(200)).unwrap(), "Number");
    }

    fn first_error(source: &str) -> GoatError {
        check(source).err().expect("an error").remove(0)
    }

    #[test]
    fn spread_adds_a_field() {
        let src = "p = {x: 1} {...p, y: true}";
        assert_eq!(type_of(src).unwrap(), "{y: Bool, x: Number}");
        assert_eq!(type_of("p = {x: 1} {...p}").unwrap(), "{x: Number}");
    }

    #[test]
    fn spread_override_replaces_the_field_even_at_a_new_type() {
        let same = "p = {x: 1, y: 2} {...p, x: 5}";
        assert_eq!(type_of(same).unwrap(), "{x: Number, y: Number}");
        let changed = "p = {x: 1, y: 2} {...p, x: \"one\"}";
        assert_eq!(type_of(changed).unwrap(), "{x: String, y: Number}");
        assert_eq!(
            type_of("p = {x: 1} q = {...p, x: true} q.x").unwrap(),
            "Bool"
        );
    }

    #[test]
    fn spread_of_an_unknown_record_stays_polymorphic_in_the_rest() {
        let src = "bump = program(m) do {...m, x: 1} done \
                   a = bump({y: true}) \
                   b = bump({x: \"s\", z: 2}) \
                   if a.y then b.x + a.x else 0 done";
        assert_eq!(type_of(src).unwrap(), "Number");
    }

    #[test]
    fn spread_update_of_a_field_it_reads_can_recurse() {
        let src = "countdown = program(s) do \
                     if s.n < 1 then s else countdown({...s, n: s.n - 1}) done done \
                   countdown({n: 3, label: true}).label";
        assert_eq!(type_of(src).unwrap(), "Bool");
    }

    #[test]
    fn spread_needs_a_record_and_mentions_what_it_got() {
        let err = first_error("{...3, x: 1}");
        assert!(err.message.contains("copies a record"), "{}", err.message);
        assert!(err.message.contains("Number"), "{}", err.message);
        assert_eq!((err.span.start, err.span.end), (4, 5));
    }

    #[test]
    fn two_spreads_cannot_merge() {
        let src = "a = {x: 1} b = {y: 2} {...a, ...b}";
        let err = first_error(src);
        assert!(
            err.message
                .contains("can't merge two records of unknown shape here"),
            "{}",
            err.message
        );
        assert_eq!(&src[err.span.start..err.span.end], "...b");
        assert!(check("a = {x: 1} {...a, x: 2, ...a}").is_err());
    }

    #[test]
    fn a_spread_must_come_first() {
        let src = "a = {x: 1} {y: 2, ...a}";
        let err = first_error(src);
        assert!(err.message.contains("must come first"), "{}", err.message);
        assert_eq!(&src[err.span.start..err.span.end], "...a");
    }

    #[test]
    fn spread_keeps_duplicate_field_detection() {
        let err = first_error("a = {x: 1} {...a, y: 1, y: 2}");
        assert!(
            err.message.contains("duplicate field `y`"),
            "{}",
            err.message
        );
    }

    #[test]
    fn destructuring_binds_each_field() {
        let src = "point = {x: 1, y: true} {x, y} = point if y then x else 0 done";
        assert_eq!(type_of(src).unwrap(), "Number");
        assert_eq!(type_of("{x} = {x: 1, y: true}  x").unwrap(), "Number");
        assert_eq!(type_of("{x, y} = {x: 1, y: true}").unwrap(), "Bool");
    }

    #[test]
    fn destructuring_accepts_any_record_with_at_least_those_fields() {
        let src = "norm = program(p) do {x, y} = p x + y done \
                   norm({x: 1, y: 2}) + norm({a: 0, x: 3, y: 4, z: true})";
        assert_eq!(type_of(src).unwrap(), "Number");
    }

    #[test]
    fn destructuring_a_missing_field_points_at_the_name() {
        let src = "p = {x: 1} {x, z} = p x";
        let err = first_error(src);
        assert!(err.message.contains("missing field `z`"), "{}", err.message);
        assert_eq!(&src[err.span.start..err.span.end], "z");
    }

    #[test]
    fn destructured_names_scope_over_the_rest_and_shadow() {
        assert_eq!(type_of("{x} = {x: 1} {x} = {x: true} x").unwrap(), "Bool");
        assert!(type_of("f = program(p) do {x} = p x done x").is_err());
        let err = first_error("p = {x: 1} {x, x} = p x");
        assert!(
            err.message.contains("duplicate name `x`"),
            "{}",
            err.message
        );
    }

    #[test]
    fn parameter_destructuring() {
        let src = "norm = program({x, y}) do x * x + y * y done \
                   norm({x: 3, y: 4})";
        assert_eq!(type_of(src).unwrap(), "Number");
        let mixed = "f = program(a, {x}, b) do a + x + b done f(1, {x: 2, q: true}, 3)";
        assert_eq!(type_of(mixed).unwrap(), "Number");
        let err = first_error("f = program({x}) do x done f({y: 1})");
        assert!(err.message.contains("`x`"), "{}", err.message);
        let dup = first_error("f = program(x, {x}) do x done");
        assert!(
            dup.message.contains("duplicate parameter `x`"),
            "{}",
            dup.message
        );
    }

    #[test]
    fn rest_binds_the_record_without_the_named_fields() {
        let src = "{x, ...rest} = {x: 1, y: true, z: 2} rest";
        assert_eq!(type_of(src).unwrap(), "{y: Bool, z: Number}");
        let all = "{x, y, ...rest} = {x: 1, y: true} rest";
        assert_eq!(type_of(all).unwrap(), "{}");
        assert_eq!(type_of("{...rest} = {x: 1} rest").unwrap(), "{x: Number}");
        let param = "drop = program({x, ...r}) do r done drop({x: 1, y: true})";
        assert_eq!(type_of(param).unwrap(), "{y: Bool}");
    }

    #[test]
    fn rest_needs_the_removed_fields() {
        let err = first_error("{x, y, ...rest} = {x: 1} rest");
        assert!(err.message.contains("`y`"), "{}", err.message);
    }

    #[test]
    fn rest_refuses_a_label_a_spread_override_hid() {
        let bump = "bump = program(m) do {...m, x: 1} done \
                    drop = program({x, ...r}) do r done ";
        assert_eq!(
            type_of(&format!("{bump} drop(bump({{y: 2}}))")).unwrap(),
            "{y: Number}"
        );
        let err = first_error(&format!("{bump} drop(bump({{x: \"s\", y: 2}}))"));
        let twice = "`x` is in this record twice";
        assert!(err.message.contains(twice), "{}", err.message);
        let direct =
            first_error("bump = program(m) do {...m, x: 1} done {x, ...r} = bump({x: true}) r");
        assert!(direct.message.contains(twice), "{}", direct.message);
    }
    #[test]
    fn a_semicolon_runs_a_statement_and_keeps_the_rest() {
        assert_eq!(type_of("print(1); 2").unwrap(), "Number");
        assert_eq!(type_of("print(1); print(2); true").unwrap(), "Bool");
        assert_eq!(type_of("1; \"a\"").unwrap(), "String");
        assert_eq!(type_of("print(1);").unwrap(), "Unit");
    }

    #[test]
    fn a_statement_ends_only_at_a_semicolon() {
        // Without `;` a parenthesis or a minus continues the expression.
        let call = first_error("print(1) (2)");
        assert!(
            call.message.contains("is not a function"),
            "{}",
            call.message
        );
        assert!(type_of("print(1) - 2").is_err());
        assert_eq!(type_of("print(1); (2)").unwrap(), "Number");
        assert_eq!(type_of("print(1); -2").unwrap(), "Number");
    }

    #[test]
    fn bindings_scope_over_the_statements_after_them() {
        assert_eq!(type_of("x = 1; x + 1").unwrap(), "Number");
        assert_eq!(type_of("x = 1  print(x); x < 2").unwrap(), "Bool");
        assert_eq!(type_of("{a, b} = {a: 1, b: true}; b").unwrap(), "Bool");
        assert_eq!(
            type_of("f = program() do print(1); 2 done f()").unwrap(),
            "Number"
        );
    }

    #[test]
    fn and_or_not_are_booleans() {
        assert_eq!(type_of("true and false").unwrap(), "Bool");
        assert_eq!(type_of("true or 1 < 2").unwrap(), "Bool");
        assert_eq!(type_of("not 1 == 2").unwrap(), "Bool");
        assert_eq!(type_of("not not true").unwrap(), "Bool");
        assert_eq!(type_of("a = true b = false a or b").unwrap(), "Bool");
        assert_eq!(type_of("flag = true not flag").unwrap(), "Bool");
        for src in [
            "1 and true",
            "true or 1",
            "not 5",
            "if 1 and true then 1 else 2 done",
        ] {
            let err = type_of(src).unwrap_err();
            assert!(err.contains("must be a Bool"), "{src}: {err}");
        }
    }

    #[test]
    fn precedence_runs_or_and_not_equality_comparison() {
        // `or` is loosest, then `and`, then `not`, then `==`, then `<`.
        assert!(type_of("1 < 2 == true or false and 3").is_err());
        assert_eq!(type_of("1 < 2 == true or false and true").unwrap(), "Bool");
        assert_eq!(type_of("not 1 < 2 == false and true").unwrap(), "Bool");
        // `not a == b` is `not (a == b)`: `(not 1) == 2` would be a mismatch.
        assert_eq!(type_of("not 1 == 2").unwrap(), "Bool");
    }

    #[test]
    fn a_pile_of_nots_counts_toward_the_depth_limit() {
        assert_eq!(
            type_of(&format!("{}true", "not ".repeat(100))).unwrap(),
            "Bool"
        );
        let err = type_of(&format!("{}true", "not ".repeat(300))).unwrap_err();
        assert_eq!(err, "expression nested too deeply");
    }

    #[test]
    fn a_long_run_of_statements_costs_no_depth() {
        let statements = vec!["print(1)"; 5000].join("; ");
        assert_eq!(type_of(&format!("{statements}; 1")).unwrap(), "Number");
    }

    #[test]
    fn a_long_chain_of_bindings_costs_no_depth() {
        let bindings: Vec<String> = (1..3000)
            .map(|i| format!("a{i} = a{} + 1", i - 1))
            .collect();
        let src = format!("a0 = 0 {} a2999", bindings.join(" "));
        assert_eq!(type_of_on_a_big_stack(src).unwrap(), "Number");
    }

    /// The parser nests each binding's rest inside it, so a long chain needs
    /// more stack than a test thread has; the passes after it use none per
    /// link. Deeply nested source is likewise lowered recursively.
    fn type_of_on_a_big_stack(source: String) -> Result<String, String> {
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn(move || type_of(&source))
            .unwrap()
            .join()
            .unwrap()
    }

    #[test]
    fn a_literal_match_gives_back_the_depth_it_took() {
        let matches = vec!["match 1 do 1 then 0 else 2 done"; 300].join("; ");
        assert_eq!(type_of(&format!("{matches}; 1")).unwrap(), "Number");
    }

    #[test]
    fn a_deeply_nested_expression_is_still_a_clean_error() {
        let nested = format!("{}1{}", "(".repeat(300), ")".repeat(300));
        let err = type_of_on_a_big_stack(nested).unwrap_err();
        assert_eq!(err, "expression nested too deeply");
        let blocks = format!(
            "{}1{}",
            "if true then ".repeat(300),
            " else 2 done".repeat(300)
        );
        let err = type_of_on_a_big_stack(blocks).unwrap_err();
        assert_eq!(err, "expression nested too deeply");
    }

    #[test]
    fn statements_inside_a_nested_block_still_count_the_nesting() {
        let inner = vec!["print(1)"; 1000].join("; ");
        let wrap = |depth: usize| {
            format!(
                "{}{inner}; 1{}",
                "if true then ".repeat(depth),
                " else 2 done".repeat(depth)
            )
        };
        assert!(type_of_on_a_big_stack(wrap(200)).is_ok());
        let err = type_of_on_a_big_stack(wrap(300)).unwrap_err();
        assert_eq!(err, "expression nested too deeply");
    }

    /// `f0` wraps its argument in `{a: _}`; each later `f` composes the one
    /// before with itself (written as a function, since a computed binding is
    /// not generalized), so `f{levels}` nests the wrapper `2^levels` times.
    fn self_composed(levels: usize) -> String {
        let mut source = String::from(
            "compose = program(f, g) do program(x) do f(g(x)) done done\n\
             f0 = program(x) do {a: x} done\n",
        );
        for level in 1..=levels {
            let previous = level - 1;
            source +=
                &format!("f{level} = program(x) do compose(f{previous}, f{previous})(x) done\n");
        }
        source + &format!("f{levels}")
    }

    #[test]
    fn composing_a_generic_function_with_itself_is_a_spanned_resource_error() {
        let started = std::time::Instant::now();
        let source = self_composed(14);
        let Err(errors) = check(&source) else {
            panic!("a type of 2^14 parts should not check");
        };
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].message.starts_with("program too complex"),
            "{}",
            errors[0].message
        );
        let blamed = &source[errors[0].span.start..errors[0].span.end];
        assert!(
            blamed.starts_with("compose(f") && blamed.ends_with(')'),
            "{blamed}"
        );
        assert!(started.elapsed().as_secs() < 10, "{:?}", started.elapsed());
    }

    #[test]
    fn composing_a_generic_function_with_itself_a_few_times_still_checks() {
        let ty = type_of(&self_composed(6)).unwrap();
        assert!(ty.starts_with("(t"), "{ty}");
        assert_eq!(ty.matches("{a: ").count(), 64);
    }

    #[test]
    fn a_wide_record_is_fine_until_its_type_passes_the_term_limit() {
        let record = |fields: usize| {
            let body: Vec<String> = (0..fields).map(|i| format!("f{i}: {i}")).collect();
            format!("{{{}}}", body.join(", "))
        };
        assert!(type_of(&record(200)).is_ok());
        let source = record(600);
        let Err(errors) = check(&source) else {
            panic!("a 600-field record should not check");
        };
        assert!(errors[0].message.starts_with("program too complex"));
        assert_eq!(&source[errors[0].span.start..errors[0].span.end], source);
    }

    #[test]
    fn a_parameter_grown_one_field_at_a_time_hits_the_term_limit_before_the_stack() {
        let reads: Vec<String> = (0..600).map(|i| format!("a{i} = r.f{i}")).collect();
        let source = format!(
            "pick = program(r) do {} a0 done\npick({{f0: 1}})",
            reads.join(" ")
        );
        let Err(errors) = check(&source) else {
            panic!("a 600-field parameter should not check");
        };
        assert!(
            errors
                .iter()
                .all(|e| e.message.starts_with("program too complex")),
            "{:?}",
            errors[0]
        );
        let blamed = &source[errors[0].span.start..errors[0].span.end];
        assert_eq!(blamed, "r");
    }

    #[test]
    fn and_or_not_have_their_own_nodes() {
        let lowered = crate::lower::lower("a = true b = false a and b").unwrap();
        let hir::ExprKind::Let { rest, .. } = &lowered.root.kind else {
            panic!("expected a binding");
        };
        let hir::ExprKind::Let { rest, .. } = &rest.as_ref().unwrap().kind else {
            panic!("expected a binding");
        };
        assert!(matches!(
            rest.as_ref().unwrap().kind,
            hir::ExprKind::And { .. }
        ));
    }

    /// The blamed source text and the message of the first error.
    fn blame(source: &str) -> (String, String) {
        let Err(errors) = check(source) else {
            panic!("{source} should not check");
        };
        let span = errors[0].span;
        (
            source[span.start..span.end].to_string(),
            errors[0].message.clone(),
        )
    }

    #[test]
    fn a_non_bool_operand_is_blamed_and_the_operator_named() {
        let cases = [
            (
                "true and 1",
                "1",
                "the right side of `and` must be a Bool, found `Number`",
            ),
            (
                "1 and true",
                "1",
                "the left side of `and` must be a Bool, found `Number`",
            ),
            (
                "false or 1",
                "1",
                "the right side of `or` must be a Bool, found `Number`",
            ),
            (
                "1 or true",
                "1",
                "the left side of `or` must be a Bool, found `Number`",
            ),
            (
                "not 1",
                "1",
                "the operand of `not` must be a Bool, found `Number`",
            ),
            (
                "true and 1 < 2 and \"x\"",
                "\"x\"",
                "the right side of `and` must be a Bool, found `String`",
            ),
        ];
        for (src, blamed, message) in cases {
            assert_eq!(
                blame(src),
                (blamed.to_string(), message.to_string()),
                "{src}"
            );
        }
    }

    #[test]
    fn loops_are_unit() {
        assert_eq!(type_of("repeat 3 times do print(1) done").unwrap(), "Unit");
        assert_eq!(
            type_of("for i from 1 to 3 do print(i) done").unwrap(),
            "Unit"
        );
        assert_eq!(type_of("for x in [1, 2] do print(x) done").unwrap(), "Unit");
        assert_eq!(type_of("repeat 2 times do done").unwrap(), "Unit");
    }

    #[test]
    fn a_loop_variable_is_scoped_to_the_loop() {
        assert_eq!(
            type_of("for i from 1 to 2 do print(i + 1) done; true").unwrap(),
            "Bool"
        );
        let err = type_of("for i from 1 to 2 do print(i) done; i").unwrap_err();
        assert_eq!(err, "unknown name `i`");
        // The bounds are outside the loop's scope, so they see the outer `i`.
        assert_eq!(
            type_of("i = 3; for i from i to i + 1 do print(i) done").unwrap(),
            "Unit"
        );
    }

    #[test]
    fn a_for_loop_takes_numbers_and_a_list() {
        let err = type_of("for i from 1 to true do print(i) done").unwrap_err();
        assert!(err.starts_with("type mismatch"), "{err}");
        let err = type_of("for x in 5 do print(x) done").unwrap_err();
        assert!(err.starts_with("type mismatch"), "{err}");
        let err = type_of("repeat true times do done").unwrap_err();
        assert!(err.starts_with("type mismatch"), "{err}");
    }

    #[test]
    fn loop_words_are_reserved_but_from_to_and_in_are_not() {
        for word in ["for", "and", "or", "not", "repeat", "times"] {
            assert!(check(&format!("{word} = 1 {word}")).is_err(), "{word}");
        }
        for word in ["from", "to", "in"] {
            let src = format!("{word} = 1 {word}");
            assert_eq!(type_of(&src).unwrap(), "Number", "{word}");
        }
        assert_eq!(
            type_of("line = {from: 1, to: 2} line.to - line.from").unwrap(),
            "Number"
        );
        assert_eq!(
            type_of("to = 3 for from from 1 to to do print(from) done").unwrap(),
            "Unit"
        );
    }
}
