//! `byte_length` and `byte_at` read inside a string's UTF-8 bytes (ADR 0009).
//! Every program runs on the MIR interpreter and as wasm under wasmtime, on
//! both profiles, and the backends must agree and leave nothing allocated.

use std::fs;

use goat::Profile::{self, Desktop, Embedded};
use goat_mir::interp::{self, InterpError};

#[allow(dead_code)]
mod support;

use support::{compiled_on, interpret_on};

const OUT_OF_RANGE: &str = "this position is outside the string";

fn run_on(profile: Profile, src: &str) -> String {
    let (expected, live) = interpret_on(profile, goat_checker::PRELUDE, src, &mut goat::NoHost);
    assert_eq!(live, 0, "interpreter leaked on {profile:?}: {src}");
    let (printed, wasm_live) = compiled_on(profile, goat_checker::PRELUDE, src);
    assert_eq!(wasm_live, 0, "wasm leaked on {profile:?}: {src}");
    assert_eq!(
        printed, expected,
        "wasm differs from interp on {profile:?}: {src}"
    );
    expected.join("\n")
}

fn run(src: &str) -> String {
    let desktop = run_on(Desktop, src);
    assert_eq!(run_on(Embedded, src), desktop, "profiles differ: {src}");
    desktop
}

fn assert_traps(src: &str, message: &str) {
    for profile in [Desktop, Embedded] {
        let checked = goat_checker::check(src).expect("type-checks");
        let program = goat_mir::mono_for(&checked, profile).expect("monomorphizes");
        assert_eq!(goat_mir::verify(&program), Ok(()), "{src}");
        assert_eq!(
            interp::run(&program),
            Err(InterpError::Trap(message.into())),
            "interpreter on {profile:?}: {src}"
        );
        let (wasm, _) =
            goat::compile_for(profile, src, &goat::HostInterface::turtle()).expect("compiles");
        let error = goat_cli::run(&wasm).err().expect("wasm should trap");
        assert_eq!(
            error,
            format!("trap: {message}"),
            "wasm on {profile:?}: {src}"
        );
    }
}

#[test]
fn byte_length_counts_ascii() {
    assert_eq!(run("print(byte_length(\"hello\"))"), "5");
    assert_eq!(run("print(byte_length(\"a\"))"), "1");
}

#[test]
fn byte_length_counts_bytes_not_characters() {
    assert_eq!(run("print(byte_length(\"é\"))"), "2");
    assert_eq!(run("print(byte_length(\"héllo\"))"), "6");
    assert_eq!(run("print(byte_length(\"日本\"))"), "6");
    assert_eq!(run("print(byte_length(\"🐐\"))"), "4");
}

#[test]
fn the_empty_string_has_no_bytes() {
    assert_eq!(run("print(byte_length(\"\"))"), "0");
    assert_traps("byte_at(\"\", 1)", OUT_OF_RANGE);
}

#[test]
fn byte_at_counts_from_one() {
    assert_eq!(run("print(byte_at(\"abc\", 1))"), "97");
    assert_eq!(run("print(byte_at(\"abc\", 2))"), "98");
    assert_eq!(run("print(byte_at(\"abc\", 3))"), "99");
}

#[test]
fn byte_at_reads_each_byte_of_a_multi_byte_character() {
    assert_eq!(run("print(byte_at(\"é\", 1))"), "195");
    assert_eq!(run("print(byte_at(\"é\", 2))"), "169");
    assert_eq!(run("print(byte_at(\"🐐\", 4))"), "144");
}

#[test]
fn byte_at_outside_the_string_traps() {
    assert_traps("byte_at(\"abc\", 4)", OUT_OF_RANGE);
    assert_traps("byte_at(\"abc\", 0)", OUT_OF_RANGE);
    assert_traps("byte_at(\"abc\", -1)", OUT_OF_RANGE);
    assert_traps("byte_at(\"abc\", 0 - 2147483647 - 1)", OUT_OF_RANGE);
    assert_traps("byte_at(\"é\", 3)", OUT_OF_RANGE);
}

#[test]
fn a_trap_after_output_keeps_the_output() {
    assert_traps("shown = print(1)\nbyte_at(\"x\", 2) + 1", OUT_OF_RANGE);
}

#[test]
fn byte_at_is_only_checked_when_reached() {
    assert_eq!(
        run("print(if 1 > 2 then byte_at(\"\", 1) else 7 done)"),
        "7"
    );
}

#[test]
fn the_functions_work_as_values() {
    assert_eq!(
        run("print(change_each([\"a\", \"hello\", \"\"], byte_length))"),
        "[1, 5, 0]"
    );
    let read = "first_byte = program(s) do byte_at(s, 1) done\n";
    assert_eq!(
        run(&format!(
            "{read}print(change_each([\"a\", \"b\"], first_byte))"
        )),
        "[97, 98]"
    );
    assert_eq!(run("at = byte_at\nprint(at(\"abc\", 2))"), "98");
}

#[test]
fn the_bytes_of_a_string_sum_in_a_loop() {
    let src = "total = program(s, at, sum) do \
                 if at > byte_length(s) then sum else total(s, at + 1, sum + byte_at(s, at)) done \
               done \
               print(total(\"goat\", 1, 0))";
    assert_eq!(run(src), "427");
}

#[test]
fn the_vowels_example_counts_nine() {
    let path = format!("{}/../examples/vowels.goat", env!("CARGO_MANIFEST_DIR"));
    assert_eq!(run(&fs::read_to_string(path).unwrap()), "9");
}

#[test]
fn char_count_counts_code_points() {
    for (text, count) in [
        ("", 0),
        ("hello", 5),
        ("héllo", 5),
        ("日本", 2),
        ("🐐", 1),
        ("👍🏽", 2),
        ("👨‍👩‍👧", 5),
    ] {
        assert_eq!(
            run(&format!("print(char_count(\"{text}\"))")),
            count.to_string(),
            "{text}"
        );
    }
}

#[test]
fn char_at_gives_the_code_point_at_each_position() {
    for (text, chars) in [
        ("abc", &["a", "b", "c"][..]),
        ("héé", &["h", "é", "é"]),
        ("日本", &["日", "本"]),
        ("a🐐b", &["a", "🐐", "b"]),
        ("👍🏽", &["👍", "🏽"]),
        ("👨‍👩‍👧", &["👨", "\u{200d}", "👩", "\u{200d}", "👧"]),
    ] {
        for (at, one) in chars.iter().enumerate() {
            let at = at + 1;
            assert_eq!(
                run(&format!("print(char_at(\"{text}\", {at}))")),
                *one,
                "{text} {at}"
            );
            assert_eq!(
                run(&format!("print(char_at(\"{text}\", {at}) == \"{one}\")")),
                "true",
                "{text} {at}"
            );
        }
    }
}

#[test]
fn a_character_is_a_string_of_its_own() {
    assert_eq!(run("print(byte_length(char_at(\"a日b\", 2)))"), "3");
    assert_eq!(run("print(char_count(char_at(\"a日b\", 2)))"), "1");
    assert_eq!(
        run("print(char_at(\"ab\", 1) == char_at(\"ba\", 2))"),
        "true"
    );
    assert_eq!(
        run("print(char_at(\"ab\", 1) == char_at(\"ab\", 2))"),
        "false"
    );
}

#[test]
fn char_at_outside_the_string_traps() {
    assert_traps("char_at(\"\", 1)", OUT_OF_RANGE);
    assert_traps("char_at(\"日本\", 3)", OUT_OF_RANGE);
    assert_traps("char_at(\"日本\", 0)", OUT_OF_RANGE);
    assert_traps("char_at(\"日本\", -1)", OUT_OF_RANGE);
    assert_traps("char_at(\"abc\", 0 - 2147483647 - 1)", OUT_OF_RANGE);
    assert_traps("char_at(\"abc\", 2147483647)", OUT_OF_RANGE);
}

#[test]
fn many_one_character_strings_are_built_and_freed() {
    let src = "walk = program(s, at, same) do
  if at > char_count(s)
    then same
    else
      more = if char_at(s, at) == \"é\" then same + 1 else same done
      walk(s, at + 1, more)
  done
done
again = program(n, total) do
  if n == 0 then total else again(n - 1, total + walk(\"é日🐐éa\", 1, 0)) done
done
print(again(500, 0))";
    assert_eq!(run(src), "1000");
}

#[test]
fn the_character_functions_work_as_values() {
    assert_eq!(
        run("print(change_each([\"a\", \"日本\", \"\"], char_count))"),
        "[1, 2, 0]"
    );
    assert_eq!(run("at = char_at\nprint(at(\"日本\", 2))"), "本");
}

#[test]
fn the_letters_example_prints_each_character() {
    let path = format!("{}/../examples/letters.goat", env!("CARGO_MANIFEST_DIR"));
    assert_eq!(
        run(&fs::read_to_string(path).unwrap()),
        "g\no\na\nt\n \né\n日\n🐐"
    );
}
