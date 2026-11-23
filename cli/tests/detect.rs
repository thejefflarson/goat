//! The vocabulary a program is written in is read from the names it uses.

use goat_cli::detect::detect;
use goat_cli::native_build::Vocabulary;
use std::fs;
use std::path::Path;
use std::process::{Command, Output};

fn goat(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_goat"))
        .args(args)
        .output()
        .expect("run goat")
}

fn example(name: &str) -> String {
    fs::read_to_string(Path::new("../examples").join(name)).unwrap()
}

const BOTH: &str =
    "forward(10)\nupdate = program(m, e) do match e do Frame(d) then m else m done done\n";

fn run_file(name: &str, source: &str, flags: &[&str]) -> Output {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join(name);
    fs::write(&path, source).unwrap();
    goat(&[&["run", path.to_str().unwrap()], flags].concat())
}

#[test]
fn the_canvas_examples_are_canvas_programs() {
    for name in ["bounce", "catch", "sky"] {
        let source = example(&format!("canvas/{name}.goat"));
        assert_eq!(detect(&source), Ok(Vocabulary::Canvas), "{name}");
    }
}

#[test]
fn turtle_events_and_calls_make_a_turtle_program() {
    assert_eq!(detect(&example("interactive.goat")), Ok(Vocabulary::Turtle));
    assert_eq!(detect(&example("spiral.goat")), Ok(Vocabulary::Turtle));
}

#[test]
fn a_program_naming_neither_vocabulary_is_a_turtle_program() {
    assert_eq!(detect("print(1 + 2)\n"), Ok(Vocabulary::Turtle));
}

#[test]
fn names_in_strings_and_comments_and_a_programs_own_bindings_do_not_count() {
    let source = "# Frame\nforward = program(n) do n done\nprint(\"Frame\")\nforward(1)\n";
    assert_eq!(detect(source), Ok(Vocabulary::Turtle));
    let own_tag = "tag Shape = Frame | Dot\nprint(1)\n";
    assert_eq!(detect(own_tag), Ok(Vocabulary::Turtle));
}

#[test]
fn a_program_naming_both_is_an_error_at_the_first_name_of_each() {
    let source = "forward(10)\nupdate = program(m, e) do match e do Tick(d) then m Frame(d) then m else m done done\n";
    let error = detect(source).unwrap_err();
    assert_eq!(&source[error.span.start..error.span.end], "forward");
    assert!(
        error.message.contains("`forward`, `Tick`"),
        "{}",
        error.message
    );
    assert!(error.message.contains("`Frame`"), "{}", error.message);
    assert!(error.message.contains("--turtle or --canvas"));
    let label = &error.labels[0];
    assert_eq!(&source[label.span.start..label.span.end], "Frame");
}

#[test]
fn goat_run_draws_a_canvas_program_without_a_flag() {
    let dir = tempfile::tempdir().unwrap();
    let svg = dir.path().join("sky.svg");
    let out = goat(&[
        "run",
        "../examples/canvas/sky.goat",
        "-o",
        svg.to_str().unwrap(),
    ]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout), "ran 60 frames\n");
    let svg = fs::read_to_string(svg).unwrap();
    assert!(
        svg.contains("<circle") && svg.contains("fill=\"gold\""),
        "{svg}"
    );
}

#[test]
fn goat_run_reports_the_ambiguity_with_spans() {
    let out = run_file("both.goat", BOTH, &[]);
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("1:1:") && stderr.contains("`forward`"),
        "{stderr}"
    );
    assert!(
        stderr.contains("2:") && stderr.contains("`Frame`"),
        "{stderr}"
    );
    assert!(stderr.contains("--turtle or --canvas"), "{stderr}");
}

#[test]
fn the_flags_override_the_detection() {
    let canvas = example("canvas/sky.goat");
    let forced = run_file("sky.goat", &canvas, &["--turtle"]);
    assert!(!forced.status.success());
    let stderr = String::from_utf8_lossy(&forced.stderr);
    assert!(stderr.contains("error(s)"), "{stderr}");

    let both = run_file("both.goat", BOTH, &["--turtle"]);
    assert!(!String::from_utf8_lossy(&both.stderr).contains("--turtle or --canvas"));
}

#[test]
fn asking_for_both_flags_is_an_error() {
    let out = run_file("p.goat", "print(1)\n", &["--turtle", "--canvas"]);
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("conflict"));
}
