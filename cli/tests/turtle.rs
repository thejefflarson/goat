//! The headless turtle: a program's turtle calls drive the interpreter and
//! wasmtime to the same command log, and that log renders to the committed
//! golden SVG. Run with `GOAT_BLESS=1` to rewrite the goldens.

#[allow(dead_code)]
mod support;

use goat_cli::turtle::{Command, TurtleHost};
use std::{env, fs};
use support::interpret_hosted;

const SQUARE: &str = "\
color(\"red\");
repeat 4 times do forward(100); right(90) done
";

/// Run `src` on the interpreter and on wasm against a fresh `TurtleHost` each,
/// assert the two drew the same thing without leaking, and return the drawing.
fn draw(src: &str) -> TurtleHost {
    let mut oracle = TurtleHost::default();
    let (printed, live) = interpret_hosted(goat_checker::PRELUDE, src, &mut oracle);
    assert_eq!(live, 0, "interpreter leaked allocations for: {src}");
    let wasm = goat::compile_turtle(src).expect("program compiles");
    let (run, compiled) = goat_cli::run_with_host(&wasm, TurtleHost::default()).expect("wasm runs");
    assert_eq!(run.live_allocs, 0, "wasm leaked allocations for: {src}");
    assert_eq!(run.printed, printed, "wasm printed differently: {src}");
    assert_eq!(compiled, oracle, "turtle commands differ for: {src}");
    assert_eq!(compiled.to_svg(), oracle.to_svg());
    oracle
}

fn assert_golden(name: &str, svg: &str) {
    let path = format!("{}/tests/golden/{name}", env!("CARGO_MANIFEST_DIR"));
    if env::var_os("GOAT_BLESS").is_some() {
        fs::write(&path, svg).unwrap();
    }
    let expected = fs::read_to_string(&path).expect("golden file exists");
    assert_eq!(svg, expected, "{name} differs from its golden");
}

fn example(file: &str) -> String {
    let path = format!("{}/../examples/{file}", env!("CARGO_MANIFEST_DIR"));
    fs::read_to_string(path).unwrap()
}

#[test]
fn a_square_has_the_same_commands_on_both_backends() {
    let turtle = draw(SQUARE);
    let mut expected = vec![Command::Color("red".into())];
    for _ in 0..4 {
        expected.extend([Command::Forward(100.0), Command::Right(90.0)]);
    }
    assert_eq!(turtle.commands, expected);
}

#[test]
fn a_square_renders_to_its_golden() {
    assert_golden("square.svg", &draw(SQUARE).to_svg());
}

#[test]
fn the_spiral_example_renders_to_its_golden() {
    assert_golden("spiral.svg", &draw(&example("spiral.goat")).to_svg());
}

#[test]
fn every_command_reaches_the_host_in_order() {
    let src = "color(\"#ff8800\"); forward(1); back(2); left(3); right(4); pen_up(); \
               pen_down(); pen_up()";
    assert_eq!(
        draw(src).commands,
        [
            Command::Color("#ff8800".into()),
            Command::Forward(1.0),
            Command::Back(2.0),
            Command::Left(3.0),
            Command::Right(4.0),
            Command::PenUp,
            Command::PenDown,
            Command::PenUp,
        ]
    );
}

#[test]
fn turtle_commands_are_values_and_work_inside_functions() {
    let src = "side = program(n) do forward(n); left(120) done\n\
               step = left\nrepeat 3 times do side(10) done;\nstep(5)";
    let turtle = draw(src);
    assert_eq!(turtle.commands.len(), 7);
    assert_eq!(turtle.commands[6], Command::Left(5.0));
}

#[test]
fn printing_works_alongside_the_turtle() {
    let (printed, _) = interpret_hosted(
        goat_checker::PRELUDE,
        "print(1); forward(2); print(3)",
        &mut TurtleHost::default(),
    );
    assert_eq!(printed, ["1", "3"]);
}

#[test]
fn a_bad_color_stops_the_program() {
    let wasm = goat::compile_turtle("color(\"not a color\")").expect("compiles");
    let err = goat_cli::run_with_host(&wasm, TurtleHost::default()).err();
    assert!(err.expect("traps").contains("color wants a name"));
}
