//! The canvas host end to end: its vocabulary checks programs, scripts run
//! under wasmtime and the MIR interpreter to the same picture, and the
//! pictures render to committed golden SVGs. Run with `GOAT_BLESS=1` to
//! rewrite the goldens.

use goat::{SceneCommand, SceneHost};
use goat_canvas::{Canvas, Event, compile, interface, render, to_svg, vocab};
use goat_mir::{Session, Value};
use std::{env, fs};

fn example(file: &str) -> String {
    let path = format!("{}/../examples/canvas/{file}", env!("CARGO_MANIFEST_DIR"));
    fs::read_to_string(path).unwrap()
}

fn assert_golden(name: &str, svg: &str) {
    let path = format!("{}/tests/golden/{name}", env!("CARGO_MANIFEST_DIR"));
    if env::var_os("GOAT_BLESS").is_some() {
        fs::write(&path, svg).unwrap();
    }
    let expected = fs::read_to_string(&path).expect("golden file exists");
    assert_eq!(svg, expected, "{name} differs from its golden");
}

fn frames(count: usize) -> Vec<Event> {
    vec![Event::Frame(16.0); count]
}

fn errors(source: &str) -> String {
    let errors = goat::compile(source, &interface()).expect_err("program is rejected");
    errors
        .iter()
        .map(|e| e.message.as_str())
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn the_vocabulary_is_well_formed() {
    assert_eq!(vocab().validate(), Ok(()));
}

#[test]
fn the_examples_check_against_the_canvas_vocabulary() {
    for file in ["bounce.goat", "catch.goat"] {
        compile(&example(file)).unwrap_or_else(|e| panic!("{file}: {e}"));
    }
}

#[test]
fn the_canvas_speaks_its_own_events_not_the_turtles() {
    let turtle_event = "init = {n: 0}\nupdate = program(m, e) do match e do Tick(dt) then m done done\ndraw = program(m) do [] done";
    assert!(
        errors(turtle_event).contains("Tick"),
        "{}",
        errors(turtle_event)
    );
    let canvas_event = "init = {n: 0}\nupdate = program(m, e) do match e do Frame(dt) then m else m done done\ndraw = program(m) do [] done";
    compile(canvas_event).unwrap();
}

#[test]
fn the_canvas_draws_its_own_shapes_not_the_turtles() {
    let draw = |shape: &str| {
        format!(
            "init = {{n: 0}}\nupdate = program(m, e) do match e do Frame(dt) then m else m done done\ndraw = program(m) do [{shape}] done"
        )
    };
    let turtle_shape = draw("Circle({x: 1, y: 2, r: 3, color: \"red\"})");
    assert!(
        errors(&turtle_shape).contains("Circle"),
        "{}",
        errors(&turtle_shape)
    );
    let renamed_field = draw("Dot({x: 1, y: 2, r: 3, color: \"red\"})");
    assert!(compile(&renamed_field).is_err());
    compile(&draw("Dot({x: 1, y: 2, r: 3, fill: \"red\"})")).unwrap();
}

#[test]
fn a_key_match_without_else_must_name_every_canvas_key() {
    let handle = |arms: &str| {
        format!(
            "init = {{n: 0}}\nupdate = program(m, e) do match e do KeyPress(k) then match k do {arms} done else m done done\ndraw = program(m) do [] done"
        )
    };
    let partial = handle("Left then m Right then m");
    assert!(compile(&partial).is_err());
    let all = handle("Space then m Left then m Right then m Up then m Down then m Char(c) then m");
    compile(&all).unwrap();
}

#[test]
fn a_script_with_no_handled_events_still_draws() {
    let svg = render(&example("bounce.goat"), &[]).unwrap();
    assert!(svg.contains("<circle cx=\"40\" cy=\"30\" r=\"20\" fill=\"tomato\"/>"));
}

#[test]
fn keys_arrive_decoded_and_events_a_script_ignores_are_dropped() {
    let source = "
init = {x: 100, y: 100}
update = program(m, e) do
  match e do
    KeyPress(k) then match k do
      Space then {x: m.x, y: 0}
      Left then {x: m.x - 10, y: m.y}
      Char(c) then {x: 0, y: m.y}
      else m
    done
    else m
  done
done
draw = program(m) do [Dot({x: m.x, y: m.y, r: 1, fill: \"red\"})] done";
    let at = |events: &[Event]| render(source, events).unwrap();
    let dot = |x: &str, y: &str| format!("<circle cx=\"{x}\" cy=\"{y}\" r=\"1\" fill=\"red\"/>");
    let press = |key: &str| Event::KeyPress(key.to_string());
    assert!(at(&[press("ArrowLeft")]).contains(&dot("90", "100")));
    assert!(at(&[press(" ")]).contains(&dot("100", "0")));
    assert!(at(&[press("q")]).contains(&dot("0", "100")));
    assert!(at(&[press("ArrowDown")]).contains(&dot("100", "100")));
    let ignored = [
        Event::KeyRelease("ArrowLeft".into()),
        Event::MouseMove(1.0, 2.0),
    ];
    assert!(at(&ignored).contains(&dot("100", "100")));
}

#[test]
fn text_is_escaped_in_the_svg() {
    let picture = [SceneCommand::Text {
        origin: (1.0, 2.0),
        text: "<b>&\"x\"".into(),
        color: "red".into(),
    }];
    assert!(to_svg(&picture).contains(">&lt;b&gt;&amp;&quot;x&quot;</text>"));
}

#[test]
fn a_bad_color_stops_the_script() {
    let source = "init = {n: 0}\nupdate = program(m, e) do match e do Frame(dt) then m else m done done\ndraw = program(m) do [Dot({x: 1, y: 2, r: 3, fill: \"a b\"})] done";
    let error = render(source, &[]).unwrap_err();
    assert!(error.contains("color wants a name"), "{error}");
}

#[test]
fn a_runaway_script_is_stopped() {
    let source = "init = {n: 0}\nupdate = program(m, e) do match e do Frame(dt) then m else m done done\nspin = program(n) do spin(n + 1) done\ndraw = program(m) do [Dot({x: spin(0), y: 0, r: 1, fill: \"red\"})] done";
    let started = std::time::Instant::now();
    let error = render(source, &[]).unwrap_err();
    assert!(error.contains("stopped"), "{error}");
    assert!(started.elapsed().as_secs() < 30);
}

#[test]
fn event_scripts_parse_and_reject_junk() {
    let parsed = Event::parse_script(
        "# note\nFrame 16\n\nKeyPress ArrowLeft\nKeyPress  \nMousePress 1.5 -2\n",
    );
    assert_eq!(
        parsed.unwrap(),
        [
            Event::Frame(16.0),
            Event::KeyPress("ArrowLeft".into()),
            Event::KeyPress(" ".into()),
            Event::MousePress(1.5, -2.0),
        ]
    );
    for bad in ["Tick 16", "Frame soon", "MouseMove 1", "Frame NaN"] {
        assert!(Event::parse_script(bad).is_err(), "{bad}");
    }
}

/// Steer the basket under each of the first five coins, which fall in
/// columns 100, 170, 240, 310 and 60.
fn winning_game() -> Vec<Event> {
    [100.0, 170.0, 240.0, 310.0, 60.0]
        .into_iter()
        .flat_map(|x| [vec![Event::MouseMove(x, 270.0)], frames(110)].concat())
        .collect()
}

#[test]
fn the_game_can_be_won() {
    let svg = render(&example("catch.goat"), &winning_game()).unwrap();
    assert!(svg.contains("you win!"), "{svg}");
    assert!(
        svg.contains("width=\"100\" height=\"10\" fill=\"green\""),
        "{svg}"
    );
}

#[test]
fn the_pictures_render_to_their_goldens() {
    let events = |file: &str| Event::parse_script(&example(file)).unwrap();
    let bounce = render(&example("bounce.goat"), &events("bounce.events")).unwrap();
    assert_golden("bounce.svg", &bounce);
    let catch = render(&example("catch.goat"), &events("catch.events")).unwrap();
    assert_golden("catch.svg", &catch);
}

/// The picture the MIR interpreter draws for `events`.
fn interpreted(source: &str, events: &[Event]) -> Vec<SceneCommand> {
    let checked = goat_checker::check_with_vocab(interface().prelude(), &vocab(), source).unwrap();
    let program = goat_mir::mono(&checked).unwrap();
    let mut host = SceneHost::default();
    let (mut session, mut model) = Session::setup(&program, &mut host).unwrap();
    for event in events {
        let Event::Frame(dt) = event else {
            panic!("the differential sends frames only")
        };
        let built = session.event("Frame", vec![Value::Float(*dt)]).unwrap();
        model = session.update(model, built).unwrap();
    }
    session.draw(model).unwrap();
    session.release_model(model).unwrap();
    assert_eq!(session.shutdown().unwrap(), 0, "the interpreter leaked");
    host.commands
}

#[test]
fn wasmtime_and_the_interpreter_draw_the_same_picture() {
    let source = example("bounce.goat");
    let events = frames(90);
    let mut canvas = Canvas::new(&compile(&source).unwrap()).unwrap();
    for event in &events {
        canvas.send(event).unwrap();
    }
    assert_eq!(canvas.draw().unwrap(), interpreted(&source, &events));
    assert_eq!(canvas.finish().unwrap(), 0, "wasm leaked");
}
