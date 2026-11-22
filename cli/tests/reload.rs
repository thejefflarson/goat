//! Reload (ADR 0035): the old module snapshots the model, the new one refreshes
//! a model of its own types from the image and rebinds each method to its own
//! closure for the method's site. Every scenario runs on the MIR interpreter
//! and on wasm; the two must stream the same pictures and give the same reason
//! for every reset, and leave nothing allocated.

use goat::native::{Event, Interactive, Reloaded};
use goat::{HostInterface, SceneCommand, SceneHost};
use goat_mir::{Program, Session, Value};
use std::time::Instant;

#[derive(Clone, Copy)]
enum Step {
    Ticks(usize),
    Draw,
    /// Reload into the source at this index.
    Reload(usize),
}

use Step::*;

#[derive(Debug, PartialEq, Default)]
struct Trace {
    scene: Vec<SceneCommand>,
    /// One per reload: `None` for a refresh, else the reason's parts.
    outcomes: Vec<Option<Vec<String>>>,
}

fn compile(source: &str) -> Program {
    let checked = goat_checker::check(source).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    let program = goat_mir::mono(&checked).expect("program monomorphizes");
    assert_eq!(goat_mir::verify(&program), Ok(()));
    program
}

fn reloadable(source: &str) -> Vec<u8> {
    goat::compile_reloadable(source, &HostInterface::turtle())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
}

fn interpreted(sources: &[&str], steps: &[Step]) -> Trace {
    let programs: Vec<Program> = sources.iter().map(|s| compile(s)).collect();
    let mut host = SceneHost::default();
    let mut outcomes = Vec::new();
    let (mut session, mut model) = Session::setup(&programs[0], &mut host).expect("setup runs");
    for step in steps {
        match *step {
            Ticks(n) => {
                for _ in 0..n {
                    let event = session.event("Tick", vec![Value::Float(16.0)]).unwrap();
                    model = session.update(model, event).expect("update runs");
                }
            }
            Draw => session.draw(model).expect("draw runs"),
            Reload(i) => {
                let (next, reason) = session.reload(&programs[i], model).expect("reload runs");
                model = next;
                outcomes.push(reason);
            }
        }
    }
    session.release_model(model).unwrap();
    assert_eq!(session.shutdown().unwrap(), 0, "the interpreter leaked");
    Trace {
        scene: host.commands,
        outcomes,
    }
}

fn compiled(sources: &[&str], steps: &[Step]) -> Trace {
    let modules: Vec<Vec<u8>> = sources.iter().map(|s| reloadable(s)).collect();
    let mut program: Interactive<SceneHost> =
        Interactive::new(&modules[0], SceneHost::default()).expect("starts");
    let mut outcomes = Vec::new();
    for step in steps {
        match *step {
            Ticks(n) => {
                for _ in 0..n {
                    assert!(program.send(&Event::Tick(16.0)).unwrap());
                }
            }
            Draw => program.draw().expect("draw runs"),
            Reload(i) => outcomes.push(match program.reload(&modules[i]).expect("reload runs") {
                Reloaded::Refreshed => None,
                Reloaded::Reset(reason) => Some(
                    std::iter::once(reason.kind)
                        .chain(reason.args)
                        .collect::<Vec<_>>(),
                ),
            }),
        }
    }
    let (sink, live) = program.finish().expect("tears down");
    assert_eq!(live, 0, "wasm leaked");
    Trace {
        scene: sink.commands,
        outcomes,
    }
}

/// Run the scenario on both backends, require them to agree, and return what
/// they did.
fn agree(sources: &[&str], steps: &[Step]) -> Trace {
    let interp = interpreted(sources, steps);
    let wasm = compiled(sources, steps);
    assert_eq!(wasm, interp, "the interpreter and wasm disagree");
    interp
}

fn circles(trace: &Trace) -> Vec<f64> {
    trace
        .scene
        .iter()
        .filter_map(|c| match c {
            SceneCommand::Circle { center, .. } => Some(center.0),
            _ => None,
        })
        .collect()
}

fn texts(trace: &Trace) -> Vec<String> {
    trace
        .scene
        .iter()
        .filter_map(|c| match c {
            SceneCommand::Text { text, .. } => Some(text.clone()),
            _ => None,
        })
        .collect()
}

fn reason(kind: &str, args: &[&str]) -> Option<Vec<String>> {
    Some(
        std::iter::once(kind)
            .chain(args.iter().copied())
            .map(String::from)
            .collect(),
    )
}

/// A list of balls, each with two methods that use a top-level value.
const BALLS: &str = r#"
speed = 5
make_ball = program(x) do
  {
    x: x,
    update: program(self) do {...self, x: self.x + speed} done,
    draw: program(self) do Circle({x: self.x, y: 10, r: 3, color: "red"}) done
  }
done
init = {tick: 0, name: "ok", balls: [make_ball(0), make_ball(10)]}
update = program(model, event) do
  match event do
    Tick(dt) then {...model, tick: model.tick + 1, balls: change_each(model.balls, program(b) do b.update() done)}
  done
done
draw = program(model) do change_each(model.balls, program(b) do b.draw() done) done
"#;

#[test]
fn a_reload_keeps_the_data_and_rebinds_each_method_to_the_new_program() {
    let faster = BALLS.replace("speed = 5", "speed = 7");
    let trace = agree(&[BALLS, &faster], &[Ticks(2), Reload(1), Ticks(1), Draw]);
    assert_eq!(trace.outcomes, [None]);
    assert_eq!(circles(&trace), [17.0, 27.0]);
}

#[test]
fn a_reload_keeps_what_it_can_when_a_method_body_changes() {
    let bigger = BALLS.replace("y: 10", "y: 20");
    let trace = agree(&[BALLS, &bigger], &[Ticks(1), Reload(1), Draw]);
    assert_eq!(trace.outcomes, [None]);
    assert_eq!(circles(&trace), [5.0, 15.0]);
    let at = |c: &SceneCommand| {
        matches!(
            c,
            SceneCommand::Circle {
                center: (_, 20.0),
                ..
            }
        )
    };
    assert!(trace.scene.iter().any(at), "the new draw ran");
}

/// A model that is not all numbers: a string built at run time, a string
/// literal, a variant with and without a payload, and a list of records.
const MIXED: &str = r##"
tag Run tag Idle
init = {
  built: char_at("hello", 2),
  literal: "lit",
  mode: Run(3),
  idle: Idle,
  dots: [{x: 1, y: 2}, {x: 3, y: 4}],
  flag: true,
  count: 7
}
update = program(model, event) do
  match event do Tick(dt) then {...model, count: model.count + 1} done
done
draw = program(model) do
  [
    Text({x: 0, y: 0, text: model.built, color: "black"}),
    Text({x: 0, y: 0, text: model.literal, color: "black"}),
    Text({x: 0, y: 0, text: match model.mode do Run(n) then "run" Idle then "idle" done, color: "black"}),
    Text({x: 0, y: 0, text: if model.flag then "yes" else "no" done, color: "black"}),
    Polyline({points: model.dots, color: "red"}),
    Circle({x: model.count, y: 0, r: 1, color: "red"})
  ]
done
"##;

#[test]
fn strings_variants_lists_and_scalars_all_cross_a_reload() {
    let other = MIXED.replace("count: 7", "count: 70");
    let trace = agree(&[MIXED, &other], &[Ticks(2), Reload(1), Ticks(1), Draw]);
    assert_eq!(trace.outcomes, [None]);
    assert_eq!(texts(&trace), ["e", "lit", "run", "yes"]);
    assert_eq!(circles(&trace), [10.0]);
    let vertices = trace
        .scene
        .iter()
        .filter(|c| matches!(c, SceneCommand::Vertex(..)))
        .count();
    assert_eq!(vertices, 2);
}

#[test]
fn a_field_the_new_program_adds_comes_from_its_init_and_one_it_drops_goes() {
    let added = MIXED.replace("count: 7", "count: 7, extra: 99");
    let trace = agree(&[MIXED, &added], &[Ticks(1), Reload(1), Draw]);
    assert_eq!(trace.outcomes, [None]);
    let dropped = MIXED
        .replace("  flag: true,\n", "")
        .replace("if model.flag then \"yes\" else \"no\" done", "\"yes\"");
    let trace = agree(&[MIXED, &dropped], &[Ticks(1), Reload(1), Draw]);
    assert_eq!(trace.outcomes, [None]);
    assert_eq!(circles(&trace), [8.0]);
}

#[test]
fn a_field_that_changes_type_resets_and_names_both_types() {
    let changed = MIXED
        .replace("count: 7", "count: \"seven\"")
        .replace("x: model.count", "x: 5")
        .replace("count: model.count + 1", "count: model.count");
    let trace = agree(&[MIXED, &changed], &[Ticks(1), Reload(1), Draw]);
    assert_eq!(
        trace.outcomes,
        [reason("type_changed", &["count", "Number", "String"])]
    );
}

#[test]
fn an_element_a_list_gains_a_field_for_has_no_fresh_value_to_take() {
    let source = r#"
init = {dots: [{a: 1}, {a: 2}], n: 0}
update = program(model, event) do match event do Tick(dt) then model done done
draw = program(model) do [Circle({x: model.n, y: 0, r: 1, color: "red"})] done
"#;
    let spun = source.replace("{a: 1}, {a: 2}", "{a: 1, spin: 0}, {a: 2, spin: 0}");
    let trace = agree(&[source, &spun], &[Reload(1), Draw]);
    assert_eq!(trace.outcomes, [reason("field_added", &["spin"])]);
}

#[test]
fn a_tag_the_new_type_lacks_resets_as_reshaped() {
    let new = MIXED
        .replace("tag Run", "tag Walk")
        .replace("Run(3)", "Walk(3)")
        .replace("Run(n) then \"run\"", "Walk(n) then \"run\"");
    let trace = agree(&[MIXED, &new], &[Reload(1), Draw]);
    assert_eq!(trace.outcomes, [reason("reshaped", &[])]);
}

#[test]
fn a_method_whose_closure_captures_a_local_resets_and_names_it() {
    let source = r#"
make_ball = program(k) do
  {x: 0, update: program(self) do {...self, x: self.x + k} done}
done
init = {ball: make_ball(2)}
update = program(model, event) do
  match event do Tick(dt) then {...model, ball: model.ball.update()} done
done
draw = program(model) do [Circle({x: model.ball.x, y: 0, r: 1, color: "red"})] done
"#;
    let trace = agree(&[source, source], &[Ticks(2), Reload(1), Draw]);
    assert_eq!(
        trace.outcomes,
        [reason("method_captures", &["update", "k"])]
    );
    assert_eq!(circles(&trace), [0.0], "the model started over");
}

#[test]
fn two_literals_with_one_site_key_reset_as_ambiguous() {
    let source = r#"
make = program(up) do
  if up then {x: 0, update: program(self) do {...self, x: self.x + 1} done}
  else {x: 0, update: program(self) do {...self, x: self.x - 1} done} done
done
init = {ball: make(true)}
update = program(model, event) do
  match event do Tick(dt) then {...model, ball: model.ball.update()} done
done
draw = program(model) do [Circle({x: model.ball.x, y: 0, r: 1, color: "red"})] done
"#;
    let trace = agree(&[source, source], &[Ticks(3), Reload(1), Draw]);
    assert_eq!(trace.outcomes, [reason("ambiguous_site", &["update"])]);
}

#[test]
fn renaming_the_binding_that_made_a_method_resets_and_names_the_binding_that_is_gone() {
    let renamed = BALLS.replace("make_ball", "new_ball");
    let trace = agree(&[BALLS, &renamed], &[Ticks(1), Reload(1), Draw]);
    assert_eq!(trace.outcomes, [reason("binding_gone", &["make_ball"])]);
    assert_eq!(circles(&trace), [0.0, 10.0], "the model started over");
}

#[test]
fn a_method_the_new_type_lacks_or_gains_resets() {
    let without = BALLS.replace(
        "    update: program(self) do {...self, x: self.x + speed} done,\n",
        "",
    );
    let without = without.replace(
        "balls: change_each(model.balls, program(b) do b.update() done)",
        "balls: model.balls",
    );
    let trace = agree(&[BALLS, &without], &[Reload(1), Draw]);
    assert_eq!(trace.outcomes, [reason("method_lost", &["update"])]);
    let trace = agree(&[&without, BALLS], &[Reload(1), Draw]);
    assert_eq!(trace.outcomes, [reason("method_added", &["update"])]);
}

#[test]
fn a_method_literal_in_a_polymorphic_function_rebinds_at_each_type() {
    let source = r#"
make = program(v) do {value: v, get: program(self) do self.value done} done
init = {num: make(4), text: make("hi"), n: 0}
update = program(model, event) do
  match event do Tick(dt) then {...model, n: model.n + 1} done
done
draw = program(model) do
  [Circle({x: model.num.get() + model.n, y: 0, r: 1, color: "red"}),
   Text({x: 0, y: 0, text: model.text.get(), color: "black"})]
done
"#;
    let edited = source.replace("y: 0, r: 1", "y: 1, r: 1");
    let trace = agree(&[source, &edited], &[Ticks(2), Reload(1), Draw]);
    assert_eq!(trace.outcomes, [None]);
    assert_eq!(circles(&trace), [6.0]);
    assert_eq!(texts(&trace), ["hi"]);
}

#[test]
fn a_method_inherited_by_a_spread_keeps_the_site_of_the_literal_that_wrote_it() {
    let source = r#"
ball = {x: 1, moved: program(self) do {...self, x: self.x + 10} done}
big = {...ball, size: 5}
init = {thing: big.moved()}
update = program(model, event) do
  match event do Tick(dt) then {...model, thing: model.thing.moved()} done
done
draw = program(model) do [Circle({x: model.thing.x, y: 0, r: model.thing.size, color: "red"})] done
"#;
    let edited = source.replace("x + 10", "x + 100");
    let trace = agree(&[source, &edited], &[Ticks(1), Reload(1), Ticks(1), Draw]);
    assert_eq!(trace.outcomes, [None]);
    assert_eq!(circles(&trace), [121.0]);
}

#[test]
fn a_reload_of_a_model_with_no_balls_works_too() {
    let counter = r#"
init = {n: 0}
update = program(model, event) do match event do Tick(dt) then {n: model.n + 1} done done
draw = program(model) do [Circle({x: model.n, y: 0, r: 1, color: "red"})] done
"#;
    let trace = agree(&[counter, counter], &[Ticks(3), Reload(1), Ticks(1), Draw]);
    assert_eq!(circles(&trace), [4.0]);
}

/// One record in two places: the image writes it once and the refreshed model
/// rebuilds it once.
const SHARED: &str = r#"
palette = {r: 1, g: 2, b: 3}
init = {a: palette, b: palette, n: 0}
update = program(model, event) do match event do Tick(dt) then {...model, n: model.n + 1} done done
draw = program(model) do [Circle({x: model.a.r + model.b.g + model.n, y: 0, r: 1, color: "red"})] done
"#;

const APART: &str = r#"
init = {a: {r: 1, g: 2, b: 3}, b: {r: 1, g: 2, b: 3}, n: 0}
update = program(model, event) do match event do Tick(dt) then {...model, n: model.n + 1} done done
draw = program(model) do [Circle({x: model.a.r + model.b.g + model.n, y: 0, r: 1, color: "red"})] done
"#;

#[test]
fn a_record_held_in_two_places_is_rebuilt_once() {
    let trace = agree(&[SHARED, SHARED], &[Ticks(1), Reload(1), Draw]);
    assert_eq!(circles(&trace), [4.0]);

    let program = compile(SHARED);
    let mut host = SceneHost::default();
    let (mut session, model) = Session::setup(&program, &mut host).unwrap();
    let before = session.fields(model).unwrap();
    assert_eq!(before[0], before[1], "setup shares the record");
    let (model, reason) = session.reload(&program, model).unwrap();
    assert_eq!(reason, None);
    let after = session.fields(model).unwrap();
    assert_eq!(after[0], after[1], "the refreshed model shares it too");

    let live = |source: &str| {
        let mut program: Interactive<SceneHost> =
            Interactive::new(&reloadable(source), SceneHost::default()).unwrap();
        let before = program.live_allocs().unwrap();
        program.reload(&reloadable(source)).unwrap();
        let after = program.live_allocs().unwrap();
        program.finish().unwrap();
        (before, after)
    };
    let (shared, apart) = (live(SHARED), live(APART));
    assert_eq!(
        apart.0 - shared.0,
        1,
        "setup builds the record twice when apart"
    );
    assert_eq!(
        apart.1 - shared.1,
        1,
        "a reload keeps one copy where there was one"
    );
}

fn many_balls(count: usize) -> String {
    format!(
        r##"
palette = {{fill: "red"}}
speed = 1
make_ball = program(x) do
  {{
    x: x,
    y: 0,
    color: palette,
    update: program(self) do {{...self, x: self.x + speed}} done,
    draw: program(self) do Line({{x1: self.x, y1: 0, x2: self.x, y2: 1, color: self.color.fill}}) done
  }}
done
build = program(n, acc) do
  if n == 0 then acc else build(n - 1, Link(make_ball(n), acc)) done
done
init = {{balls: build({count}, []), tick: 0}}
update = program(model, event) do
  match event do
    Tick(dt) then {{...model, tick: model.tick + 1, balls: change_each(model.balls, program(b) do b.update() done)}}
  done
done
draw = program(model) do change_each(model.balls, program(b) do b.draw() done) done
"##
    )
}

fn first_line_x(trace: &Trace) -> f64 {
    trace
        .scene
        .iter()
        .find_map(|c| match c {
            SceneCommand::Line { from, .. } => Some(from.0),
            _ => None,
        })
        .expect("a line was drawn")
}

#[test]
fn the_interpreter_and_wasm_agree_across_a_reload_of_hundreds_of_balls() {
    let old = many_balls(300);
    let new = old.replace("speed = 1", "speed = 10");
    let trace = agree(&[&old, &new], &[Ticks(1), Reload(1), Ticks(1), Draw]);
    assert_eq!(trace.outcomes, [None]);
    assert_eq!(
        trace
            .scene
            .iter()
            .filter(|c| matches!(c, SceneCommand::Line { .. }))
            .count(),
        300
    );
    assert_eq!(first_line_x(&trace), 12.0);
}

#[test]
fn ten_thousand_balls_reload_in_well_under_a_frame_and_every_method_is_rebound() {
    let old = many_balls(10_000);
    let new = old.replace("speed = 1", "speed = 10");
    let (old, new) = (reloadable(&old), reloadable(&new));
    let mut program: Interactive<SceneHost> =
        Interactive::new(&old, SceneHost::default()).expect("starts");
    assert!(program.send(&Event::Tick(16.0)).unwrap());
    let heap_before = program.heap_end().unwrap();
    let started = Instant::now();
    let reloaded = program.reload(&new).expect("reloads");
    let took = started.elapsed();
    assert_eq!(reloaded, Reloaded::Refreshed);
    let carried = program.carry_time();
    eprintln!(
        "10,000-ball reload: snapshot and refresh {carried:?}, whole reload {took:?}; heap {heap_before} -> {} bytes; {} live blocks",
        program.heap_end().unwrap(),
        program.live_allocs().unwrap()
    );
    assert!(
        carried.as_millis() < 1000,
        "snapshot and refresh took {carried:?}, over the 1000 ms frame budget"
    );
    assert!(program.send(&Event::Tick(16.0)).unwrap());
    program.draw().unwrap();
    let (sink, live) = program.finish().unwrap();
    assert_eq!(live, 0, "leaked");
    let lines: Vec<f64> = sink
        .commands
        .iter()
        .filter_map(|c| match c {
            SceneCommand::Line { from, .. } => Some(from.0),
            _ => None,
        })
        .collect();
    assert_eq!(lines.len(), 10_000);
    // Ball n started at x = n, moved once by the old speed (1) and once by the new (10).
    assert_eq!(lines[0], 1.0 + 1.0 + 10.0);
    assert_eq!(lines[9_999], 10_000.0 + 1.0 + 10.0);
}

#[test]
fn repeated_reloads_return_the_live_count_and_the_heap_high_water_mark_to_where_they_began() {
    let source = many_balls(200);
    let edits: Vec<Vec<u8>> = (1..=8)
        .map(|round| reloadable(&source.replace("speed = 1", &format!("speed = {round}"))))
        .collect();
    let mut program: Interactive<SceneHost> =
        Interactive::new(&reloadable(&source), SceneHost::default()).expect("starts");
    let mut marks = Vec::new();
    for module in &edits {
        assert!(program.send(&Event::Tick(16.0)).unwrap());
        assert_eq!(program.reload(module).unwrap(), Reloaded::Refreshed);
        marks.push((program.live_allocs().unwrap(), program.heap_end().unwrap()));
    }
    let (live, heap) = marks[1];
    for (round, mark) in marks.iter().enumerate().skip(1) {
        assert_eq!(*mark, (live, heap), "round {round}: {marks:?}");
    }
    program.finish().unwrap();
}

#[test]
fn a_reset_also_frees_the_old_modules_static_data() {
    let source = BALLS;
    let reset: Vec<Vec<u8>> = (1..=6)
        .map(|round| reloadable(&BALLS.replace("make_ball", &format!("make_{round}"))))
        .collect();
    let mut program: Interactive<SceneHost> =
        Interactive::new(&reloadable(source), SceneHost::default()).expect("starts");
    let mut marks = Vec::new();
    for module in &reset {
        assert!(matches!(
            program.reload(module).unwrap(),
            Reloaded::Reset(_)
        ));
        marks.push((program.live_allocs().unwrap(), program.heap_end().unwrap()));
    }
    for (round, mark) in marks.iter().enumerate().skip(2) {
        assert_eq!(*mark, marks[1], "round {round}: {marks:?}");
    }
    program.finish().unwrap();
}
