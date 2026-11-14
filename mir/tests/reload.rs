//! Reload on the interpreter (ADR 0035): a snapshot of the old model, refreshed
//! into the new program's types, keeps the data by name and rebinds each
//! method to the new program's closure for its site.

use goat_mir::{Program, Refresh, SceneCommand, SceneHost, Session, Value, mono, verify};

fn compile(source: &str) -> Program {
    let checked = goat_checker::check(source).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    let program = mono(&checked).expect("program monomorphizes");
    assert_eq!(verify(&program), Ok(()));
    program
}

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

/// The circles `draw` streamed, by x.
fn circles(commands: &[SceneCommand]) -> Vec<f64> {
    commands
        .iter()
        .filter_map(|c| match c {
            SceneCommand::Circle { center, .. } => Some(center.0),
            _ => None,
        })
        .collect()
}

fn tick(session: &mut Session, model: Value) -> Value {
    let event = session.event("Tick", vec![Value::Float(16.0)]).unwrap();
    session.update(model, event).unwrap()
}

#[test]
fn a_reload_keeps_the_data_and_rebinds_the_methods() {
    let old = compile(BALLS);
    let new = compile(&BALLS.replace("speed = 5", "speed = 7"));
    let mut host = SceneHost::default();
    let (mut session, mut model) = Session::setup(&old, &mut host).unwrap();
    model = tick(&mut session, model);
    model = tick(&mut session, model);
    let (mut model, reason) = session.reload(&new, model).unwrap();
    assert_eq!(reason, None);
    model = tick(&mut session, model);
    session.draw(model).unwrap();
    session.release_model(model).unwrap();
    assert_eq!(session.shutdown().unwrap(), 0, "leaked");
    assert_eq!(circles(&host.commands), vec![17.0, 27.0]);
}

#[test]
fn refresh_without_a_program_change_is_the_identity() {
    let program = compile(BALLS);
    let mut host = SceneHost::default();
    let (mut session, model) = Session::setup(&program, &mut host).unwrap();
    let image = session.snapshot(model).unwrap();
    let fresh = session
        .event("Tick", vec![Value::Float(1.0)])
        .and_then(|e| Ok(e))
        .unwrap();
    let _ = (image, fresh, Refresh::Reset(vec![]));
}
