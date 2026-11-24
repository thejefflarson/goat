//! The engine through its public seam: sources go in, messages and frames come
//! out of a sink, as they will for the Swift host.

use goat::HostValue;
use goat_apple::{Budgets, Engine, Pointer, Sink};
use serde_json::{Value, json};
use std::sync::{Arc, Condvar, Mutex, MutexGuard, PoisonError};
use std::time::{Duration, Instant};

#[derive(Clone, Debug)]
enum Heard {
    Control(Value),
    Frame(Vec<u8>),
    Closed,
}

/// A sink that records everything the engine says, and lets a test wait for it.
#[derive(Clone, Default)]
struct Log(Arc<(Mutex<Vec<Heard>>, Condvar)>);

impl Sink for Log {
    fn control(&mut self, json: &str) {
        self.push(Heard::Control(serde_json::from_str(json).expect("JSON")));
    }

    fn frame(&mut self, bytes: &[u8]) {
        self.push(Heard::Frame(bytes.to_vec()));
    }

    fn closed(&mut self) {
        self.push(Heard::Closed);
    }
}

const WAIT: Duration = Duration::from_secs(20);

impl Log {
    /// A test that fails while waiting poisons the lock; the sink still has to
    /// answer when the engine is dropped during the unwind.
    fn lock(&self) -> MutexGuard<'_, Vec<Heard>> {
        self.0.0.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn push(&self, heard: Heard) {
        self.lock().push(heard);
        self.0.1.notify_all();
    }

    fn heard(&self) -> Vec<Heard> {
        self.lock().clone()
    }

    fn clear(&self) {
        self.lock().clear();
    }

    /// The first thing `find` picks out of what has been heard, waiting for it.
    fn wait<T>(&self, mut find: impl FnMut(&Heard) -> Option<T>) -> T {
        let deadline = Instant::now() + WAIT;
        let mut heard = self.lock();
        loop {
            if let Some(found) = heard.iter().find_map(&mut find) {
                return found;
            }
            let left = deadline.saturating_duration_since(Instant::now());
            assert!(!left.is_zero(), "timed out; heard {heard:?}");
            heard = self.0.1.wait_timeout(heard, left).unwrap().0;
        }
    }

    fn control(&self, matching: Value) -> Value {
        self.wait(|heard| match heard {
            Heard::Control(message) if contains(message, &matching) => Some(message.clone()),
            _ => None,
        })
    }

    fn state(&self, state: &str) -> Value {
        self.control(json!({"type": "state", "state": state}))
    }

    /// The first frame whose line ends at `x`.
    fn frame_ending_at(&self, x: f64) -> Vec<u8> {
        self.wait(|heard| match heard {
            Heard::Frame(bytes) if line_ends(bytes) == Some(x) => Some(bytes.clone()),
            _ => None,
        })
    }

    fn wait_for_frames(&self, count: usize) {
        let deadline = Instant::now() + WAIT;
        let mut heard = self.lock();
        while heard
            .iter()
            .filter(|h| matches!(h, Heard::Frame(_)))
            .count()
            < count
        {
            let left = deadline.saturating_duration_since(Instant::now());
            assert!(!left.is_zero(), "timed out waiting for {count} frames");
            heard = self.0.1.wait_timeout(heard, left).unwrap().0;
        }
    }

    fn frame_count(&self) -> usize {
        self.heard()
            .iter()
            .filter(|h| matches!(h, Heard::Frame(_)))
            .count()
    }
}

/// True when every field of `pattern` is in `message`.
fn contains(message: &Value, pattern: &Value) -> bool {
    pattern
        .as_object()
        .unwrap()
        .iter()
        .all(|(key, want)| message.get(key) == Some(want))
}

/// The calls a frame makes, by name.
fn calls(frame: &[u8]) -> Vec<(String, Vec<HostValue>)> {
    let mut seen = Vec::new();
    goat_mir::frame::replay(frame, |name, args| {
        seen.push((name.to_string(), args.to_vec()));
        Ok(())
    })
    .expect("a well-formed frame");
    seen
}

/// Where the frame's first line ends, along x.
fn line_ends(frame: &[u8]) -> Option<f64> {
    calls(frame)
        .into_iter()
        .find_map(|(name, args)| match (name.as_str(), &args[..]) {
            ("line", [_, _, HostValue::Number(x), ..]) => Some(*x),
            _ => None,
        })
}

fn vertices(frame: &[u8]) -> usize {
    calls(frame)
        .iter()
        .filter(|(name, _)| name == "vertex")
        .count()
}

/// Draws a line as long as the model's `n`, which each key press raises by
/// `step`. Only key presses are handled, so the model changes only when a test
/// presses a key. `extra` is a model field that changes the model's layout.
fn presses(step: i32, extra: &str) -> String {
    format!(
        r#"
init = {{n: 0, color: "red"{extra}}}
update = program(model, event) do
  match event do
    KeyDown(key) then {{...model, n: model.n + {step}}}
    else model
  done
done
draw = program(model) do [Line({{x1: 0, y1: 0, x2: model.n, y2: 0, color: model.color}})] done
"#
    )
}

fn press(engine: &Engine, times: usize) {
    for _ in 0..times {
        engine.key("a", true);
    }
}

fn started(source: &str) -> (Engine, Log) {
    let log = Log::default();
    let engine = Engine::new(log.clone());
    engine.run(source);
    (engine, log)
}

fn quick() -> Budgets {
    Budgets {
        frame: Duration::from_millis(300),
        once: Duration::from_secs(5),
        ..Budgets::default()
    }
}

#[test]
fn the_engine_says_ready_and_then_runs_a_program_to_frames() {
    let (engine, log) = started(&presses(1, ""));
    log.control(json!({"type": "ready"}));
    log.state("running");
    log.frame_ending_at(0.0);
    press(&engine, 2);
    log.frame_ending_at(2.0);
}

#[test]
fn the_default_budgets_are_a_second_a_frame_and_ten_for_setup() {
    let budgets = Budgets::default();
    assert_eq!(budgets.frame, Duration::from_secs(1));
    assert_eq!(budgets.once, Duration::from_secs(10));
}

#[test]
fn a_reload_that_keeps_the_model_swaps_the_logic() {
    let (engine, log) = started(&presses(1, ""));
    press(&engine, 3);
    log.frame_ending_at(3.0);

    engine.run(&presses(10, ""));
    log.control(json!({"type": "reloaded", "outcome": "kept"}));
    press(&engine, 1);
    log.frame_ending_at(13.0);
}

#[test]
fn a_reload_that_cannot_keep_the_model_starts_over_and_says_why() {
    let (engine, log) = started(&presses(1, ""));
    press(&engine, 3);
    log.frame_ending_at(3.0);

    let changed = presses(1, "").replace(r#"color: "red""#, "color: 5");
    let changed = changed.replace("color: model.color", r#"color: "red""#);
    engine.run(&changed);
    let reloaded = log.control(json!({"type": "reloaded", "outcome": "reset"}));
    assert_eq!(
        reloaded["reason"],
        json!({"kind": "type_changed", "args": ["color", "String", "Int"]})
    );
    log.clear();
    press(&engine, 1);
    log.frame_ending_at(1.0);
}

#[test]
fn a_program_with_errors_says_where_and_leaves_a_running_one_alone() {
    let (engine, log) = started(&presses(1, ""));
    press(&engine, 1);
    log.frame_ending_at(1.0);

    engine.run("1 + true");
    let message = log.control(json!({"type": "diagnostics"}));
    let first = &message["diagnostics"][0];
    assert_eq!(first["line"], 1);
    assert!(first["column"].as_u64().unwrap() >= 1);
    assert!(!first["message"].as_str().unwrap().is_empty());

    press(&engine, 1);
    log.frame_ending_at(2.0);
    let failed = log
        .heard()
        .iter()
        .any(|h| matches!(h, Heard::Control(m) if m["state"] == "failed"));
    assert!(!failed, "the running program was stopped");
}

#[test]
fn nothing_running_and_a_program_with_errors_is_a_failed_state() {
    let (_engine, log) = started("1 + true");
    log.control(json!({"type": "diagnostics"}));
    let failed = log.state("failed");
    assert!(failed["message"].as_str().unwrap().contains("problems"));
}

#[test]
fn a_call_that_never_returns_is_stopped_within_its_budget() {
    let spinning = presses(1, "").replace(
        "KeyDown(key) then {...model, n: model.n + 1}",
        "KeyDown(key) then {...model, n: spin(0)}",
    ) + "\nspin = program(n) do if n < 0 then n else spin(n + 1) done done\n";
    let log = Log::default();
    let engine = Engine::with_budgets(log.clone(), quick());
    engine.run(&spinning);
    log.frame_ending_at(0.0);

    let started = Instant::now();
    press(&engine, 1);
    let failed = log.state("failed");
    let took = started.elapsed();
    assert!(
        took < quick().frame + Duration::from_millis(100),
        "{took:?}"
    );
    let message = failed["message"].as_str().unwrap();
    assert!(message.contains("looks stuck"), "{message}");
    assert!(!message.contains("goat_update"), "{message}");

    log.clear();
    engine.run(&presses(1, ""));
    log.frame_ending_at(0.0);
    press(&engine, 1);
    log.frame_ending_at(1.0);
}

#[test]
fn a_run_once_program_that_never_ends_is_stopped_within_its_budget() {
    let budgets = Budgets {
        once: Duration::from_millis(300),
        ..Budgets::default()
    };
    let log = Log::default();
    let engine = Engine::with_budgets(log.clone(), budgets);
    log.control(json!({"type": "ready"}));
    let started = Instant::now();
    engine.run("spin = program(n) do if n < 0 then n else spin(n + 1) done done\nspin(0)");
    let failed = log.state("failed");
    assert!(started.elapsed() < budgets.once + Duration::from_millis(100) + COMPILE_SLACK);
    assert!(failed["message"].as_str().unwrap().contains("looks stuck"));
}

/// Compiling the program and the module to Pulley happen inside the budget's
/// window in this test, though the budget itself starts after them.
const COMPILE_SLACK: Duration = Duration::from_secs(2);

#[test]
fn a_goat_trap_stops_the_program_with_its_message() {
    let trapping = presses(1, "").replace(
        "KeyDown(key) then {...model, n: model.n + 1}",
        r#"KeyDown(key) then trap("boom")"#,
    );
    let (engine, log) = started(&trapping);
    log.frame_ending_at(0.0);
    press(&engine, 1);
    let failed = log.state("failed");
    assert_eq!(failed["message"], "your program stopped: boom");

    log.clear();
    engine.run(&presses(1, ""));
    log.frame_ending_at(0.0);
}

#[test]
fn a_run_once_trap_keeps_what_was_printed_and_draws_nothing() {
    let (_engine, log) = started("print(\"before\");\nforward(10);\ntrap(\"nope\")");
    let output = log.control(json!({"type": "output"}));
    assert_eq!(output["lines"], json!(["before"]));
    let failed = log.state("failed");
    assert!(failed["message"].as_str().unwrap().contains("nope"));
    assert_eq!(log.frame_count(), 0);
}

#[test]
fn a_program_that_outgrows_its_heap_is_stopped_with_a_message() {
    let budgets = Budgets {
        heap: 8 << 20,
        ..Budgets::default()
    };
    let log = Log::default();
    let engine = Engine::with_budgets(log.clone(), budgets);
    engine.run("grow = program(n, acc) do grow(n + 1, Link(n, acc)) done\ngrow(0, Empty)");
    let failed = log.state("failed");
    let message = failed["message"].as_str().unwrap();
    assert!(message.contains("more memory"), "{message}");
}

#[test]
fn print_output_reaches_the_host_from_either_kind_of_program() {
    let (_once, log) = started("print(1 + 2)");
    let output = log.control(json!({"type": "output"}));
    assert_eq!(output["lines"], json!(["3"]));

    let chatty = presses(1, "").replace(
        "KeyDown(key) then {...model, n: model.n + 1}",
        "KeyDown(key) then say(model, key)",
    ) + "\nsay = program(model, key) do print(\"hi\"); {...model, n: model.n + 1} done\n";
    let (engine, log) = started(&chatty);
    log.frame_ending_at(0.0);
    engine.key("q", true);
    let output = log.control(json!({"type": "output"}));
    assert_eq!(output["lines"], json!(["hi"]));
}

#[test]
fn a_turtle_program_is_drawn_a_few_segments_at_a_time() {
    let spiral = include_str!("../../../../examples/spiral.goat");
    let (_engine, log) = started(spiral);
    log.state("finished");

    let frames: Vec<usize> = log
        .heard()
        .iter()
        .filter_map(|h| match h {
            Heard::Frame(bytes) => Some(vertices(bytes)),
            _ => None,
        })
        .collect();
    // 60 segments, 4 to a frame, and a frame is dropped only when a newer one
    // is waiting, so a fast sink hears them all.
    assert!(frames.windows(2).all(|w| w[0] <= w[1]), "{frames:?}");
    assert_eq!(frames.last(), Some(&61));
    assert!(frames.len() > 1);
    let last = log
        .heard()
        .into_iter()
        .rev()
        .find_map(|h| match h {
            Heard::Frame(bytes) => Some(bytes),
            _ => None,
        })
        .unwrap();
    for (name, args) in calls(&last) {
        if let ("vertex", [HostValue::Number(x), HostValue::Number(y)]) = (name.as_str(), &args[..])
        {
            assert!(
                (0.0..=400.0).contains(x) && (0.0..=300.0).contains(y),
                "{x},{y}"
            );
        }
    }
    let heard = log.heard();
    let last_frame = heard.iter().rposition(|h| matches!(h, Heard::Frame(_)));
    let finished = heard
        .iter()
        .position(|h| matches!(h, Heard::Control(m) if m["state"] == "finished"));
    assert!(last_frame < finished, "finished before the last frame");
}

#[test]
fn a_canvas_program_gets_the_canvas_events() {
    let source = r#"
init = {x: 0}
update = program(m, e) do
  match e do
    MousePress(p) then {x: p.x}
    else m
  done
done
draw = program(m) do [Segment({x1: 0, y1: 0, x2: m.x, y2: 0, fill: "gray"})] done
"#;
    let (engine, log) = started(source);
    log.frame_ending_at(0.0);
    engine.pointer(Pointer::Down, 42.0, 7.0);
    log.frame_ending_at(42.0);
}

#[test]
fn callbacks_stop_when_the_engine_is_dropped() {
    let busy = r#"
init = {n: 0}
update = program(m, e) do match e do Tick(dt) then {n: m.n + 1} else m done done
draw = program(m) do [Line({x1: 0, y1: 0, x2: m.n, y2: 0, color: "red"})] done
"#;
    let (engine, log) = started(busy);
    log.wait_for_frames(4);
    drop(engine);

    let heard = log.heard();
    assert!(
        matches!(heard.last(), Some(Heard::Closed)),
        "closed is last"
    );
    std::thread::sleep(Duration::from_millis(300));
    assert_eq!(
        log.heard().len(),
        heard.len(),
        "heard something after the engine was dropped"
    );
    let closed = heard.iter().filter(|h| matches!(h, Heard::Closed)).count();
    assert_eq!(closed, 1);
}

#[test]
fn two_engines_run_side_by_side() {
    let (first, one) = started(&presses(1, ""));
    let (second, two) = started(&presses(100, ""));
    press(&first, 2);
    press(&second, 2);
    one.frame_ending_at(2.0);
    two.frame_ending_at(200.0);

    let trapping = presses(1, "").replace(
        "KeyDown(key) then {...model, n: model.n + 1}",
        r#"KeyDown(key) then trap("boom")"#,
    );
    second.run(&trapping);
    two.control(json!({"type": "state", "state": "running"}));
    second.key("a", true);
    two.state("failed");

    press(&first, 1);
    one.frame_ending_at(3.0);
    assert!(
        !one.heard()
            .iter()
            .any(|h| matches!(h, Heard::Control(m) if m["state"] == "failed"))
    );
}
