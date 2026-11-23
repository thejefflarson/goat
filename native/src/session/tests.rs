use super::*;
use crate::driver::{Library, clang_available};
use crate::interactive::subscriptions;
use goat::Profile;
use goat_mir::frame;
use std::ffi::CString;
use std::sync::Mutex;
use std::sync::mpsc;

const BOUNCE: &str = include_str!("../../../examples/canvas/bounce.goat");
const CATCH: &str = include_str!("../../../examples/canvas/catch.goat");

/// A program that traps on the first frame event.
const TRAPS: &str = r#"
init = {n: 0}
update = program(model, event) do
  match event do
    Frame(dt) then {n: 5 // 0}
    else model
  done
done
draw = program(model) do [Dot({x: 10, y: 10, r: 5, fill: "red"})] done
"#;

/// A program whose `update` never returns once a key is pressed.
const SPINS: &str = r#"
init = {n: 0}
spin = program(n, model) do if n < 0 then model else spin(n + 1, model) done done
update = program(model, event) do
  match event do
    KeyPress(key) then spin(0, model)
    else model
  done
done
draw = program(model) do [Dot({x: 10, y: 10, r: 5, fill: "red"})] done
"#;

enum Seen {
    Frame(Vec<u8>),
    Stopped(Stop, String),
}

struct Channel(Mutex<mpsc::Sender<Seen>>);

impl Output for Channel {
    fn frame(&self, bytes: &[u8]) {
        let _ = self.0.lock().unwrap().send(Seen::Frame(bytes.to_vec()));
    }

    fn stopped(&self, reason: Stop, message: &str) {
        let _ = self
            .0
            .lock()
            .unwrap()
            .send(Seen::Stopped(reason, message.to_string()));
    }
}

/// The program's exports as a window host's entry code passes them. The library
/// and the tables stay loaded for the rest of the process, since a stopped
/// worker never returns from them.
fn program_of(source: &str) -> GoatProgram {
    let ll = goat::compile_ll(Profile::Desktop, source, &goat_canvas::interface())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    let library: &'static Library = Box::leak(Box::new(Library::build(&ll).unwrap()));
    let events: Vec<GoatEvent> = subscriptions(library)
        .into_iter()
        .map(|label| GoatEvent {
            constructor: library
                .symbol::<*const c_void>(&format!("goat_event_{label}"))
                .unwrap(),
            label: CString::new(label).unwrap().into_raw(),
        })
        .collect();
    let events = Box::leak(events.into_boxed_slice());
    GoatProgram {
        attach: library.symbol("goat_attach").unwrap(),
        setup: library.symbol("goat_setup").unwrap(),
        update: library.symbol("goat_update").unwrap(),
        draw: library.symbol("goat_draw").unwrap(),
        alloc: library.symbol("goat_alloc").unwrap(),
        events: events.as_ptr(),
        event_count: events.len() as u64,
    }
}

fn start(source: &str, limits: Limits) -> (Session, mpsc::Receiver<Seen>) {
    let (sender, seen) = mpsc::channel();
    let output = Arc::new(Channel(Mutex::new(sender)));
    let session = Session::start(program_of(source), source.to_string(), output, limits).unwrap();
    (session, seen)
}

fn next(seen: &mpsc::Receiver<Seen>) -> Seen {
    seen.recv_timeout(Duration::from_secs(20))
        .expect("the session says something")
}

type Picture = Vec<(String, Vec<HostValue>)>;

fn next_picture(seen: &mpsc::Receiver<Seen>) -> Picture {
    match next(seen) {
        Seen::Frame(bytes) => {
            let mut calls = Vec::new();
            frame::replay(&bytes, |name, args| {
                calls.push((name.to_string(), args.to_vec()));
                Ok(())
            })
            .unwrap();
            calls
        }
        Seen::Stopped(_, message) => panic!("the program stopped: {message}"),
    }
}

/// The first argument of the first call named `name` in a picture.
fn x_of(picture: &Picture, name: &str) -> f64 {
    let (_, args) = picture.iter().find(|(n, _)| n == name).expect(name);
    match args[0] {
        HostValue::Number(x) => x,
        ref other => panic!("not a number: {other:?}"),
    }
}

macro_rules! need_clang {
    () => {
        if !clang_available() {
            eprintln!("skipping: clang is not available");
            return;
        }
    };
}

#[test]
fn frame_events_animate_the_picture() {
    need_clang!();
    let (_session, seen) = start(BOUNCE, Limits::default());
    let first = x_of(&next_picture(&seen), "circle");
    assert_eq!(first, 40.0);
    let mut later = first;
    for _ in 0..10 {
        later = x_of(&next_picture(&seen), "circle");
    }
    assert!(later > first, "the ball moved right: {first} to {later}");
}

#[test]
fn a_key_reaches_update_through_the_event_constructor() {
    need_clang!();
    let (session, seen) = start(CATCH, Limits::default());
    assert_eq!(x_of(&next_picture(&seen), "rect"), 160.0);
    session.key(true, "ArrowLeft");
    let moved = (0..50)
        .map(|_| x_of(&next_picture(&seen), "rect"))
        .find(|x| *x != 160.0);
    assert_eq!(moved, Some(140.0));
}

#[test]
fn a_trap_is_reported_with_the_message_and_the_site() {
    need_clang!();
    let (_session, seen) = start(TRAPS, Limits::default());
    loop {
        match next(&seen) {
            Seen::Frame(_) => {}
            Seen::Stopped(reason, message) => {
                assert_eq!(reason, Stop::Trap);
                assert!(message.contains("division by zero"), "{message}");
                assert!(message.contains("5 // 0"), "{message}");
                break;
            }
        }
    }
}

#[test]
fn a_runaway_update_is_stopped_by_the_watchdog() {
    need_clang!();
    let limits = Limits {
        call: Duration::from_millis(200),
        ..Limits::default()
    };
    let (session, seen) = start(SPINS, limits);
    next_picture(&seen);
    session.key(true, "a");
    loop {
        match next(&seen) {
            Seen::Frame(_) => {}
            Seen::Stopped(reason, message) => {
                assert_eq!(reason, Stop::Stuck);
                assert_eq!(message, STUCK_MESSAGE);
                break;
            }
        }
    }
    session.key(true, "b");
    assert!(
        seen.recv_timeout(Duration::from_millis(300)).is_err(),
        "a stopped program says nothing more"
    );
}
