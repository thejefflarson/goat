//! The engine through the C functions `goat_engine.h` declares, as Swift calls
//! them.

use goat_apple::{
    GoatEngineCallbacks, goat_engine_free, goat_engine_key, goat_engine_new, goat_engine_pointer,
    goat_engine_run, goat_engine_stop,
};
use std::ffi::c_void;
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

#[derive(Default)]
struct Heard {
    controls: Vec<String>,
    frames: usize,
    closed: bool,
}

type Shared = (Mutex<Heard>, Condvar);

unsafe extern "C" fn control(context: *mut c_void, json: *const u8, len: usize) {
    // SAFETY: `context` is the `Shared` the test leaked, and `json` is valid for `len`.
    let (shared, ready) = unsafe { &*(context as *const Shared) };
    let text = String::from_utf8(unsafe { std::slice::from_raw_parts(json, len) }.to_vec());
    shared.lock().unwrap().controls.push(text.expect("UTF-8"));
    ready.notify_all();
}

unsafe extern "C" fn frame(context: *mut c_void, bytes: *const u8, len: usize) {
    // SAFETY: as in `control`.
    let (shared, ready) = unsafe { &*(context as *const Shared) };
    assert!(!bytes.is_null() && len > 0);
    shared.lock().unwrap().frames += 1;
    ready.notify_all();
}

unsafe extern "C" fn closed(context: *mut c_void) {
    // SAFETY: as in `control`.
    let (shared, ready) = unsafe { &*(context as *const Shared) };
    shared.lock().unwrap().closed = true;
    ready.notify_all();
}

fn wait_for(shared: &Shared, mut done: impl FnMut(&Heard) -> bool) {
    let deadline = Instant::now() + Duration::from_secs(20);
    let mut heard = shared.0.lock().unwrap();
    while !done(&heard) {
        let left = deadline.saturating_duration_since(Instant::now());
        assert!(!left.is_zero(), "timed out; heard {:?}", heard.controls);
        heard = shared.1.wait_timeout(heard, left).unwrap().0;
    }
}

#[test]
fn the_c_functions_run_a_program_and_free_the_engine() {
    let shared: Arc<Shared> = Arc::default();
    let callbacks = GoatEngineCallbacks {
        context: Arc::as_ptr(&shared) as *mut c_void,
        control: Some(control),
        frame: Some(frame),
        closed: Some(closed),
    };
    let engine = goat_engine_new(callbacks);
    let source = br#"
init = {n: 0}
update = program(m, e) do match e do KeyDown(k) then {n: m.n + 1} else m done done
draw = program(m) do [Line({x1: 0, y1: 0, x2: m.n, y2: 0, color: "red"})] done
"#;
    // SAFETY: `engine` is live until the free below, and the slices outlive each call.
    unsafe {
        goat_engine_run(engine, source.as_ptr(), source.len());
        goat_engine_key(engine, b"a".as_ptr(), 1, true);
        goat_engine_pointer(engine, 0, 1.0, 2.0);
        goat_engine_pointer(engine, 9, 1.0, 2.0);
    }
    wait_for(&shared, |heard| heard.frames > 1);
    {
        let heard = shared.0.lock().unwrap();
        assert!(
            heard.controls[0].contains("\"ready\""),
            "{:?}",
            heard.controls
        );
        assert!(heard.controls.iter().any(|c| c.contains("\"running\"")));
    }

    // SAFETY: the engine is live, and not freed until the last call.
    unsafe {
        goat_engine_stop(engine);
        goat_engine_free(engine);
    }
    assert!(
        shared.0.lock().unwrap().closed,
        "closed arrives before free returns"
    );
}

#[test]
fn null_arguments_do_nothing() {
    // SAFETY: each function accepts a null engine and a null text.
    unsafe {
        goat_engine_run(std::ptr::null(), std::ptr::null(), 0);
        goat_engine_stop(std::ptr::null());
        goat_engine_key(std::ptr::null(), std::ptr::null(), 0, true);
        goat_engine_pointer(std::ptr::null(), 0, 0.0, 0.0);
        goat_engine_free(std::ptr::null_mut());
    }
}

#[test]
fn the_header_declares_every_function_the_library_exports() {
    let header = include_str!("../include/goat_engine.h");
    for name in [
        "goat_engine_new",
        "goat_engine_run",
        "goat_engine_stop",
        "goat_engine_key",
        "goat_engine_pointer",
        "goat_engine_free",
    ] {
        assert!(
            header.contains(&format!("{name}(")),
            "{name} is not declared"
        );
    }
}
