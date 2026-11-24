//! The C seam, declared in `include/goat_engine.h`.

use crate::engine::{Engine, Sink};
use crate::events::Pointer;
use std::ffi::c_void;

/// The host's three callbacks and the pointer they are handed back. Each runs
/// on the engine's delivery thread, one at a time.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct GoatEngineCallbacks {
    pub context: *mut c_void,
    pub control: Option<unsafe extern "C" fn(*mut c_void, *const u8, usize)>,
    pub frame: Option<unsafe extern "C" fn(*mut c_void, *const u8, usize)>,
    pub closed: Option<unsafe extern "C" fn(*mut c_void)>,
}

// SAFETY: the header makes the host answerable for `context` being usable from
// the engine's delivery thread until `closed` returns.
unsafe impl Send for GoatEngineCallbacks {}

impl Sink for GoatEngineCallbacks {
    fn control(&mut self, json: &str) {
        if let Some(control) = self.control {
            // SAFETY: the slice is valid for the call, as the header promises.
            unsafe { control(self.context, json.as_ptr(), json.len()) };
        }
    }

    fn frame(&mut self, bytes: &[u8]) {
        if let Some(frame) = self.frame {
            // SAFETY: as in `control`.
            unsafe { frame(self.context, bytes.as_ptr(), bytes.len()) };
        }
    }

    fn closed(&mut self) {
        if let Some(closed) = self.closed {
            // SAFETY: the host's `context` is still valid until this returns.
            unsafe { closed(self.context) };
        }
    }
}

/// `len` bytes at `bytes` as text, or "" for a null pointer.
///
/// # Safety
/// `bytes` must be valid for reads of `len` bytes, or null.
unsafe fn text<'a>(bytes: *const u8, len: usize) -> std::borrow::Cow<'a, str> {
    if bytes.is_null() {
        return "".into();
    }
    // SAFETY: the caller guarantees the range.
    String::from_utf8_lossy(unsafe { std::slice::from_raw_parts(bytes, len) })
}

/// Start an engine. Free it with `goat_engine_free`.
#[unsafe(no_mangle)]
pub extern "C" fn goat_engine_new(callbacks: GoatEngineCallbacks) -> *mut Engine {
    Box::into_raw(Box::new(Engine::new(callbacks)))
}

/// Run `source`, or reload it into the interactive program that is live.
///
/// # Safety
/// `engine` came from `goat_engine_new` and is not freed; `source` is valid for
/// `len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn goat_engine_run(engine: *const Engine, source: *const u8, len: usize) {
    // SAFETY: the caller guarantees both pointers.
    if let Some(engine) = unsafe { engine.as_ref() } {
        engine.run(&unsafe { text(source, len) });
    }
}

/// # Safety
/// `engine` came from `goat_engine_new` and is not freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn goat_engine_stop(engine: *const Engine) {
    // SAFETY: the caller guarantees the pointer.
    if let Some(engine) = unsafe { engine.as_ref() } {
        engine.stop();
    }
}

/// # Safety
/// `engine` came from `goat_engine_new` and is not freed; `key` is valid for
/// `len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn goat_engine_key(
    engine: *const Engine,
    key: *const u8,
    len: usize,
    down: bool,
) {
    // SAFETY: the caller guarantees both pointers.
    if let Some(engine) = unsafe { engine.as_ref() } {
        engine.key(&unsafe { text(key, len) }, down);
    }
}

/// `kind` is 0 for a move, 1 for a press and 2 for a release; any other value
/// is ignored.
///
/// # Safety
/// `engine` came from `goat_engine_new` and is not freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn goat_engine_pointer(engine: *const Engine, kind: u32, x: f64, y: f64) {
    let kind = match kind {
        0 => Pointer::Move,
        1 => Pointer::Down,
        2 => Pointer::Up,
        _ => return,
    };
    // SAFETY: the caller guarantees the pointer.
    if let Some(engine) = unsafe { engine.as_ref() } {
        engine.pointer(kind, x, y);
    }
}

/// Stop the program and free the engine. `closed` is called once before this
/// returns, and no callback runs after. Do not call this from a callback.
///
/// # Safety
/// `engine` came from `goat_engine_new` and has not been freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn goat_engine_free(engine: *mut Engine) {
    if !engine.is_null() {
        // SAFETY: the caller guarantees the pointer is live and unique.
        drop(unsafe { Box::from_raw(engine) });
    }
}
