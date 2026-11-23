//! The loop of a windowed native binary (ADR 0015, ADR 0021). A window host
//! hands [`Session::start`] the exports of an interactive program; the session
//! runs `setup`, `update` and `draw` on a worker thread with an instance of its
//! own, feeds `update` the events the host sends and a frame clock, and gives
//! the host each picture as one `scene.frame` buffer. The host draws; it never
//! calls into goat.
//!
//! goat cannot be preempted from inside, so a watchdog thread owns the clock: a
//! call into the program that outlives its budget is reported as stuck and its
//! thread is parked for good (ADR 0021). A trap does the same without the wait.
//! Either way the instance is dead (ADR 0042) and the session ends in
//! [`Output::stopped`]; the host decides whether the process goes on.
//!
//! The C entry points at the bottom are the whole interface the Swift host
//! sees; `native/appkit/goat_host.h` declares them.

use crate::abi::{Ctx, GoatHost, GoatInstance, Instance};
use crate::adapter::Adapter;
use crate::driver::DEFAULT_HEAP_BYTES;
use crate::interactive::{STR_BYTES, STR_LEN};
use goat::{Boundary, Host, HostValue};
use std::ffi::{CStr, c_char, c_int, c_void};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::mpsc::{Receiver, RecvTimeoutError, Sender, channel};
use std::sync::{Arc, Once};
use std::time::{Duration, Instant};

/// Stack for the worker: address space, not memory, so a deep recursion reaches
/// goat's stack-overflow trap instead of a guard page.
const STACK_BYTES: usize = 256 << 20;

/// The gap between frame events, about sixty a second.
const TICK: Duration = Duration::from_millis(16);

/// The longest step a frame event reports, so a stall is not replayed as one
/// enormous step.
const MAX_STEP_MS: f64 = 250.0;

const WATCHDOG_POLL: Duration = Duration::from_millis(20);

pub const STUCK_MESSAGE: &str =
    "your program got stuck: it kept running without finishing, so it was stopped";

type Export0 = unsafe extern "C" fn(*const GoatHost, Ctx, *mut GoatInstance) -> *mut u8;
type Draw = unsafe extern "C" fn(*const GoatHost, Ctx, *mut GoatInstance, *mut u8);
type Export2 =
    unsafe extern "C" fn(*const GoatHost, Ctx, *mut GoatInstance, *mut u8, *mut u8) -> *mut u8;
type Attach = unsafe extern "C" fn(*const GoatHost, Ctx, *mut GoatInstance) -> i32;
type Alloc = unsafe extern "C" fn(*const GoatHost, Ctx, *mut GoatInstance, u32) -> *mut u8;
type FloatEvent = unsafe extern "C" fn(*const GoatHost, Ctx, *mut GoatInstance, f64) -> *mut u8;
type TextEvent = unsafe extern "C" fn(*const GoatHost, Ctx, *mut GoatInstance, *mut u8) -> *mut u8;
type PointEvent =
    unsafe extern "C" fn(*const GoatHost, Ctx, *mut GoatInstance, f64, f64) -> *mut u8;

/// One `goat_event_<Label>` export of the program.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct GoatEvent {
    pub label: *const c_char,
    pub constructor: *const c_void,
}

/// The exports of an interactive program, which the binary's entry code fills
/// in: ADR 0015's names, as `goat_llvm` emits them.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct GoatProgram {
    pub attach: Attach,
    pub setup: Export0,
    pub update: Export2,
    pub draw: Draw,
    pub alloc: Alloc,
    pub events: *const GoatEvent,
    pub event_count: u64,
}

// SAFETY: the pointers are code and constant data in the program's image.
unsafe impl Send for GoatProgram {}
unsafe impl Sync for GoatProgram {}

/// What the host has to say to a running program.
enum Input {
    Key { down: bool, text: String },
    Pointer { kind: Pointer, x: f64, y: f64 },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pointer {
    Move,
    Down,
    Up,
}

/// Why a session ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub enum Stop {
    Trap = 0,
    Stuck = 1,
}

/// Where a session's pictures and its end go. Both are called off the host's
/// main thread.
pub trait Output: Send + Sync {
    /// One picture: the bytes of a `scene.frame`, empty for a blank one.
    fn frame(&self, bytes: &[u8]);

    /// The program is done for good; `message` says why, as a user reads it.
    fn stopped(&self, reason: Stop, message: &str);
}

/// How long a call into the program may run before the watchdog stops it.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    /// One `update` or `draw`.
    pub call: Duration,
    /// `setup`, which runs the program's top-level code.
    pub setup: Duration,
}

impl Default for Limits {
    fn default() -> Limits {
        Limits {
            call: Duration::from_secs(1),
            setup: Duration::from_secs(10),
        }
    }
}

/// State the worker and the watchdog share.
struct Shared {
    clock: Instant,
    /// Nanoseconds past `clock` by which the call in progress must finish, plus
    /// one; zero when the program is idle.
    deadline: AtomicU64,
    stopped: AtomicBool,
    /// The worker's `pthread_t`, for the watchdog to park it.
    worker: AtomicUsize,
    limits: Limits,
}

impl Shared {
    fn enter(&self, budget: Duration) {
        let by = self.clock.elapsed() + budget;
        self.deadline
            .store(by.as_nanos() as u64 + 1, Ordering::Release);
    }

    fn leave(&self) {
        self.deadline.store(0, Ordering::Release);
    }

    fn overdue(&self) -> bool {
        match self.deadline.load(Ordering::Acquire) {
            0 => false,
            by => self.clock.elapsed().as_nanos() as u64 >= by - 1,
        }
    }

    /// Whether this call ended the session, which only one caller can.
    fn stop(&self) -> bool {
        !self.stopped.swap(true, Ordering::AcqRel)
    }
}

/// A running program.
pub struct Session {
    input: Sender<Input>,
    shared: Arc<Shared>,
}

impl Session {
    /// Starts `program` on a worker thread. `source` is the program's text, for
    /// the report of a trap.
    pub fn start(
        program: GoatProgram,
        source: String,
        output: Arc<dyn Output>,
        limits: Limits,
    ) -> std::io::Result<Session> {
        let shared = Arc::new(Shared {
            clock: Instant::now(),
            deadline: AtomicU64::new(0),
            stopped: AtomicBool::new(false),
            worker: AtomicUsize::new(0),
            limits,
        });
        let (input, inbox) = channel();
        let (worker_shared, worker_output) = (shared.clone(), output.clone());
        std::thread::Builder::new()
            .name("goat".into())
            .stack_size(STACK_BYTES)
            .spawn(move || {
                worker_shared
                    .worker
                    .store(unsafe { libc::pthread_self() } as usize, Ordering::Release);
                Worker::run(program, source, worker_output, worker_shared, inbox)
            })?;
        let watching = shared.clone();
        std::thread::Builder::new()
            .name("goat-watchdog".into())
            .spawn(move || watch(&watching, output.as_ref()))?;
        Ok(Session { input, shared })
    }

    /// A key went down or up; `text` is the browser's `KeyboardEvent.key`.
    pub fn key(&self, down: bool, text: &str) {
        self.send(Input::Key {
            down,
            text: text.to_string(),
        });
    }

    pub fn pointer(&self, kind: Pointer, x: f64, y: f64) {
        self.send(Input::Pointer { kind, x, y });
    }

    fn send(&self, input: Input) {
        if !self.shared.stopped.load(Ordering::Acquire) {
            let _ = self.input.send(input);
        }
    }
}

impl Drop for Session {
    /// Ends the watchdog. The worker leaves when its inbox closes, unless it is
    /// inside the program, which the process exit then ends.
    fn drop(&mut self) {
        self.shared.stopped.store(true, Ordering::Release);
    }
}

fn watch(shared: &Shared, output: &dyn Output) {
    while !shared.stopped.load(Ordering::Acquire) {
        std::thread::sleep(WATCHDOG_POLL);
        if shared.overdue() && shared.stop() {
            park(shared.worker.load(Ordering::Acquire));
            output.stopped(Stop::Stuck, STUCK_MESSAGE);
        }
    }
}

/// Makes the worker thread sleep for good, wherever it is. A signal reaches a
/// thread that spins inside generated code, which no flag could. A thread
/// parked inside the host's allocator would keep its lock, but a call that
/// outlives its budget is in generated code, which allocates from the
/// instance's own heap.
fn park(thread: usize) {
    static HANDLER: Once = Once::new();
    HANDLER.call_once(|| {
        extern "C" fn sleep_forever(_: c_int) {
            loop {
                // SAFETY: `pause` is async-signal-safe.
                unsafe { libc::pause() };
            }
        }
        // SAFETY: the handler only calls `pause`.
        unsafe { libc::signal(libc::SIGUSR2, sleep_forever as *const () as usize) };
    });
    if thread != 0 {
        // SAFETY: `thread` is the worker's id, and the worker never exits.
        unsafe { libc::pthread_kill(thread as libc::pthread_t, libc::SIGUSR2) };
    }
}

/// Answers the program's host calls: the picture goes to the [`Output`], and
/// nothing else is on offer.
struct Pictures {
    output: Arc<dyn Output>,
    shared: Arc<Shared>,
    source: String,
    instance: *mut GoatInstance,
    picture: Vec<u8>,
}

impl Host for Pictures {
    fn signature(&self, module: &str, name: &str) -> Option<(Vec<Boundary>, Boundary)> {
        match (module, name) {
            ("scene", "begin" | "end" | "frame") => Some((vec![], Boundary::Unit)),
            _ => None,
        }
    }

    fn call(&mut self, module: &str, name: &str, _: &[HostValue]) -> Result<HostValue, String> {
        match (module, name) {
            ("scene", "begin") => self.picture.clear(),
            ("scene", "end") => self.output.frame(&self.picture),
            _ => return Err(format!("this host has no {module}.{name}")),
        }
        Ok(HostValue::Unit)
    }

    fn frame(&mut self, bytes: &[u8]) -> Result<(), String> {
        self.picture.clear();
        self.picture.extend_from_slice(bytes);
        Ok(())
    }
}

/// A trap ends the program: report it, then sleep, since generated code cannot
/// be returned into.
unsafe extern "C" fn trap(ctx: Ctx, message: *const u8, len: u64) -> ! {
    // SAFETY: `ctx` is the adapter the worker passed to the export; a raw
    // projection avoids a reference beside the `&mut` the host call holds.
    let pictures = unsafe { &*std::ptr::addr_of!((*ctx.cast::<Adapter<Pictures>>()).host) };
    let message = match len {
        0 => std::borrow::Cow::Borrowed(""),
        // SAFETY: the table's contract: `len` bytes at `message`.
        _ => String::from_utf8_lossy(unsafe { std::slice::from_raw_parts(message, len as usize) }),
    };
    // SAFETY: the worker's instance outlives every call into the program.
    let site = unsafe { pictures.instance.as_ref() }.and_then(GoatInstance::site);
    if pictures.shared.stop() {
        let report = goat::render_trap(&pictures.source, &message, site);
        pictures.output.stopped(Stop::Trap, &report);
    }
    pictures.shared.leave();
    loop {
        std::thread::park();
    }
}

/// How `update` is told of an event the program has a constructor for.
#[derive(Clone, Copy)]
enum Constructor {
    Tick(FloatEvent),
    Key { down: bool, make: TextEvent },
    Pointer { kind: Pointer, make: PointEvent },
}

/// The function at `at`, as the type `T` the caller says it has.
///
/// # Safety
///
/// `at` is the address of a function of type `T`.
unsafe fn code<T: Copy>(at: *const c_void) -> T {
    // SAFETY: the caller's contract; a function pointer is one word, as `T` is.
    unsafe { std::mem::transmute_copy(&at) }
}

/// The constructors for the labels of the canvas vocabulary (`Frame`,
/// `KeyPress`, `MouseMove`, ...) and the turtle's (`Tick`, `KeyDown`,
/// `PointerMove`, ...).
fn constructor_of(label: &str, at: *const c_void) -> Option<Constructor> {
    // SAFETY: the entry code points `at` at the export named `goat_event_<label>`,
    // whose signature follows from the event's payload.
    unsafe {
        Some(match label {
            "Frame" | "Tick" => Constructor::Tick(code(at)),
            "KeyPress" | "KeyDown" => Constructor::Key {
                down: true,
                make: code(at),
            },
            "KeyRelease" | "KeyUp" => Constructor::Key {
                down: false,
                make: code(at),
            },
            "MouseMove" | "PointerMove" => Constructor::Pointer {
                kind: Pointer::Move,
                make: code(at),
            },
            "MousePress" | "PointerDown" => Constructor::Pointer {
                kind: Pointer::Down,
                make: code(at),
            },
            "MouseRelease" | "PointerUp" => Constructor::Pointer {
                kind: Pointer::Up,
                make: code(at),
            },
            _ => return None,
        })
    }
}

struct Worker {
    program: GoatProgram,
    instance: Instance,
    adapter: Box<Adapter<Pictures>>,
    table: Box<GoatHost>,
    shared: Arc<Shared>,
    constructors: Vec<Constructor>,
}

impl Worker {
    fn run(
        program: GoatProgram,
        source: String,
        output: Arc<dyn Output>,
        shared: Arc<Shared>,
        inbox: Receiver<Input>,
    ) {
        let mut instance = Instance::new(DEFAULT_HEAP_BYTES);
        let pictures = Pictures {
            output: output.clone(),
            shared: shared.clone(),
            source,
            instance: instance.as_ptr(),
            picture: Vec::new(),
        };
        let adapter = Box::new(Adapter::new(pictures, trap));
        let table = Box::new(adapter.table());
        // SAFETY: the entry code's table holds `event_count` entries.
        let events =
            unsafe { std::slice::from_raw_parts(program.events, program.event_count as usize) };
        let constructors = events
            .iter()
            .filter_map(|event| {
                // SAFETY: each label is a NUL-terminated string in the image.
                let label = unsafe { CStr::from_ptr(event.label) }.to_string_lossy();
                constructor_of(&label, event.constructor)
            })
            .collect();
        let mut worker = Worker {
            program,
            instance,
            adapter,
            table,
            shared,
            constructors,
        };
        worker.serve(&output, inbox);
    }

    /// Runs `call` against the table, the context and the instance, with the
    /// watchdog's clock running.
    fn call<R>(
        &mut self,
        budget: Duration,
        call: impl FnOnce(*const GoatHost, Ctx, *mut GoatInstance) -> R,
    ) -> R {
        self.instance.set_stack_limit(crate::stack::limit());
        let table: *const GoatHost = &*self.table;
        let (ctx, raw) = (self.adapter.ctx(), self.instance.as_ptr());
        self.shared.enter(budget);
        let result = call(table, ctx, raw);
        self.shared.leave();
        result
    }

    fn serve(&mut self, output: &Arc<dyn Output>, inbox: Receiver<Input>) {
        let program = self.program;
        let setup = self.shared.limits.setup;
        // SAFETY: `program` holds the exports `goat_llvm` emits, which take the
        // table, the context and the instance this worker keeps alive.
        let status = self.call(setup, |t, c, i| unsafe { (program.attach)(t, c, i) });
        if status != 0 {
            let message = "the program's runtime is out of step with its code";
            if self.shared.stop() {
                output.stopped(Stop::Trap, message);
            }
            return;
        }
        let mut model = self.call(setup, |t, c, i| unsafe { (program.setup)(t, c, i) });
        self.draw(model);

        let ticks = self
            .constructors
            .iter()
            .any(|c| matches!(c, Constructor::Tick(_)));
        let mut last = Instant::now();
        loop {
            let first = if ticks {
                match inbox.recv_timeout(TICK.saturating_sub(last.elapsed())) {
                    Ok(input) => Some(input),
                    Err(RecvTimeoutError::Timeout) => None,
                    Err(RecvTimeoutError::Disconnected) => return,
                }
            } else {
                match inbox.recv() {
                    Ok(input) => Some(input),
                    Err(_) => return,
                }
            };
            for input in first.into_iter().chain(inbox.try_iter()) {
                if let Some(event) = self.event(&input) {
                    model = self.update(model, event);
                }
            }
            if ticks && last.elapsed() >= TICK {
                let step = (last.elapsed().as_secs_f64() * 1000.0).min(MAX_STEP_MS);
                last = Instant::now();
                if let Some(event) = self.tick(step) {
                    model = self.update(model, event);
                }
            }
            self.draw(model);
        }
    }

    fn update(&mut self, model: *mut u8, event: *mut u8) -> *mut u8 {
        let (update, budget) = (self.program.update, self.shared.limits.call);
        // SAFETY: `update` consumes the model and the event, which this worker
        // owns, and returns the next model.
        self.call(budget, |t, c, i| unsafe { update(t, c, i, model, event) })
    }

    fn draw(&mut self, model: *mut u8) {
        let (draw, budget) = (self.program.draw, self.shared.limits.call);
        // SAFETY: `draw` only reads the model.
        self.call(budget, |t, c, i| unsafe { draw(t, c, i, model) });
    }

    fn tick(&mut self, step: f64) -> Option<*mut u8> {
        let budget = self.shared.limits.call;
        let make = self.constructors.iter().find_map(|c| match c {
            Constructor::Tick(make) => Some(*make),
            _ => None,
        })?;
        // SAFETY: the constructor takes the frame's milliseconds.
        Some(self.call(budget, |t, c, i| unsafe { make(t, c, i, step) }))
    }

    /// The event `input` stands for, or `None` when the program does not handle
    /// that kind of event.
    fn event(&mut self, input: &Input) -> Option<*mut u8> {
        let budget = self.shared.limits.call;
        match input {
            Input::Key { down, text } => {
                let make = self.constructors.iter().find_map(|c| match c {
                    Constructor::Key { down: d, make } if d == down => Some(*make),
                    _ => None,
                })?;
                let key = self.string(text)?;
                // SAFETY: the constructor takes a goat string, which it consumes.
                Some(self.call(budget, |t, c, i| unsafe { make(t, c, i, key) }))
            }
            Input::Pointer { kind, x, y } => {
                let make = self.constructors.iter().find_map(|c| match c {
                    Constructor::Pointer { kind: k, make } if k == kind => Some(*make),
                    _ => None,
                })?;
                // SAFETY: the constructor takes the pointer's two coordinates.
                Some(self.call(budget, |t, c, i| unsafe { make(t, c, i, *x, *y) }))
            }
        }
    }

    /// A goat string holding `text`, owned by the caller (count 1).
    fn string(&mut self, text: &str) -> Option<*mut u8> {
        let len = u32::try_from(text.len()).ok()?;
        let size = (STR_BYTES as u32).checked_add(len)?;
        let (alloc, budget) = (self.program.alloc, self.shared.limits.call);
        // SAFETY: `goat_alloc` returns a block of the size asked for.
        let at = self.call(budget, |t, c, i| unsafe { alloc(t, c, i, size) });
        let written = self
            .instance
            .write(at as usize + STR_LEN, &len.to_le_bytes())
            .and_then(|()| {
                self.instance
                    .write(at as usize + STR_BYTES, text.as_bytes())
            });
        written.ok().map(|()| at)
    }
}

/// What a host that is not Rust holds to call the session: callbacks to draw
/// and to report an end, and the `user` pointer they receive.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct GoatCallbacks {
    pub user: *mut c_void,
    pub frame: unsafe extern "C" fn(*mut c_void, *const u8, u64),
    pub stopped: unsafe extern "C" fn(*mut c_void, Stop, *const u8, u64),
}

struct CallbackOutput(GoatCallbacks);

// SAFETY: the host promises its callbacks may run on any thread.
unsafe impl Send for CallbackOutput {}
unsafe impl Sync for CallbackOutput {}

impl Output for CallbackOutput {
    fn frame(&self, bytes: &[u8]) {
        // SAFETY: the host's contract: callable from any thread with a pointer
        // and the length behind it.
        unsafe { (self.0.frame)(self.0.user, bytes.as_ptr(), bytes.len() as u64) }
    }

    fn stopped(&self, reason: Stop, message: &str) {
        // SAFETY: as `frame`.
        unsafe { (self.0.stopped)(self.0.user, reason, message.as_ptr(), message.len() as u64) }
    }
}

/// The limits for a window host: `$GOAT_STUCK_MS` replaces the default budget
/// of one call, which a test sets small.
fn host_limits() -> Limits {
    let mut limits = Limits::default();
    if let Some(ms) = std::env::var("GOAT_STUCK_MS")
        .ok()
        .and_then(|ms| ms.parse().ok())
    {
        limits.call = Duration::from_millis(ms);
    }
    limits
}

/// Starts `program` and returns the session, or null if a thread would not
/// start.
///
/// # Safety
///
/// `program` and `callbacks` point at valid structs, the program's exports stay
/// loaded for the life of the process, and `source` holds `source_len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn goat_session_start(
    program: *const GoatProgram,
    source: *const u8,
    source_len: u64,
    callbacks: *const GoatCallbacks,
) -> *mut Session {
    // SAFETY: the caller's contract.
    let (program, callbacks, source) = unsafe {
        (
            *program,
            *callbacks,
            std::slice::from_raw_parts(source, source_len as usize),
        )
    };
    let source = String::from_utf8_lossy(source).into_owned();
    let output = Arc::new(CallbackOutput(callbacks));
    match Session::start(program, source, output, host_limits()) {
        Ok(session) => Box::into_raw(Box::new(session)),
        Err(_) => std::ptr::null_mut(),
    }
}

/// # Safety
///
/// `session` came from [`goat_session_start`] and is not freed, and `key`
/// holds `len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn goat_session_key(
    session: *const Session,
    down: c_int,
    key: *const u8,
    len: u64,
) {
    // SAFETY: the caller's contract.
    let session = unsafe { &*session };
    let key = match len {
        0 => &[],
        // SAFETY: the caller's contract.
        _ => unsafe { std::slice::from_raw_parts(key, len as usize) },
    };
    session.key(down != 0, &String::from_utf8_lossy(key));
}

/// # Safety
///
/// `session` came from [`goat_session_start`] and is not freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn goat_session_pointer(
    session: *const Session,
    kind: c_int,
    x: f64,
    y: f64,
) {
    let kind = match kind {
        0 => Pointer::Move,
        1 => Pointer::Down,
        2 => Pointer::Up,
        _ => return,
    };
    // SAFETY: the caller's contract.
    unsafe { &*session }.pointer(kind, x, y);
}

/// # Safety
///
/// `session` came from [`goat_session_start`] and is not used again.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn goat_session_free(session: *mut Session) {
    // SAFETY: the caller's contract.
    drop(unsafe { Box::from_raw(session) });
}

#[cfg(test)]
mod tests;
