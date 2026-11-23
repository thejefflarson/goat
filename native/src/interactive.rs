//! The host side of ADR 0015 for a natively compiled program: load it, feed it
//! events, and stream each frame it draws to a [`SceneSink`], as
//! `goat::native::Interactive` does for wasm. A [`Guest`] is the raw program,
//! an [`Interactive`] the loop built on it, and [`Interactive::reload`] swaps in
//! a recompiled program over the same heap (ADR 0035).
//!
//! The instance is shared by both modules of a reload, and it keeps the
//! closures a module stored (`update`, `draw`, `sites`) and its failed-refresh
//! reason, so each module's copy travels with it and is put in the instance
//! around that module's calls ([`ModuleState`]). A trap kills the instance
//! (ADR 0042): every call after one fails.

use crate::abi::{Ctx, Instance};
use crate::abi::{GoatHost, GoatInstance, ModuleState};
use crate::adapter::Adapter;
use crate::driver::{DEFAULT_HEAP_BYTES, Library, Trap};
use goat::{Event, Host, Reloaded, ResetReason, Scene, SceneSink};
use std::marker::PhantomData;
use std::time::{Duration, Instant};

const SUBSCRIPTIONS: &str = "goat_subscriptions";

/// Where a string object keeps its length and its bytes (`docs/mir.md`).
const STR_LEN: usize = 8;
const STR_BYTES: usize = 12;

const STOPPED: &str = "the program has stopped";

/// The address of a goat object, as an export returned it. An object a
/// constant program built (a record of constants) lives in the library, not the
/// heap.
pub type Object = usize;

/// A value an event constructor takes.
#[derive(Clone, Copy, Debug)]
pub enum Arg {
    Float(f64),
    Object(Object),
}

struct Core<H> {
    instance: Instance,
    adapter: Box<Adapter<H>>,
    table: Box<GoatHost>,
}

struct Module {
    library: Library,
    state: ModuleState,
}

type Export0<R> = unsafe extern "C" fn(*const GoatHost, Ctx, *mut GoatInstance) -> R;
type Export1<A, R> = unsafe extern "C" fn(*const GoatHost, Ctx, *mut GoatInstance, A) -> R;
type Export2<A, B, R> = unsafe extern "C" fn(*const GoatHost, Ctx, *mut GoatInstance, A, B) -> R;

impl Module {
    fn new(library: Library) -> Module {
        Module {
            library,
            state: ModuleState::default(),
        }
    }

    /// Runs `call` with the table, context and instance of `core`, with this
    /// module's state in the instance. A trap kills the instance.
    fn invoke<H: Host, R>(
        &mut self,
        core: &mut Core<H>,
        name: &str,
        call: impl FnOnce(*const GoatHost, Ctx, *mut GoatInstance) -> R,
    ) -> Result<R, String> {
        if core.instance.is_dead() {
            return Err(format!("{name}: {STOPPED}"));
        }
        let trap: Trap = self
            .library
            .symbol("goat_shim_trap")
            .map_err(|e| e.to_string())?;
        core.adapter.set_trap(trap);
        *core.table = core.adapter.table();
        core.instance.set_module_state(self.state);
        core.instance.set_stack_limit(crate::stack::limit());
        let table: *const GoatHost = &*core.table;
        let (ctx, raw) = (core.adapter.ctx(), core.instance.as_ptr());
        let outcome = self
            .library
            .guarded(|| call(table, ctx, raw))
            .map_err(|e| e.to_string())?;
        match outcome {
            Ok(result) => {
                self.state = core.instance.module_state();
                Ok(result)
            }
            Err(message) => {
                core.instance.mark_dead();
                Err(format!(
                    "{name} trapped: {}",
                    String::from_utf8_lossy(&message)
                ))
            }
        }
    }

    fn call0<H: Host, R>(&mut self, core: &mut Core<H>, name: &str) -> Result<R, String> {
        let export: Export0<R> = self.library.symbol(name).map_err(|e| e.to_string())?;
        // SAFETY: the emitter defines `name` with this signature, and the
        // table, context and instance outlive the call.
        self.invoke(core, name, |t, c, i| unsafe { export(t, c, i) })
    }

    fn call1<H: Host, A: Copy, R>(
        &mut self,
        core: &mut Core<H>,
        name: &str,
        a: A,
    ) -> Result<R, String> {
        let export: Export1<A, R> = self.library.symbol(name).map_err(|e| e.to_string())?;
        // SAFETY: as `call0`.
        self.invoke(core, name, |t, c, i| unsafe { export(t, c, i, a) })
    }

    fn call2<H: Host, A: Copy, B: Copy, R>(
        &mut self,
        core: &mut Core<H>,
        name: &str,
        a: A,
        b: B,
    ) -> Result<R, String> {
        let export: Export2<A, B, R> = self.library.symbol(name).map_err(|e| e.to_string())?;
        // SAFETY: as `call0`.
        self.invoke(core, name, |t, c, i| unsafe { export(t, c, i, a, b) })
    }

    fn object0<H: Host>(&mut self, core: &mut Core<H>, name: &str) -> Result<Object, String> {
        self.call0::<H, *mut u8>(core, name).map(|p| p as Object)
    }

    fn object1<H: Host, A: Copy>(
        &mut self,
        core: &mut Core<H>,
        name: &str,
        a: A,
    ) -> Result<Object, String> {
        self.call1::<H, A, *mut u8>(core, name, a)
            .map(|p| p as Object)
    }
}

/// A natively compiled interactive program, loaded: the raw exports of
/// ADR 0015, which [`Interactive`] drives.
pub struct Guest<H: Host> {
    core: Core<H>,
    module: Module,
}

impl<H: Host> Guest<H> {
    /// Loads `library` over a fresh heap, answering the program's host calls
    /// from `host`.
    pub fn new(library: Library, host: H) -> Result<Guest<H>, String> {
        let trap: Trap = library
            .symbol("goat_shim_trap")
            .map_err(|e| e.to_string())?;
        let adapter = Box::new(Adapter::new(host, trap));
        let table = Box::new(adapter.table());
        let mut guest = Guest {
            core: Core {
                instance: Instance::new(DEFAULT_HEAP_BYTES),
                adapter,
                table,
            },
            module: Module::new(library),
        };
        check_versions(&mut guest.module, &mut guest.core)?;
        Ok(guest)
    }

    /// The event labels the program handles, in the order it exports them.
    pub fn subscriptions(&self) -> Vec<String> {
        subscriptions(&self.module.library)
    }

    pub fn setup(&mut self) -> Result<Object, String> {
        self.module.object0(&mut self.core, "goat_setup")
    }

    /// The event `label` builds from `args`, owned by the caller.
    pub fn event(&mut self, label: &str, args: &[Arg]) -> Result<Object, String> {
        event(&mut self.module, &mut self.core, label, args)
    }

    /// Consumes the model and the event, returning the new model.
    pub fn update(&mut self, model: Object, event: Object) -> Result<Object, String> {
        self.module
            .call2::<_, _, _, *mut u8>(
                &mut self.core,
                "goat_update",
                model as *mut u8,
                event as *mut u8,
            )
            .map(|p| p as Object)
    }

    /// Streams the model's picture to the host; the caller keeps the model.
    pub fn draw(&mut self, model: Object) -> Result<(), String> {
        self.module
            .call1(&mut self.core, "goat_draw", model as *mut u8)
    }

    pub fn release_model(&mut self, model: Object) -> Result<(), String> {
        self.module
            .call1(&mut self.core, "goat_release_model", model as *mut u8)
    }

    pub fn shutdown(&mut self) -> Result<(), String> {
        self.module.call0(&mut self.core, "goat_shutdown")
    }

    /// A goat string holding `text`, owned by the caller (count 1).
    pub fn string(&mut self, text: &str) -> Result<Object, String> {
        let len = u32::try_from(text.len()).map_err(|_| "string too long".to_string())?;
        let size = STR_BYTES as u32 + len;
        let at = self.module.object1(&mut self.core, "goat_alloc", size)?;
        let instance = &mut self.core.instance;
        instance.write(at + STR_LEN, &len.to_le_bytes())?;
        instance.write(at + STR_BYTES, text.as_bytes())?;
        Ok(at)
    }

    /// `len` bytes of the object at `at`, `offset` bytes in.
    ///
    /// # Safety
    ///
    /// `at` must be an object the program returned that is still alive, and
    /// `offset + len` must lie inside it.
    pub unsafe fn read(&self, at: Object, offset: usize, len: usize) -> Vec<u8> {
        // SAFETY: the caller promises the range is inside a live object.
        unsafe { std::slice::from_raw_parts((at + offset) as *const u8, len) }.to_vec()
    }

    pub fn live_allocs(&self) -> u32 {
        self.core.instance.live()
    }

    /// How far the heap has grown, in bytes.
    pub fn heap_end(&self) -> u64 {
        self.core.instance.heap_used()
    }

    /// Every allocation the program has made, freed or not.
    pub fn allocations(&self) -> u64 {
        self.core.instance.allocations()
    }

    pub fn host_mut(&mut self) -> &mut H {
        &mut self.core.adapter.host
    }

    pub fn into_host(self) -> H {
        self.core.adapter.host
    }
}

fn check_versions<H: Host>(module: &mut Module, core: &mut Core<H>) -> Result<(), String> {
    match module.call0::<H, i32>(core, "goat_attach")? {
        0 => Ok(()),
        1 => Err("the program needs a newer goat_host".to_string()),
        _ => Err("the program needs a newer goat_instance".to_string()),
    }
}

fn subscriptions(library: &Library) -> Vec<String> {
    let Ok(start) = library.symbol::<*const u8>(SUBSCRIPTIONS) else {
        return Vec::new();
    };
    let mut labels = Vec::new();
    let mut at = start;
    // SAFETY: the table is NUL-separated labels closed by an empty one, which
    // the emitter writes.
    unsafe {
        loop {
            let label = std::ffi::CStr::from_ptr(at.cast());
            if label.is_empty() {
                break;
            }
            labels.push(label.to_string_lossy().into_owned());
            at = at.add(label.to_bytes().len() + 1);
        }
    }
    labels
}

fn event<H: Host>(
    module: &mut Module,
    core: &mut Core<H>,
    label: &str,
    args: &[Arg],
) -> Result<Object, String> {
    let name = format!("goat_event_{label}");
    match args {
        [] => module.object0(core, &name),
        [Arg::Float(x)] => module.object1(core, &name, *x),
        [Arg::Object(o)] => module.object1(core, &name, *o as *mut u8),
        [Arg::Float(x), Arg::Float(y)] => module
            .call2::<H, f64, f64, *mut u8>(core, &name, *x, *y)
            .map(|p| p as Object),
        _ => Err(format!("{name} does not take these arguments")),
    }
}

/// An event a host can send: the label of the `goat_event_<Label>` constructor
/// the program exports for it, and how to build the event value in the guest.
pub trait HostEvent {
    fn tag(&self) -> &'static str;

    fn construct<H: Host>(&self, guest: &mut Guest<H>) -> Result<Object, String>;
}

impl HostEvent for Event {
    fn tag(&self) -> &'static str {
        Event::tag(self)
    }

    fn construct<H: Host>(&self, guest: &mut Guest<H>) -> Result<Object, String> {
        match self {
            Event::Tick(dt) => guest.event(self.tag(), &[Arg::Float(*dt)]),
            Event::KeyDown(key) | Event::KeyUp(key) => {
                let key = guest.string(key)?;
                guest.event(self.tag(), &[Arg::Object(key)])
            }
            Event::PointerMove { x, y }
            | Event::PointerDown { x, y }
            | Event::PointerUp { x, y } => {
                guest.event(self.tag(), &[Arg::Float(*x), Arg::Float(*y)])
            }
        }
    }
}

/// A running interactive program. Any trap stops it for good: later calls
/// fail, since a half-run `update` leaves no model worth continuing from.
pub struct Interactive<S: SceneSink + 'static, E: HostEvent = Event> {
    guest: Guest<Scene<S>>,
    model: Option<Object>,
    subscriptions: Vec<String>,
    events: PhantomData<fn(&E)>,
    carried: Duration,
}

impl<S: SceneSink + 'static, E: HostEvent> Interactive<S, E> {
    /// Loads `library` and runs its top-level code, which yields the first
    /// model.
    pub fn new(library: Library, sink: S) -> Result<Self, String> {
        let mut guest = Guest::new(library, Scene(sink))?;
        let subscriptions = guest.subscriptions();
        let model = guest.setup()?;
        Ok(Interactive {
            guest,
            model: Some(model),
            subscriptions,
            events: PhantomData,
            carried: Duration::ZERO,
        })
    }

    /// Swaps in a recompiled program over the same heap (ADR 0035). The old
    /// module snapshots the model, the new one refreshes a model of its own
    /// types from the snapshot, and the old module is unloaded. A model that
    /// cannot be refreshed restarts from the new `init` (or when the program
    /// had stopped), and the reason says why. A trap in the snapshot or the
    /// refresh does the same in a fresh instance, as wasm does, since the
    /// trapped one is dead (ADR 0042). If the new program cannot
    /// start, the old one is left running.
    pub fn reload(&mut self, library: Library) -> Result<Reloaded, String> {
        let core = &mut self.guest.core;
        let mut new = Module::new(library);
        check_versions(&mut new, core)?;
        let fresh = new.object0(core, "goat_setup")?;
        let old = &mut self.guest.module;

        let (model, outcome, old_runs) = match self.model.take() {
            None => (fresh, Reloaded::Reset(ResetReason::reshaped()), true),
            Some(model) => {
                let started = Instant::now();
                // The snapshot consumes the model, so the old module is not
                // asked to release it.
                let refreshed = old
                    .object1(core, "goat_snapshot", model as *mut u8)
                    .and_then(|image| {
                        new.call2::<_, _, _, *mut u8>(
                            core,
                            "goat_refresh",
                            image as *mut u8,
                            fresh as *mut u8,
                        )
                    });
                self.carried = started.elapsed();
                match refreshed.map(|p| p as Object) {
                    Ok(0) => (fresh, Reloaded::Reset(reason(&mut new, core)), true),
                    Ok(rebuilt) => {
                        new.call1::<_, _, ()>(core, "goat_release_model", fresh as *mut u8)?;
                        (rebuilt, Reloaded::Refreshed, true)
                    }
                    Err(_) => {
                        // The trap killed the instance both modules share, so
                        // the new module starts over in a fresh one and the old
                        // module goes without a shutdown.
                        core.instance = Instance::new(DEFAULT_HEAP_BYTES);
                        new.state = ModuleState::default();
                        check_versions(&mut new, core)?;
                        let restarted = new.object0(core, "goat_setup")?;
                        (restarted, Reloaded::Reset(ResetReason::reshaped()), false)
                    }
                }
            }
        };
        if old_runs {
            old.call0::<_, ()>(core, "goat_shutdown")?;
            old.call0::<_, ()>(core, "goat_free_static")?;
        }

        self.guest.module = new;
        self.subscriptions = self.guest.subscriptions();
        self.model = Some(model);
        Ok(outcome)
    }

    /// How long the last reload spent in the old module's snapshot and the new
    /// module's refresh: the part of a reload that grows with the model.
    pub fn carry_time(&self) -> Duration {
        self.carried
    }

    /// The event tags the program handles; the host need only listen for
    /// these.
    pub fn subscriptions(&self) -> &[String] {
        &self.subscriptions
    }

    /// Delivers `event` to `update`. Returns false, doing nothing, if the
    /// program does not handle that kind of event.
    pub fn send(&mut self, event: &E) -> Result<bool, String> {
        if !self.subscriptions.iter().any(|s| s == event.tag()) {
            return Ok(false);
        }
        let model = self.model.take().ok_or(STOPPED)?;
        let built = event.construct(&mut self.guest)?;
        self.model = Some(self.guest.update(model, built)?);
        Ok(true)
    }

    /// Streams the current picture to the sink as one frame.
    pub fn draw(&mut self) -> Result<(), String> {
        let model = self.model.ok_or(STOPPED)?;
        let drawn = self.guest.draw(model);
        if drawn.is_err() {
            self.model = None;
        }
        drawn
    }

    /// Tears the program down and hands back the sink with the heap blocks
    /// still allocated, which is zero for a correct program.
    pub fn finish(mut self) -> Result<(S, u32), String> {
        let model = self.model.ok_or(STOPPED)?;
        self.guest.release_model(model)?;
        self.guest.shutdown()?;
        let live = self.guest.live_allocs();
        Ok((self.guest.into_host().0, live))
    }

    /// Heap blocks allocated and not yet freed, the model's among them.
    pub fn live_allocs(&self) -> u32 {
        self.guest.live_allocs()
    }

    /// How far the heap has grown, in bytes.
    pub fn heap_end(&self) -> u64 {
        self.guest.heap_end()
    }

    /// Every allocation the program has made, freed or not.
    pub fn allocations(&self) -> u64 {
        self.guest.allocations()
    }

    /// The sink the frames stream to.
    pub fn sink_mut(&mut self) -> &mut S {
        &mut self.guest.host_mut().0
    }

    /// Gives up on the program, returning the sink without tearing it down.
    pub fn into_sink(self) -> S {
        self.guest.into_host().0
    }
}

/// The parts of the reason the last `goat_refresh` gave up, read out of the
/// module's heap.
fn reason<H: Host>(module: &mut Module, core: &mut Core<H>) -> ResetReason {
    let mut parts = Vec::new();
    while let Ok(at) = module.object1(core, "goat_reason_part", parts.len() as u32) {
        if at == 0 {
            break;
        }
        // SAFETY: `at` is a string the module's reason holds, which stays
        // alive until the next refresh.
        let text = unsafe {
            let len = u32::from_le_bytes(*(at as *const u8).add(STR_LEN).cast::<[u8; 4]>());
            std::slice::from_raw_parts((at as *const u8).add(STR_BYTES), len as usize)
        };
        let text = String::from_utf8_lossy(text).into_owned();
        if text.is_empty() {
            break;
        }
        parts.push(text);
    }
    ResetReason::of(parts)
}
