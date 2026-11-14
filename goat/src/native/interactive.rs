//! The host side of ADR 0015: instantiate an interactive module, feed it
//! events, and stream each frame it draws to a [`SceneSink`].

use super::{Guest, site_table};
use crate::{Host, Scene, SceneSink};
use std::marker::PhantomData;
use std::time::{Duration, Instant};

const EVENT_PREFIX: &str = "goat_event_";

/// An event a host can send: the tag of the `goat_event_<Tag>` constructor the
/// program exports for it, and how to build the event value in the guest. The
/// vocabulary's event set (ADR 0020) is the implementor's.
pub trait HostEvent {
    fn tag(&self) -> &'static str;

    /// Call `constructor` on `guest` with this event's payload, returning the
    /// event object it builds.
    fn construct<H: Host + 'static>(
        &self,
        guest: &mut Guest<H>,
        constructor: &str,
    ) -> Result<i32, String>;
}

/// What the host can tell a turtle program (ADR 0015's v1 vocabulary). Keys
/// are the raw `KeyboardEvent.key` text; goat maps the arrows itself.
#[derive(Clone, Debug, PartialEq)]
pub enum Event {
    Tick(f64),
    KeyDown(String),
    KeyUp(String),
    PointerMove { x: f64, y: f64 },
    PointerDown { x: f64, y: f64 },
    PointerUp { x: f64, y: f64 },
}

impl HostEvent for Event {
    fn construct<H: Host + 'static>(
        &self,
        guest: &mut Guest<H>,
        constructor: &str,
    ) -> Result<i32, String> {
        match self {
            Event::Tick(dt) => guest.call(constructor, *dt),
            Event::KeyDown(key) | Event::KeyUp(key) => {
                let key = guest.string(key)?;
                guest.call(constructor, key)
            }
            Event::PointerMove { x, y }
            | Event::PointerDown { x, y }
            | Event::PointerUp { x, y } => guest.call(constructor, (*x, *y)),
        }
    }

    fn tag(&self) -> &'static str {
        match self {
            Event::Tick(_) => "Tick",
            Event::KeyDown(_) => "KeyDown",
            Event::KeyUp(_) => "KeyUp",
            Event::PointerMove { .. } => "PointerMove",
            Event::PointerDown { .. } => "PointerDown",
            Event::PointerUp { .. } => "PointerUp",
        }
    }
}

/// What a reload did with the model (ADR 0035).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reloaded {
    /// The running model carried across by name, its methods rebound to the
    /// new program's.
    Refreshed,
    /// The model restarted from the new `init`, and why.
    Reset(ResetReason),
}

/// Why a reload started the model over: a kind such as `field_added` or
/// `method_captures`, and the names it carries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResetReason {
    pub kind: String,
    pub args: Vec<String>,
}

impl ResetReason {
    pub(super) fn of(parts: Vec<String>) -> ResetReason {
        let mut parts = parts.into_iter();
        ResetReason {
            kind: parts.next().unwrap_or_else(|| "reshaped".into()),
            args: parts.collect(),
        }
    }

    fn reshaped() -> ResetReason {
        ResetReason::of(Vec::new())
    }
}

/// A running interactive program. Any trap stops it for good: later calls
/// fail, since a half-run `update` leaves no model worth continuing from.
/// `E` is the host's event type; the default is the turtle's.
pub struct Interactive<S: SceneSink + 'static, E: HostEvent = Event> {
    guest: Guest<Scene<S>>,
    model: Option<i32>,
    subscriptions: Vec<String>,
    events: PhantomData<fn(&E)>,
    carried: Duration,
}

impl<S: SceneSink + 'static, E: HostEvent> Interactive<S, E> {
    /// Instantiate `wasm` and run its top-level code, which yields the first
    /// model.
    pub fn new(wasm: &[u8], sink: S) -> Result<Self, String> {
        Self::start(Guest::new(wasm, Scene(sink))?)
    }

    /// Like `new`, but each call into the program (setup, every event's
    /// `update`, every `draw`) is stopped with a trap if it runs longer than
    /// `timeout`.
    pub fn with_timeout(wasm: &[u8], sink: S, timeout: Duration) -> Result<Self, String> {
        Self::start(Guest::with_timeout(wasm, Scene(sink), timeout)?)
    }

    fn start(mut guest: Guest<Scene<S>>) -> Result<Self, String> {
        let subscriptions = subscriptions(&mut guest);
        let model = guest.call("goat_setup", ())?;
        Ok(Interactive {
            guest,
            model: Some(model),
            subscriptions,
            events: PhantomData,
            carried: Duration::ZERO,
        })
    }

    /// Swap in a recompiled program over the same heap (ADR 0035). The old
    /// module snapshots the model, the new one refreshes a model of its own
    /// types from the snapshot, and the old module's code and static data are
    /// freed. A model that cannot be refreshed restarts from the new `init`
    /// (or when the program had stopped), and the reason says why. Both
    /// modules must come from `compile_reloadable`. If the new program cannot
    /// start, the old one is left running.
    pub fn reload(&mut self, wasm: &[u8]) -> Result<Reloaded, String> {
        let guest = &mut self.guest;
        let (old, new) = (guest.instance, guest.spawn(wasm)?);
        let fresh: i32 = guest.on(new, |guest| guest.call("goat_setup", ()))?;

        let (model, outcome) = match self.model.take() {
            None => (fresh, Reloaded::Reset(ResetReason::reshaped())),
            Some(model) => {
                let started = Instant::now();
                // The snapshot consumes the model, so the old module is not
                // asked to release it.
                let image = guest.on(old, |guest| guest.call::<_, i32>("goat_snapshot", model));
                let refreshed = image.and_then(|image| {
                    guest.on(new, |guest| {
                        guest.call::<_, i32>("goat_refresh", (image, fresh))
                    })
                });
                self.carried = started.elapsed();
                match refreshed {
                    Ok(0) => {
                        let reason = guest.on(new, |guest| guest.reason());
                        (fresh, Reloaded::Reset(reason))
                    }
                    Ok(rebuilt) => {
                        guest.on(new, |guest| {
                            guest.call::<_, ()>("goat_release_model", fresh)
                        })?;
                        (rebuilt, Reloaded::Refreshed)
                    }
                    Err(_) => (fresh, Reloaded::Reset(ResetReason::reshaped())),
                }
            }
        };
        guest.on(old, |guest| guest.call::<_, ()>("goat_shutdown", ()))?;
        guest.on(old, |guest| guest.call::<_, ()>("goat_free_static", ()))?;

        guest.instance = new;
        guest.store.data_mut().sites = site_table(wasm);
        self.subscriptions = subscriptions(guest);
        self.model = Some(model);
        Ok(outcome)
    }

    /// How long the last reload spent in the old module's snapshot and the new
    /// module's refresh: the part of a reload that grows with the model, and
    /// the part a host's per-call budget applies to.
    pub fn carry_time(&self) -> Duration {
        self.carried
    }

    /// The event tags the program handles; the host need only listen for
    /// these.
    pub fn subscriptions(&self) -> &[String] {
        &self.subscriptions
    }

    /// Deliver `event` to `update`. Returns false, doing nothing, if the
    /// program does not handle that kind of event.
    pub fn send(&mut self, event: &E) -> Result<bool, String> {
        let tag = event.tag();
        if !self.subscriptions.iter().any(|s| s == tag) {
            return Ok(false);
        }
        let model = self.model.take().ok_or(STOPPED)?;
        let built = event.construct(&mut self.guest, &format!("{EVENT_PREFIX}{tag}"))?;
        self.model = Some(self.guest.call("goat_update", (model, built))?);
        Ok(true)
    }

    /// Stream the current picture to the sink as one frame.
    pub fn draw(&mut self) -> Result<(), String> {
        let model = self.model.ok_or(STOPPED)?;
        let drawn = self.guest.call("goat_draw", model);
        if drawn.is_err() {
            self.model = None;
        }
        drawn
    }

    /// Tear the program down and hand back the sink with the heap blocks
    /// still allocated, which is zero for a correct program.
    pub fn finish(mut self) -> Result<(S, u32), String> {
        let model = self.model.ok_or(STOPPED)?;
        self.guest.call::<_, ()>("goat_release_model", model)?;
        self.guest.call::<_, ()>("goat_shutdown", ())?;
        let live = self.guest.live_allocs()?;
        Ok((self.guest.into_host().0, live))
    }

    /// Heap blocks allocated and not yet freed, the model's among them.
    pub fn live_allocs(&mut self) -> Result<u32, String> {
        self.guest.live_allocs()
    }

    /// How far the heap has grown, in bytes; see [`Guest::heap_end`].
    pub fn heap_end(&mut self) -> Result<u32, String> {
        self.guest.heap_end()
    }

    /// The sink the frames stream to.
    pub fn sink_mut(&mut self) -> &mut S {
        &mut self.guest.host_mut().0
    }

    /// Give up on the program, returning the sink without tearing it down.
    pub fn into_sink(self) -> S {
        self.guest.into_host().0
    }
}

fn subscriptions<S: SceneSink + 'static>(guest: &mut Guest<Scene<S>>) -> Vec<String> {
    guest
        .exports()
        .iter()
        .filter_map(|name| name.strip_prefix(EVENT_PREFIX).map(str::to_string))
        .collect()
}

const STOPPED: &str = "the program has stopped";
