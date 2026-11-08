//! The host side of ADR 0015: instantiate an interactive module, feed it
//! events, and stream each frame it draws to a [`SceneSink`].

use super::{Guest, site_table};
use goat_mir::{Scene, SceneSink};
use std::time::Duration;

const EVENT_PREFIX: &str = "goat_event_";

/// What the host can tell a program (ADR 0015's v1 vocabulary). Keys are the
/// raw `KeyboardEvent.key` text; goat maps the arrows itself.
#[derive(Clone, Debug, PartialEq)]
pub enum Event {
    Tick(f64),
    KeyDown(String),
    KeyUp(String),
    PointerMove { x: f64, y: f64 },
    PointerDown { x: f64, y: f64 },
    PointerUp { x: f64, y: f64 },
}

impl Event {
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

/// What a reload did with the model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reloaded {
    /// The new program's model layout matches, so the running model carried
    /// over.
    Kept,
    /// The layout changed, so the model restarted from the new `init`.
    Reset,
}

/// A running interactive program. Any trap stops it for good: later calls
/// fail, since a half-run `update` leaves no model worth continuing from.
pub struct Interactive<S: SceneSink + 'static> {
    guest: Guest<Scene<S>>,
    model: Option<i32>,
    subscriptions: Vec<String>,
}

impl<S: SceneSink + 'static> Interactive<S> {
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
        })
    }

    /// Swap in a recompiled program, keeping the running model when its
    /// layout fingerprint is unchanged and starting over from the new `init`
    /// when it is not (or when the program had stopped). Both modules must
    /// come from `compile_reloadable`. If the new program cannot start, the
    /// old one is left running.
    pub fn reload(&mut self, wasm: &[u8]) -> Result<Reloaded, String> {
        let guest = &mut self.guest;
        let (old, new) = (guest.instance, guest.spawn(wasm)?);
        let fresh: i32 = guest.on(new, |guest| guest.call("goat_setup", ()))?;
        let same_layout = guest.fingerprint(old)? == guest.fingerprint(new)?;

        let (model, outcome) = match self.model.take() {
            Some(model) if same_layout => {
                guest.on(new, |guest| {
                    guest.call::<_, ()>("goat_release_model", fresh)
                })?;
                (model, Reloaded::Kept)
            }
            Some(model) => {
                guest.on(old, |guest| {
                    guest.call::<_, ()>("goat_release_model", model)
                })?;
                (fresh, Reloaded::Reset)
            }
            None => (fresh, Reloaded::Reset),
        };
        guest.on(old, |guest| guest.call::<_, ()>("goat_shutdown", ()))?;

        guest.instance = new;
        guest.store.data_mut().sites = site_table(wasm);
        self.subscriptions = subscriptions(guest);
        self.model = Some(model);
        Ok(outcome)
    }

    /// The event tags the program handles; the host need only listen for
    /// these.
    pub fn subscriptions(&self) -> &[String] {
        &self.subscriptions
    }

    /// Deliver `event` to `update`. Returns false, doing nothing, if the
    /// program does not handle that kind of event.
    pub fn send(&mut self, event: &Event) -> Result<bool, String> {
        let tag = event.tag();
        if !self.subscriptions.iter().any(|s| s == tag) {
            return Ok(false);
        }
        let model = self.model.take().ok_or(STOPPED)?;
        let constructor = format!("{EVENT_PREFIX}{tag}");
        let guest = &mut self.guest;
        let built: i32 = match event {
            Event::Tick(dt) => guest.call(&constructor, *dt)?,
            Event::KeyDown(key) | Event::KeyUp(key) => {
                let key = guest.string(key)?;
                guest.call(&constructor, key)?
            }
            Event::PointerMove { x, y }
            | Event::PointerDown { x, y }
            | Event::PointerUp { x, y } => guest.call(&constructor, (*x, *y))?,
        };
        self.model = Some(guest.call("goat_update", (model, built))?);
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
