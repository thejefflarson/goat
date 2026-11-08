//! The host side of ADR 0015: instantiate an interactive module, feed it
//! events, and stream each frame it draws to a [`SceneSink`].

use super::Guest;
use goat_mir::{Scene, SceneSink};

/// The fuel refilled before every call into goat, so a runaway `update`
/// traps instead of hanging the host.
pub const UPDATE_FUEL: i32 = 5_000_000;

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
        let mut guest = Guest::new(wasm, Scene(sink))?;
        let subscriptions = guest
            .exports()
            .iter()
            .filter_map(|name| name.strip_prefix(EVENT_PREFIX).map(str::to_string))
            .collect();
        let model = call(&mut guest, "goat_setup", ())?;
        Ok(Interactive {
            guest,
            model: Some(model),
            subscriptions,
        })
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
            Event::Tick(dt) => call(guest, &constructor, *dt)?,
            Event::KeyDown(key) | Event::KeyUp(key) => {
                let key = guest.string(key)?;
                call(guest, &constructor, key)?
            }
            Event::PointerMove { x, y }
            | Event::PointerDown { x, y }
            | Event::PointerUp { x, y } => call(guest, &constructor, (*x, *y))?,
        };
        self.model = Some(call(guest, "goat_update", (model, built))?);
        Ok(true)
    }

    /// Stream the current picture to the sink as one frame.
    pub fn draw(&mut self) -> Result<(), String> {
        let model = self.model.ok_or(STOPPED)?;
        let drawn = call(&mut self.guest, "goat_draw", model);
        if drawn.is_err() {
            self.model = None;
        }
        drawn
    }

    /// Tear the program down and hand back the sink with the heap blocks
    /// still allocated, which is zero for a correct program.
    pub fn finish(mut self) -> Result<(S, u32), String> {
        let model = self.model.ok_or(STOPPED)?;
        call::<_, _, ()>(&mut self.guest, "goat_release_model", model)?;
        call::<_, _, ()>(&mut self.guest, "goat_shutdown", ())?;
        let live = self.guest.live_allocs()?;
        Ok((self.guest.into_host().0, live))
    }

    /// Give up on the program, returning the sink without tearing it down.
    pub fn into_sink(self) -> S {
        self.guest.into_host().0
    }
}

const STOPPED: &str = "the program has stopped";

/// Call an export with a full tank of fuel, saying so if the call ran dry.
fn call<S: SceneSink + 'static, P: wasmtime::WasmParams, R: wasmtime::WasmResults>(
    guest: &mut Guest<Scene<S>>,
    name: &str,
    args: P,
) -> Result<R, String> {
    guest.set_fuel(UPDATE_FUEL)?;
    guest.call(name, args).map_err(|error| {
        if guest.fuel().is_ok_and(|left| left <= 0) {
            format!("{name} ran out of fuel, so the program looks stuck: {error}")
        } else {
            error
        }
    })
}
