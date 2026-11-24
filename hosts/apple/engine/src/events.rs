//! What the host tells an interactive program. The turtle and the canvas name
//! their events differently but build them the same way, so one event type
//! carries the vocabulary's tag.

use goat::Host;
use goat::native::{Guest, HostEvent};
use goat_detect::Vocabulary;

/// The names of the events the host can send, in one vocabulary.
#[derive(Clone, Copy)]
pub struct Tags {
    tick: &'static str,
    key_down: &'static str,
    key_up: &'static str,
    pointer_move: &'static str,
    pointer_down: &'static str,
    pointer_up: &'static str,
}

const TURTLE: Tags = Tags {
    tick: "Tick",
    key_down: "KeyDown",
    key_up: "KeyUp",
    pointer_move: "PointerMove",
    pointer_down: "PointerDown",
    pointer_up: "PointerUp",
};

const CANVAS: Tags = Tags {
    tick: "Frame",
    key_down: "KeyPress",
    key_up: "KeyRelease",
    pointer_move: "MouseMove",
    pointer_down: "MousePress",
    pointer_up: "MouseRelease",
};

impl Tags {
    pub fn of(vocabulary: Vocabulary) -> Tags {
        match vocabulary {
            Vocabulary::Turtle => TURTLE,
            Vocabulary::Canvas => CANVAS,
        }
    }

    pub fn tick(self, milliseconds: f64) -> EngineEvent {
        EngineEvent::new(self.tick, Payload::Elapsed(milliseconds))
    }

    pub fn key(self, key: &str, down: bool) -> EngineEvent {
        let tag = if down { self.key_down } else { self.key_up };
        EngineEvent::new(tag, Payload::Key(key.to_string()))
    }

    pub fn pointer(self, kind: Pointer, x: f64, y: f64) -> EngineEvent {
        let tag = match kind {
            Pointer::Move => self.pointer_move,
            Pointer::Down => self.pointer_down,
            Pointer::Up => self.pointer_up,
        };
        EngineEvent::new(tag, Payload::At(x, y))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pointer {
    Move,
    Down,
    Up,
}

enum Payload {
    Elapsed(f64),
    Key(String),
    At(f64, f64),
}

pub struct EngineEvent {
    tag: &'static str,
    payload: Payload,
}

impl EngineEvent {
    fn new(tag: &'static str, payload: Payload) -> EngineEvent {
        EngineEvent { tag, payload }
    }
}

impl HostEvent for EngineEvent {
    fn tag(&self) -> &'static str {
        self.tag
    }

    fn construct<H: Host + 'static>(
        &self,
        guest: &mut Guest<H>,
        constructor: &str,
    ) -> Result<i32, String> {
        match &self.payload {
            Payload::Elapsed(ms) => guest.call(constructor, *ms),
            Payload::Key(key) => {
                let key = guest.string(key)?;
                guest.call(constructor, key)
            }
            Payload::At(x, y) => guest.call(constructor, (*x, *y)),
        }
    }
}
