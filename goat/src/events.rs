//! What a host sends an interactive program and what a reload reports: the
//! values both execution backends share.

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

impl Event {
    pub fn tag(&self) -> &'static str {
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
    pub fn of(parts: Vec<String>) -> ResetReason {
        let mut parts = parts.into_iter();
        ResetReason {
            kind: parts.next().unwrap_or_else(|| "reshaped".into()),
            args: parts.collect(),
        }
    }

    pub fn reshaped() -> ResetReason {
        ResetReason::of(Vec::new())
    }
}
