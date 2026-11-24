//! The engine a host holds: commands go to a worker thread that owns the
//! wasmtime store, and what the worker says comes back through an outbox a
//! delivery thread drains into the host's [`Sink`]. A caller never waits on
//! the worker, and a slow sink costs the worker nothing but frames.

use crate::events::Pointer;
use crate::worker;
use std::collections::VecDeque;
use std::sync::mpsc::{Sender, channel};
use std::sync::{Arc, Condvar, Mutex, MutexGuard, PoisonError};
use std::time::Duration;

/// Where the engine's messages go. Calls arrive one at a time from the
/// delivery thread, and none arrives once the engine has been dropped.
pub trait Sink: Send + 'static {
    /// An `EngineMessage`, as JSON.
    fn control(&mut self, json: &str);
    /// The bytes of one `scene.frame`.
    fn frame(&mut self, bytes: &[u8]);
    /// The engine is gone; this is the last call.
    fn closed(&mut self);
}

/// What a program may spend: time for each call into goat, and heap.
#[derive(Clone, Copy, Debug)]
pub struct Budgets {
    /// `update` or `draw`, one frame's worth of work.
    pub frame: Duration,
    /// Setup, a reload, or a whole run-once program.
    pub once: Duration,
    /// The most bytes the program's heap may grow to.
    pub heap: usize,
}

impl Default for Budgets {
    fn default() -> Budgets {
        Budgets {
            frame: Duration::from_secs(1),
            once: Duration::from_secs(10),
            heap: 128 << 20,
        }
    }
}

pub(crate) enum Command {
    Run(String),
    Stop,
    Key { key: String, down: bool },
    Pointer { kind: Pointer, x: f64, y: f64 },
    Shutdown,
}

enum Item {
    Control(String),
    Frame(Vec<u8>),
}

#[derive(Default)]
struct Queue {
    items: VecDeque<Item>,
    closed: bool,
}

/// What the worker has said and the host has not yet heard. A frame replaces
/// any frame still waiting, so a slow host sees the newest picture, never a
/// backlog.
#[derive(Default)]
pub(crate) struct Outbox {
    queue: Mutex<Queue>,
    ready: Condvar,
}

fn locked<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

impl Outbox {
    pub fn control(&self, json: String) {
        self.push(Item::Control(json));
    }

    pub fn frame(&self, bytes: Vec<u8>) {
        self.push(Item::Frame(bytes));
    }

    fn push(&self, item: Item) {
        let mut queue = locked(&self.queue);
        if matches!(item, Item::Frame(_)) {
            queue
                .items
                .retain(|waiting| !matches!(waiting, Item::Frame(_)));
        }
        queue.items.push_back(item);
        self.ready.notify_one();
    }

    fn close(&self) {
        locked(&self.queue).closed = true;
        self.ready.notify_all();
    }

    fn next(&self) -> Option<Item> {
        let mut queue = locked(&self.queue);
        loop {
            if queue.closed {
                return None;
            }
            if let Some(item) = queue.items.pop_front() {
                return Some(item);
            }
            queue = self
                .ready
                .wait(queue)
                .unwrap_or_else(PoisonError::into_inner);
        }
    }
}

type SharedSink = Arc<Mutex<Option<Box<dyn Sink>>>>;

fn deliver(outbox: &Outbox, sink: &Mutex<Option<Box<dyn Sink>>>) {
    while let Some(item) = outbox.next() {
        let mut held = locked(sink);
        let Some(sink) = held.as_mut() else { return };
        match item {
            Item::Control(json) => sink.control(&json),
            Item::Frame(bytes) => sink.frame(&bytes),
        }
    }
}

/// A goat engine. Dropping it stops its program, delivers `closed`, and
/// guarantees the sink is never called again; the worker thread winds down on
/// its own once any call in flight has been stopped by its budget.
pub struct Engine {
    commands: Sender<Command>,
    outbox: Arc<Outbox>,
    sink: SharedSink,
}

impl Engine {
    pub fn new(sink: impl Sink) -> Engine {
        Engine::with_budgets(sink, Budgets::default())
    }

    pub fn with_budgets(sink: impl Sink, budgets: Budgets) -> Engine {
        let (commands, receiver) = channel();
        let outbox = Arc::new(Outbox::default());
        let sink: SharedSink = Arc::new(Mutex::new(Some(Box::new(sink))));
        let (worker_outbox, deliver_outbox, deliver_sink) =
            (Arc::clone(&outbox), Arc::clone(&outbox), Arc::clone(&sink));
        std::thread::Builder::new()
            .name("goat-engine".into())
            .spawn(move || worker::work(receiver, worker_outbox, budgets))
            .expect("spawn the engine's worker thread");
        std::thread::Builder::new()
            .name("goat-engine-delivery".into())
            .spawn(move || deliver(&deliver_outbox, &deliver_sink))
            .expect("spawn the engine's delivery thread");
        Engine {
            commands,
            outbox,
            sink,
        }
    }

    fn send(&self, command: Command) {
        let _ = self.commands.send(command);
    }

    /// Compile and run `source`. While an interactive program is live, a new
    /// interactive source reloads it instead (ADR 0035).
    pub fn run(&self, source: &str) {
        self.send(Command::Run(source.to_string()));
    }

    pub fn stop(&self) {
        self.send(Command::Stop);
    }

    /// A key, named as `KeyboardEvent.key` names it.
    pub fn key(&self, key: &str, down: bool) {
        self.send(Command::Key {
            key: key.to_string(),
            down,
        });
    }

    /// A pointer event at (`x`, `y`) in the canvas's own coordinates.
    pub fn pointer(&self, kind: Pointer, x: f64, y: f64) {
        self.send(Command::Pointer { kind, x, y });
    }
}

impl Drop for Engine {
    fn drop(&mut self) {
        self.send(Command::Shutdown);
        self.outbox.close();
        if let Some(mut sink) = locked(&self.sink).take() {
            sink.closed();
        }
    }
}
