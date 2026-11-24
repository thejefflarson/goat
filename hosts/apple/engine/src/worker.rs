//! The worker thread: the only code that touches the wasmtime store. It runs
//! on Pulley (no executable memory, so it works on iOS), steps a live
//! program at about 60 frames a second, and throws the store away after any
//! trap, since a half-run `update` leaves no model worth continuing from.

use crate::engine::{Budgets, Command, Outbox};
use crate::events::{EngineEvent, Tags};
use crate::protocol::{self, State};
use crate::turtle::{Drawing, TurtleHost};
use goat::native::{Interactive, build_engine, engine_config, pulley, run_to_end_in};
use goat::{GoatError, LiveProgram, SceneSink};
use goat_detect::Vocabulary;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;
use std::sync::mpsc::{Receiver, RecvTimeoutError};
use std::time::{Duration, Instant};

const FRAME_INTERVAL: Duration = Duration::from_millis(16);

const HAS_PROBLEMS: &str = "your program has problems";

/// A sink that wants the frame's bytes and nothing else.
struct FrameSink(Arc<Outbox>);

impl SceneSink for FrameSink {
    fn begin(&mut self) {}
    fn end(&mut self) {}
    fn line(&mut self, _: (f64, f64), _: (f64, f64), _: &str) {}
    fn polyline_begin(&mut self, _: &str) {}
    fn vertex(&mut self, _: f64, _: f64) {}
    fn polyline_end(&mut self) {}
    fn circle(&mut self, _: (f64, f64), _: f64, _: &str) {}
    fn rect(&mut self, _: (f64, f64), _: (f64, f64), _: &str) {}
    fn text(&mut self, _: (f64, f64), _: &str, _: &str) {}

    fn frame(&mut self, bytes: &[u8]) -> Result<(), String> {
        self.0.frame(bytes.to_vec());
        Ok(())
    }
}

struct Live {
    program: Interactive<FrameSink, EngineEvent>,
    tags: Tags,
    last_tick: Option<Instant>,
    next_tick: Instant,
}

enum Active {
    Idle,
    Live(Box<Live>),
    /// A run-once drawing being shown, and when its next frame is due.
    Paced(Drawing, Instant),
}

struct Worker {
    wasm: wasmtime::Engine,
    outbox: Arc<Outbox>,
    budgets: Budgets,
    active: Active,
    showing_problems: bool,
}

fn engine() -> Result<wasmtime::Engine, String> {
    let mut config = engine_config();
    pulley(&mut config).map_err(|e| format!("pulley: {e}"))?;
    build_engine(&config)
}

pub(crate) fn work(commands: Receiver<Command>, outbox: Arc<Outbox>, budgets: Budgets) {
    let wasm = match engine() {
        Ok(wasm) => wasm,
        Err(message) => {
            outbox.control(protocol::state(State::Failed, Some(&message)));
            return;
        }
    };
    outbox.control(protocol::ready());
    let mut worker = Worker {
        wasm,
        outbox,
        budgets,
        active: Active::Idle,
        showing_problems: false,
    };
    loop {
        let mut batch = Vec::new();
        let first = match worker.due() {
            None => commands.recv().map_err(|_| RecvTimeoutError::Disconnected),
            Some(due) => commands.recv_timeout(due.saturating_duration_since(Instant::now())),
        };
        match first {
            Ok(command) => batch.push(command),
            Err(RecvTimeoutError::Timeout) => {}
            Err(RecvTimeoutError::Disconnected) => return,
        }
        batch.extend(commands.try_iter());
        let stepped = catch_unwind(AssertUnwindSafe(|| {
            let running = worker.handle(batch);
            if running {
                worker.tick();
            }
            running
        }));
        match stepped {
            Ok(true) => {}
            Ok(false) => return,
            Err(_) => worker.fail("goat stopped unexpectedly"),
        }
    }
}

impl Worker {
    fn post(&self, json: String) {
        self.outbox.control(json);
    }

    /// When the next frame is due, if a program is on screen.
    fn due(&self) -> Option<Instant> {
        match &self.active {
            Active::Idle => None,
            Active::Live(live) => Some(live.next_tick),
            Active::Paced(_, due) => Some(*due),
        }
    }

    /// Carry out `commands` in order, except that a run another run follows
    /// is skipped. False once the engine is told to shut down.
    fn handle(&mut self, commands: Vec<Command>) -> bool {
        let last_run = commands.iter().rposition(|c| matches!(c, Command::Run(_)));
        for (at, command) in commands.into_iter().enumerate() {
            match command {
                Command::Run(source) if Some(at) == last_run => self.run(&source),
                Command::Run(_) => {}
                Command::Stop => self.active = Active::Idle,
                Command::Key { key, down } => self.send(|tags| tags.key(&key, down)),
                Command::Pointer { kind, x, y } => self.send(|tags| tags.pointer(kind, x, y)),
                Command::Shutdown => return false,
            }
        }
        true
    }

    fn run(&mut self, source: &str) {
        let vocabulary = match goat_detect::detect(source) {
            Ok(vocabulary) => vocabulary,
            Err(error) => return self.reject(&[error], source),
        };
        let live = match goat::compile_live_program(source, &vocabulary.interface()) {
            Ok(live) => live,
            Err(errors) => return self.reject(&errors, source),
        };
        if std::mem::take(&mut self.showing_problems) {
            self.post(protocol::diagnostics(&[], source));
        }
        if live.interactive && matches!(self.active, Active::Live(_)) {
            self.reload(&live.wasm, vocabulary);
        } else {
            self.start(live, vocabulary);
        }
    }

    /// A program that does not compile. One already running is left running,
    /// so a half-typed edit does not take the picture away.
    fn reject(&mut self, errors: &[GoatError], source: &str) {
        self.showing_problems = true;
        self.post(protocol::diagnostics(errors, source));
        if !matches!(self.active, Active::Live(_)) {
            self.active = Active::Idle;
            self.post(protocol::state(State::Failed, Some(HAS_PROBLEMS)));
        }
    }

    fn start(&mut self, live: LiveProgram, vocabulary: Vocabulary) {
        self.active = Active::Idle;
        self.post(protocol::state(State::Running, None));
        if live.interactive {
            let sink = FrameSink(Arc::clone(&self.outbox));
            let started = Interactive::in_engine(
                &self.wasm,
                &live.wasm,
                sink,
                self.budgets.once,
                Some(self.budgets.heap),
            );
            match started {
                Ok(mut program) => {
                    program.set_timeout(self.budgets.frame);
                    self.active = Active::Live(Box::new(Live {
                        program,
                        tags: Tags::of(vocabulary),
                        last_tick: None,
                        next_tick: Instant::now(),
                    }));
                    self.flush_output();
                }
                Err(message) => self.fail(&message),
            }
            return;
        }
        let finished = run_to_end_in(
            &self.wasm,
            &live.wasm,
            TurtleHost::default(),
            Some(self.budgets.once),
            Some(self.budgets.heap),
        );
        match finished {
            Err(message) => self.fail(&message),
            Ok(finished) => {
                if !finished.printed.is_empty() {
                    self.post(protocol::output(&finished.printed));
                }
                match finished.result {
                    Err(stopped) => self.fail(&stopped.message),
                    Ok(_) => {
                        self.active = Active::Paced(finished.host.into_drawing(), Instant::now())
                    }
                }
            }
        }
    }

    fn reload(&mut self, wasm: &[u8], vocabulary: Vocabulary) {
        let Active::Live(live) = &mut self.active else {
            return;
        };
        live.program.set_timeout(self.budgets.once);
        let reloaded = live.program.reload(wasm);
        live.program.set_timeout(self.budgets.frame);
        live.tags = Tags::of(vocabulary);
        match reloaded {
            Ok(outcome) => {
                self.post(protocol::reloaded(&outcome));
                self.flush_output();
            }
            Err(message) => self.fail(&message),
        }
    }

    fn send(&mut self, event: impl FnOnce(Tags) -> EngineEvent) {
        let Active::Live(live) = &mut self.active else {
            return;
        };
        let sent = live.program.send(&event(live.tags)).map(|_| ());
        self.after_call(sent);
    }

    /// Show whatever is due: a live program's next frame, or a drawing's.
    fn tick(&mut self) {
        let now = Instant::now();
        match &mut self.active {
            Active::Live(live) if now >= live.next_tick => {
                let elapsed = live
                    .last_tick
                    .map_or(0.0, |last| (now - last).as_secs_f64() * 1e3);
                (live.last_tick, live.next_tick) = (Some(now), now + FRAME_INTERVAL);
                let stepped = live
                    .program
                    .send(&live.tags.tick(elapsed))
                    .and_then(|_| live.program.draw());
                self.after_call(stepped);
            }
            Active::Paced(drawing, due) if now >= *due => {
                let (frame, last) = drawing.next_frame();
                *due = now + FRAME_INTERVAL;
                self.outbox.frame(frame);
                if last {
                    self.active = Active::Idle;
                    self.post(protocol::state(State::Finished, None));
                }
            }
            _ => {}
        }
    }

    fn after_call(&mut self, result: Result<(), String>) {
        self.flush_output();
        if let Err(message) = result {
            self.fail(&message);
        }
    }

    fn flush_output(&mut self) {
        let Active::Live(live) = &mut self.active else {
            return;
        };
        let lines = live.program.take_output();
        if !lines.is_empty() {
            self.post(protocol::output(&lines));
        }
    }

    /// Discard the store and tell the host why; the next run starts fresh.
    fn fail(&mut self, message: &str) {
        self.flush_output();
        self.active = Active::Idle;
        let text = format!("your program stopped: {}", plain(message));
        self.post(protocol::state(State::Failed, Some(&text)));
    }
}

/// The message without the name of the export it came from: `goat_update
/// trapped: boom` is `boom` to the person who wrote the program.
fn plain(message: &str) -> &str {
    ["trapped", "stopped"]
        .iter()
        .find_map(|verb| {
            let (export, rest) = message.split_once(&format!(" {verb}: "))?;
            (export.starts_with("goat_") && !export.contains(' ')).then_some(rest)
        })
        .unwrap_or(message)
}

#[cfg(test)]
mod tests {
    use super::plain;

    #[test]
    fn the_export_name_is_dropped_from_a_stop_message() {
        assert_eq!(plain("goat_update trapped: boom"), "boom");
        assert_eq!(
            plain("goat_draw stopped: the program ran for more than 5 ms, so it looks stuck"),
            "the program ran for more than 5 ms, so it looks stuck"
        );
        assert_eq!(plain("invalid module: nope"), "invalid module: nope");
        assert_eq!(plain("a b trapped: c"), "a b trapped: c");
    }
}
