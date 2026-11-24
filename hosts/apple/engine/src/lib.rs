//! The goat engine the Apple apps embed (ADR 0043): a program is compiled and
//! run in-process on wasmtime's Pulley interpreter, behind the C header
//! `include/goat_engine.h`. Native only; the compiler crates stay wasm32-clean
//! and this one is not among them.

mod engine;
mod events;
mod ffi;
mod protocol;
mod turtle;
mod worker;

pub use engine::{Budgets, Engine, Sink};
pub use events::Pointer;
pub use ffi::*;
