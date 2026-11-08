//! The `goat` binary's library half: the turtle host, plus the wasmtime driver
//! (`goat::native`) re-exported for the differential tests.

pub use goat::native::{Finished, Guest, Run, Stopped, execute, run, run_to_end, run_with_host};

pub mod turtle;
