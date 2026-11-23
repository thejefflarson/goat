//! The native host library for goat's LLVM backend (ADR 0042). Native only: it
//! runs clang and `dlopen`s, so it stays out of the compiler crates' wasm32
//! build.
//!
//! - [`abi`] mirrors the `goat_host` table and the `goat_instance` the
//!   generated code reads.
//! - [`adapter`] serves a table from any Rust [`goat::Host`].
//! - [`driver`] builds emitted IR into a shared library and runs it.

pub mod abi;
pub mod adapter;
pub mod driver;

pub use driver::{Library, NativeError, Run, Stopped, Versions, clang_available};

use goat::{GoatError, HostInterface, Profile};
use std::fmt;

/// Why a program did not become a library.
#[derive(Debug)]
pub enum BuildError {
    /// The compiler rejected the source, or the backend does not cover a
    /// construct in it yet.
    Compile(Vec<GoatError>),
    Native(NativeError),
}

impl BuildError {
    /// The reason, when the backend does not cover something in the program.
    pub fn unsupported(&self) -> Option<String> {
        match self {
            BuildError::Compile(errors) => errors
                .iter()
                .map(|e| e.to_string())
                .find(|message| message.contains("not yet supported by the native backend")),
            BuildError::Native(_) => None,
        }
    }
}

impl fmt::Display for BuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BuildError::Compile(errors) => {
                let rendered: Vec<_> = errors.iter().map(|e| e.to_string()).collect();
                write!(f, "{}", rendered.join("\n"))
            }
            BuildError::Native(e) => e.fmt(f),
        }
    }
}

impl std::error::Error for BuildError {}

/// Compiles `source` for the native backend and loads it.
pub fn build(profile: Profile, source: &str, host: &HostInterface) -> Result<Library, BuildError> {
    let ll = goat::compile_ll(profile, source, host).map_err(BuildError::Compile)?;
    Library::build(&ll).map_err(BuildError::Native)
}
