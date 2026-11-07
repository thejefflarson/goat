//! The host side of `foreign` functions, as the interpreter and the wasmtime
//! CLI both see it: a value that crosses the boundary, and the functions a
//! host provides. One implementation serves both, so a differential test can
//! run a program with a foreign call on each backend and compare.

use goat_checker::hir::Boundary;

/// A value crossing the host boundary. A string is copied: the host never
/// keeps goat's pointer.
#[derive(Debug, Clone, PartialEq)]
pub enum HostValue {
    Number(f64),
    Bool(bool),
    Unit,
    Str(String),
}

pub trait Host {
    /// The type of the function `name` in `module`, or `None` if the host
    /// does not provide it. Compiled code only carries wasm value types, so a
    /// wasm host needs this to tell a `Bool` from a `String` pointer.
    fn signature(&self, module: &str, name: &str) -> Option<(Vec<Boundary>, Boundary)>;

    /// Run `module.name` on `args`; an error traps the program.
    fn call(&mut self, module: &str, name: &str, args: &[HostValue]) -> Result<HostValue, String>;
}

/// The host of a program that calls nothing foreign.
pub struct NoHost;

impl Host for NoHost {
    fn signature(&self, _: &str, _: &str) -> Option<(Vec<Boundary>, Boundary)> {
        None
    }

    fn call(&mut self, module: &str, name: &str, _: &[HostValue]) -> Result<HostValue, String> {
        Err(format!("no host function {module}.{name}"))
    }
}
