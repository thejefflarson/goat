//! A p5-style canvas host. A script defines `init`, `update` and `draw`
//! (ADR 0015); the host feeds `update` canvas events and renders the picture
//! `draw` returns. Goat issues no drawing calls: the picture is data.
//!
//! The vocabulary is the canvas's own (`Frame`, `MousePress`, `Dot`, `Box`, ...)
//! and its shapes ride the turtle's `scene.*` wire protocol unchanged.

mod vocab;

#[cfg(feature = "native")]
mod native;

use goat::HostInterface;

#[cfg(feature = "native")]
pub use native::*;
pub use vocab::vocab;

pub fn interface() -> HostInterface {
    HostInterface::with_vocab(goat_checker::STDLIB, vocab())
}

/// Compile `source` against the canvas vocabulary, rendering errors with spans.
pub fn compile(source: &str) -> Result<Vec<u8>, String> {
    goat::compile(source, &interface()).map_err(|errors| {
        let rendered: Vec<String> = errors.iter().map(|e| e.render(source)).collect();
        rendered.join("\n")
    })
}
