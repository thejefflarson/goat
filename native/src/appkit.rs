//! The macOS window host of `goat build --native` (ADR 0042): Swift and AppKit
//! sources that `goat build` compiles with `swiftc` and links with the
//! program and this crate's staticlib. Swift draws and handles input; the
//! [`session`](crate::session) runs the program, and the header below is all
//! the Swift sees of it.
//!
//! Swift rather than Objective-C: `swiftc` is the linker driver, so the
//! Swift runtime links with no extra step, and the host is native code the
//! same as the editor app's.

/// The C interface between the Swift host and [`crate::session`].
pub const HEADER: (&str, &str) = ("goat_host.h", include_str!("../appkit/goat_host.h"));

/// The Swift files of the host, by file name.
pub const SWIFT: [(&str, &str); 7] = [
    ("Color.swift", include_str!("../appkit/Color.swift")),
    ("Frame.swift", include_str!("../appkit/Frame.swift")),
    ("Headless.swift", include_str!("../appkit/Headless.swift")),
    ("Link.swift", include_str!("../appkit/Link.swift")),
    ("Painter.swift", include_str!("../appkit/Painter.swift")),
    ("Window.swift", include_str!("../appkit/Window.swift")),
    ("main.swift", include_str!("../appkit/main.swift")),
];
