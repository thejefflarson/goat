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
    Int(i64),
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

/// One call an interactive program's `draw` makes to the `scene.*` imports, in
/// the order it made them.
#[derive(Debug, Clone, PartialEq)]
pub enum SceneCommand {
    Begin,
    End,
    Line {
        from: (f64, f64),
        to: (f64, f64),
        color: String,
    },
    PolylineBegin(String),
    Vertex(f64, f64),
    PolylineEnd,
}

/// The host of an interactive program's picture: it records the scene the
/// program streams, so the interpreter and wasmtime can be compared command
/// for command.
#[derive(Debug, Default)]
pub struct SceneHost {
    pub commands: Vec<SceneCommand>,
}

impl Host for SceneHost {
    fn signature(&self, module: &str, name: &str) -> Option<(Vec<Boundary>, Boundary)> {
        use Boundary::{Number, Str, Unit};
        if module != "scene" {
            return None;
        }
        Some(match name {
            "begin" | "end" | "polyline_end" => (vec![], Unit),
            "line" => (vec![Number, Number, Number, Number, Str], Unit),
            "polyline_begin" => (vec![Str], Unit),
            "vertex" => (vec![Number, Number], Unit),
            _ => return None,
        })
    }

    fn call(&mut self, _: &str, name: &str, args: &[HostValue]) -> Result<HostValue, String> {
        use HostValue::{Number, Str};
        let command = match (name, args) {
            ("begin", []) => SceneCommand::Begin,
            ("end", []) => SceneCommand::End,
            ("line", [Number(x1), Number(y1), Number(x2), Number(y2), Str(color)]) => {
                SceneCommand::Line {
                    from: (*x1, *y1),
                    to: (*x2, *y2),
                    color: color_name(color)?,
                }
            }
            ("polyline_begin", [Str(color)]) => SceneCommand::PolylineBegin(color_name(color)?),
            ("vertex", [Number(x), Number(y)]) => SceneCommand::Vertex(*x, *y),
            ("polyline_end", []) => SceneCommand::PolylineEnd,
            _ => return Err(format!("bad call to scene.{name}")),
        };
        self.commands.push(command);
        Ok(HostValue::Unit)
    }
}

/// A color name or `#hex` code, the only text safe to hand a renderer
/// (ADR 0014's allowlist).
fn color_name(text: &str) -> Result<String, String> {
    let ok = (1..=32).contains(&text.len())
        && text.chars().all(|c| c.is_ascii_alphanumeric() || c == '#');
    if ok {
        Ok(text.to_string())
    } else {
        Err(format!("{text:?} is not a color name or #hex code"))
    }
}
