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
    Circle {
        center: (f64, f64),
        radius: f64,
        color: String,
    },
    Rect {
        origin: (f64, f64),
        size: (f64, f64),
        color: String,
    },
    Text {
        origin: (f64, f64),
        text: String,
        color: String,
    },
    Span {
        from: i64,
        to: i64,
        kind: String,
    },
    Swatch {
        role: String,
        light: String,
        dark: String,
    },
}

/// Where an interactive program's picture goes: `draw` streams each frame as
/// `begin`, shapes, `end` (ADR 0015). Colors arrive already checked against
/// ADR 0014's allowlist.
pub trait SceneSink {
    fn begin(&mut self);
    fn end(&mut self);
    fn line(&mut self, from: (f64, f64), to: (f64, f64), color: &str);
    fn polyline_begin(&mut self, color: &str);
    fn vertex(&mut self, x: f64, y: f64);
    fn polyline_end(&mut self);
    fn circle(&mut self, center: (f64, f64), radius: f64, color: &str);
    fn rect(&mut self, origin: (f64, f64), size: (f64, f64), color: &str);
    fn text(&mut self, origin: (f64, f64), text: &str, color: &str);

    /// A style span over `from..to`, byte offsets into the host's text; `kind`
    /// is a role the host styles, never a color. Hosts with no text ignore it.
    fn span(&mut self, _from: i64, _to: i64, _kind: &str) {}

    /// The colors a theme gives a style role on a light page and a dark one.
    /// They are the program's words, not checked here: the host that reads a
    /// theme validates them. Hosts that read no theme ignore it.
    fn swatch(&mut self, _role: &str, _light: &str, _dark: &str) {}
}

/// A sink as a host: answers the `scene.*` imports by calling the sink.
pub struct Scene<S>(pub S);

impl<S: SceneSink> Host for Scene<S> {
    fn signature(&self, module: &str, name: &str) -> Option<(Vec<Boundary>, Boundary)> {
        scene_signature(module, name)
    }

    fn call(&mut self, _: &str, name: &str, args: &[HostValue]) -> Result<HostValue, String> {
        scene_call(&mut self.0, name, args)
    }
}

fn scene_signature(module: &str, name: &str) -> Option<(Vec<Boundary>, Boundary)> {
    use Boundary::{Int, Number, Str, Unit};
    if module != "scene" {
        return None;
    }
    Some(match name {
        "begin" | "end" | "polyline_end" => (vec![], Unit),
        "line" => (vec![Number, Number, Number, Number, Str], Unit),
        "polyline_begin" => (vec![Str], Unit),
        "vertex" => (vec![Number, Number], Unit),
        "circle" => (vec![Number, Number, Number, Str], Unit),
        "rect" => (vec![Number, Number, Number, Number, Str], Unit),
        "text" => (vec![Number, Number, Str, Str], Unit),
        "span" => (vec![Int, Int, Str], Unit),
        "swatch" => (vec![Str, Str, Str], Unit),
        _ => return None,
    })
}

fn scene_call(
    sink: &mut impl SceneSink,
    name: &str,
    args: &[HostValue],
) -> Result<HostValue, String> {
    use HostValue::{Int, Number, Str};
    match (name, args) {
        ("begin", []) => sink.begin(),
        ("end", []) => sink.end(),
        ("line", [Number(x1), Number(y1), Number(x2), Number(y2), Str(color)]) => {
            check_color(color)?;
            sink.line((*x1, *y1), (*x2, *y2), color)
        }
        ("polyline_begin", [Str(color)]) => {
            check_color(color)?;
            sink.polyline_begin(color)
        }
        ("vertex", [Number(x), Number(y)]) => sink.vertex(*x, *y),
        ("polyline_end", []) => sink.polyline_end(),
        ("circle", [Number(x), Number(y), Number(r), Str(color)]) => {
            check_color(color)?;
            sink.circle((*x, *y), *r, color)
        }
        ("rect", [Number(x), Number(y), Number(w), Number(h), Str(color)]) => {
            check_color(color)?;
            sink.rect((*x, *y), (*w, *h), color)
        }
        ("text", [Number(x), Number(y), Str(text), Str(color)]) => {
            check_color(color)?;
            sink.text((*x, *y), text, color)
        }
        ("span", [Int(from), Int(to), Str(kind)]) => sink.span(*from, *to, kind),
        ("swatch", [Str(role), Str(light), Str(dark)]) => sink.swatch(role, light, dark),
        _ => return Err(format!("bad call to scene.{name}")),
    }
    Ok(HostValue::Unit)
}

/// The host of an interactive program's picture: it records the scene the
/// program streams, so the interpreter and wasmtime can be compared command
/// for command.
#[derive(Debug, Default)]
pub struct SceneHost {
    pub commands: Vec<SceneCommand>,
}

impl SceneSink for SceneHost {
    fn begin(&mut self) {
        self.commands.push(SceneCommand::Begin);
    }

    fn end(&mut self) {
        self.commands.push(SceneCommand::End);
    }

    fn line(&mut self, from: (f64, f64), to: (f64, f64), color: &str) {
        self.commands.push(SceneCommand::Line {
            from,
            to,
            color: color.to_string(),
        });
    }

    fn polyline_begin(&mut self, color: &str) {
        self.commands
            .push(SceneCommand::PolylineBegin(color.to_string()));
    }

    fn vertex(&mut self, x: f64, y: f64) {
        self.commands.push(SceneCommand::Vertex(x, y));
    }

    fn polyline_end(&mut self) {
        self.commands.push(SceneCommand::PolylineEnd);
    }

    fn circle(&mut self, center: (f64, f64), radius: f64, color: &str) {
        self.commands.push(SceneCommand::Circle {
            center,
            radius,
            color: color.to_string(),
        });
    }

    fn rect(&mut self, origin: (f64, f64), size: (f64, f64), color: &str) {
        self.commands.push(SceneCommand::Rect {
            origin,
            size,
            color: color.to_string(),
        });
    }

    fn text(&mut self, origin: (f64, f64), text: &str, color: &str) {
        self.commands.push(SceneCommand::Text {
            origin,
            text: text.to_string(),
            color: color.to_string(),
        });
    }

    fn span(&mut self, from: i64, to: i64, kind: &str) {
        self.commands.push(SceneCommand::Span {
            from,
            to,
            kind: kind.to_string(),
        });
    }

    fn swatch(&mut self, role: &str, light: &str, dark: &str) {
        self.commands.push(SceneCommand::Swatch {
            role: role.to_string(),
            light: light.to_string(),
            dark: dark.to_string(),
        });
    }
}

impl Host for SceneHost {
    fn signature(&self, module: &str, name: &str) -> Option<(Vec<Boundary>, Boundary)> {
        scene_signature(module, name)
    }

    fn call(&mut self, _: &str, name: &str, args: &[HostValue]) -> Result<HostValue, String> {
        scene_call(self, name, args)
    }
}

/// A color name or `#hex` code of at most 32 characters, the only text safe to
/// write into an SVG or HTML attribute (ADR 0014's allowlist). Every Rust host
/// validates colors through this one rule.
pub fn check_color(text: &str) -> Result<(), String> {
    let ok = (1..=32).contains(&text.len())
        && text.chars().all(|c| c.is_ascii_alphanumeric() || c == '#');
    if ok {
        Ok(())
    } else {
        Err(format!(
            "color wants a name like \"red\" or a code like \"#ff8800\", not {text:?}"
        ))
    }
}
