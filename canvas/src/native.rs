use crate::compile;
use goat::native::{Guest, HostEvent, Interactive};
use goat::{Host, SceneCommand, SceneHost};
use std::fmt::Write;
use std::time::Duration;

pub const WIDTH: u32 = 400;
pub const HEIGHT: u32 = 300;

/// Bounds one call into a script, so a runaway `update` or `draw` traps
/// instead of hanging the host (ADR 0021).
const CALL_TIMEOUT: Duration = Duration::from_secs(5);

#[derive(Clone, Debug, PartialEq)]
pub enum Event {
    Frame(f64),
    KeyPress(String),
    KeyRelease(String),
    MouseMove(f64, f64),
    MousePress(f64, f64),
    MouseRelease(f64, f64),
}

impl HostEvent for Event {
    fn tag(&self) -> &'static str {
        match self {
            Event::Frame(_) => "Frame",
            Event::KeyPress(_) => "KeyPress",
            Event::KeyRelease(_) => "KeyRelease",
            Event::MouseMove(..) => "MouseMove",
            Event::MousePress(..) => "MousePress",
            Event::MouseRelease(..) => "MouseRelease",
        }
    }

    fn construct<H: Host + 'static>(
        &self,
        guest: &mut Guest<H>,
        constructor: &str,
    ) -> Result<i32, String> {
        match self {
            Event::Frame(dt) => guest.call(constructor, *dt),
            Event::KeyPress(key) | Event::KeyRelease(key) => {
                let key = guest.string(key)?;
                guest.call(constructor, key)
            }
            Event::MouseMove(x, y) | Event::MousePress(x, y) | Event::MouseRelease(x, y) => {
                guest.call(constructor, (*x, *y))
            }
        }
    }
}

impl Event {
    /// One event per line, the tag then its arguments: `Frame 16`,
    /// `KeyPress ArrowLeft`, `MousePress 120 80`. Blank lines and `#` comments
    /// are skipped. A key is the rest of its line, so `KeyPress  ` is Space.
    pub fn parse_script(text: &str) -> Result<Vec<Event>, String> {
        let mut events = Vec::new();
        for (index, line) in text.lines().enumerate() {
            if line.trim().is_empty() || line.starts_with('#') {
                continue;
            }
            let at = |message: &str| format!("events line {}: {message}", index + 1);
            let (tag, rest) = line.split_once(' ').unwrap_or((line, ""));
            let number = |s: &str| {
                s.parse::<f64>()
                    .ok()
                    .filter(|x| x.is_finite())
                    .ok_or_else(|| at(&format!("`{s}` is not a number")))
            };
            let point = || match rest.split_whitespace().collect::<Vec<_>>()[..] {
                [x, y] => Ok((number(x)?, number(y)?)),
                _ => Err(at("expected two numbers")),
            };
            events.push(match tag {
                "Frame" => Event::Frame(number(rest.trim())?),
                "KeyPress" => Event::KeyPress(rest.to_string()),
                "KeyRelease" => Event::KeyRelease(rest.to_string()),
                "MouseMove" => point().map(|(x, y)| Event::MouseMove(x, y))?,
                "MousePress" => point().map(|(x, y)| Event::MousePress(x, y))?,
                "MouseRelease" => point().map(|(x, y)| Event::MouseRelease(x, y))?,
                _ => return Err(at(&format!("unknown event `{tag}`"))),
            });
        }
        Ok(events)
    }
}

/// A running script and the picture it last drew.
pub struct Canvas {
    script: Interactive<SceneHost, Event>,
}

impl Canvas {
    pub fn new(wasm: &[u8]) -> Result<Canvas, String> {
        Ok(Canvas {
            script: Interactive::with_timeout(wasm, SceneHost::default(), CALL_TIMEOUT)?,
        })
    }

    /// Deliver `event` to `update`, unless the script does not handle it.
    pub fn send(&mut self, event: &Event) -> Result<(), String> {
        self.script.send(event).map(|_| ())
    }

    /// Run `draw` and return the picture it streamed.
    pub fn draw(&mut self) -> Result<Vec<SceneCommand>, String> {
        self.script.draw()?;
        let commands = std::mem::take(&mut self.script.sink_mut().commands);
        let frame = commands.iter().rposition(|c| *c == SceneCommand::Begin);
        Ok(frame.map_or(Vec::new(), |at| commands[at..].to_vec()))
    }

    /// Tear the script down, returning how many heap blocks it leaked.
    pub fn finish(self) -> Result<u32, String> {
        self.script.finish().map(|(_, leaked)| leaked)
    }
}

/// Run `source` through `events` and draw once at the end, as an SVG.
pub fn render(source: &str, events: &[Event]) -> Result<String, String> {
    let mut canvas = Canvas::new(&compile(source)?)?;
    for event in events {
        canvas.send(event)?;
    }
    let picture = canvas.draw()?;
    let leaked = canvas.finish()?;
    if leaked != 0 {
        return Err(format!("the script leaked {leaked} heap blocks"));
    }
    Ok(to_svg(&picture))
}

/// A picture as an SVG, a pure function of its commands. Colors arrive checked
/// against the shared allowlist; text is the only free-form string, so it is
/// escaped.
pub fn to_svg(picture: &[SceneCommand]) -> String {
    let mut svg = format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{WIDTH}\" height=\"{HEIGHT}\" \
         viewBox=\"0 0 {WIDTH} {HEIGHT}\">\n\
         <rect width=\"{WIDTH}\" height=\"{HEIGHT}\" fill=\"white\"/>\n"
    );
    for command in picture {
        match command {
            SceneCommand::Line { from, to, color } => writeln!(
                svg,
                "<line x1=\"{}\" y1=\"{}\" x2=\"{}\" y2=\"{}\" stroke=\"{color}\"/>",
                number(from.0),
                number(from.1),
                number(to.0),
                number(to.1)
            ),
            SceneCommand::Circle {
                center,
                radius,
                color,
            } => writeln!(
                svg,
                "<circle cx=\"{}\" cy=\"{}\" r=\"{}\" fill=\"{color}\"/>",
                number(center.0),
                number(center.1),
                number(*radius)
            ),
            SceneCommand::Rect {
                origin,
                size,
                color,
            } => writeln!(
                svg,
                "<rect x=\"{}\" y=\"{}\" width=\"{}\" height=\"{}\" fill=\"{color}\"/>",
                number(origin.0),
                number(origin.1),
                number(size.0),
                number(size.1)
            ),
            SceneCommand::Text {
                origin,
                text,
                color,
            } => writeln!(
                svg,
                "<text x=\"{}\" y=\"{}\" fill=\"{color}\" font-family=\"sans-serif\" \
                 font-size=\"14\" dominant-baseline=\"hanging\">{}</text>",
                number(origin.0),
                number(origin.1),
                escape(text)
            ),
            SceneCommand::Begin
            | SceneCommand::End
            | SceneCommand::PolylineBegin(_)
            | SceneCommand::Vertex(..)
            | SceneCommand::PolylineEnd => Ok(()),
        }
        .expect("writing to a String");
    }
    svg.push_str("</svg>\n");
    svg
}

/// Three decimals, trailing zeros dropped, and no `-0`.
fn number(x: f64) -> String {
    let fixed = format!("{x:.3}");
    let trimmed = fixed.trim_end_matches('0').trim_end_matches('.');
    if trimmed == "-0" { "0" } else { trimmed }.to_string()
}

fn escape(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}
