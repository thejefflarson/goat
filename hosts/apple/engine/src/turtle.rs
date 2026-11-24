//! Run-once turtle programs as frames. The program runs to its end first, the
//! turtle only recording the pen's trail; the trail is then drawn a few
//! segments at a time, as `animate` in `web/runtime.ts` does, each step one
//! `scene.frame` of the picture so far, fitted to the canvas.

use goat::Boundary::{self, Number, Str, Unit};
use goat::{Host, HostValue};
use goat_mir::frame::{Calls, Wire};

/// The canvas the frames are drawn for (`native/appkit/Painter.swift`).
const WIDTH: f64 = 400.0;
const HEIGHT: f64 = 300.0;
const MARGIN: f64 = 10.0;

/// Segments drawn per frame, until a drawing is long enough that this would
/// take more than [`LONGEST_FRAMES`] frames.
const SEGMENTS_PER_FRAME: usize = 4;
const LONGEST_FRAMES: usize = 900;

/// A bound on a runaway program's memory, and on the size of the last frame,
/// which holds every segment.
pub const MAX_SEGMENTS: usize = 250_000;

struct Stroke {
    color: String,
    points: Vec<(f64, f64)>,
}

/// The turtle as a `Host`: it keeps the pen's state and the strokes it has
/// drawn.
pub struct TurtleHost {
    at: (f64, f64),
    heading: f64,
    pen_down: bool,
    color: String,
    open: bool,
    strokes: Vec<Stroke>,
    segments: usize,
}

impl Default for TurtleHost {
    fn default() -> Self {
        TurtleHost {
            at: (0.0, 0.0),
            heading: 0.0,
            pen_down: true,
            color: "black".into(),
            open: false,
            strokes: Vec::new(),
            segments: 0,
        }
    }
}

impl TurtleHost {
    fn travel(&mut self, distance: f64) -> Result<(), String> {
        let angle = self.heading.to_radians();
        let to = (
            self.at.0 + distance * angle.sin(),
            self.at.1 - distance * angle.cos(),
        );
        if self.pen_down {
            if self.segments >= MAX_SEGMENTS {
                return Err(format!("the turtle drew more than {MAX_SEGMENTS} lines"));
            }
            if !self.open {
                self.strokes.push(Stroke {
                    color: self.color.clone(),
                    points: vec![self.at],
                });
                self.open = true;
            }
            self.strokes
                .last_mut()
                .expect("an open stroke")
                .points
                .push(to);
            self.segments += 1;
        }
        self.at = to;
        Ok(())
    }

    /// The finished drawing, ready to be shown a few segments at a time.
    pub fn into_drawing(self) -> Drawing {
        Drawing::new(self.strokes, self.segments)
    }
}

fn finite(name: &str, x: f64) -> Result<f64, String> {
    if x.is_finite() {
        Ok(x)
    } else {
        Err(format!(
            "{name} needs a real number, not {}",
            goat::format_number(x)
        ))
    }
}

impl Host for TurtleHost {
    fn signature(&self, module: &str, name: &str) -> Option<(Vec<Boundary>, Boundary)> {
        if module != "turtle" {
            return None;
        }
        Some(match name {
            "forward" | "back" | "left" | "right" => (vec![Number], Unit),
            "pen_up" | "pen_down" => (vec![], Unit),
            "color" => (vec![Str], Unit),
            _ => return None,
        })
    }

    fn call(&mut self, _: &str, name: &str, args: &[HostValue]) -> Result<HostValue, String> {
        match (name, args) {
            ("forward", [HostValue::Number(x)]) => self.travel(finite(name, *x)?)?,
            ("back", [HostValue::Number(x)]) => self.travel(-finite(name, *x)?)?,
            ("left", [HostValue::Number(x)]) => {
                self.heading = (self.heading - finite(name, *x)?).rem_euclid(360.0)
            }
            ("right", [HostValue::Number(x)]) => {
                self.heading = (self.heading + finite(name, *x)?).rem_euclid(360.0)
            }
            ("pen_up", []) => (self.pen_down, self.open) = (false, false),
            ("pen_down", []) => self.pen_down = true,
            ("color", [HostValue::Str(text)]) => {
                goat::check_color(text)?;
                (self.color, self.open) = (text.clone(), false);
            }
            _ => return Err(format!("bad call to turtle.{name}")),
        }
        Ok(HostValue::Unit)
    }
}

/// A drawing scaled to the canvas, and how far along showing it is.
pub struct Drawing {
    strokes: Vec<Stroke>,
    segments: usize,
    shown: usize,
    per_frame: usize,
    header: Vec<u8>,
    indexes: Indexes,
}

struct Indexes {
    begin: u8,
    end: u8,
    polyline_begin: u8,
    vertex: u8,
    polyline_end: u8,
}

impl Drawing {
    fn new(mut strokes: Vec<Stroke>, segments: usize) -> Drawing {
        fit(&mut strokes);
        let mut calls = Calls::default();
        let indexes = Indexes {
            begin: calls.index("begin", &[]),
            end: calls.index("end", &[]),
            polyline_begin: calls.index("polyline_begin", &[Wire::Str]),
            vertex: calls.index("vertex", &[Wire::Float, Wire::Float]),
            polyline_end: calls.index("polyline_end", &[]),
        };
        Drawing {
            strokes,
            segments,
            shown: 0,
            per_frame: SEGMENTS_PER_FRAME.max(segments.div_ceil(LONGEST_FRAMES)),
            header: calls.header(),
            indexes,
        }
    }

    /// The next frame, and whether it is the last. A drawing with no
    /// segments is one blank frame.
    pub fn next_frame(&mut self) -> (Vec<u8>, bool) {
        self.shown = (self.shown + self.per_frame).min(self.segments);
        (self.encode(self.shown), self.shown == self.segments)
    }

    fn encode(&self, mut budget: usize) -> Vec<u8> {
        let at = &self.indexes;
        let mut bytes = self.header.clone();
        bytes.push(at.begin);
        for stroke in &self.strokes {
            let take = budget.min(stroke.points.len() - 1);
            if take == 0 {
                break;
            }
            budget -= take;
            bytes.push(at.polyline_begin);
            bytes.extend((stroke.color.len() as u32).to_le_bytes());
            bytes.extend(stroke.color.as_bytes());
            for (x, y) in &stroke.points[..=take] {
                bytes.push(at.vertex);
                bytes.extend(x.to_le_bytes());
                bytes.extend(y.to_le_bytes());
            }
            bytes.push(at.polyline_end);
        }
        bytes.push(at.end);
        bytes
    }
}

/// Move the strokes into the canvas, scaled to fill it and centered, with the
/// turtle's starting point inside.
fn fit(strokes: &mut [Stroke]) {
    let points = || strokes.iter().flat_map(|s| s.points.iter());
    let low = points().fold((0.0_f64, 0.0_f64), |m, p| (m.0.min(p.0), m.1.min(p.1)));
    let high = points().fold((0.0_f64, 0.0_f64), |m, p| (m.0.max(p.0), m.1.max(p.1)));
    let (width, height) = (high.0 - low.0 + 2.0 * MARGIN, high.1 - low.1 + 2.0 * MARGIN);
    let scale = (WIDTH / width).min(HEIGHT / height);
    let (pad_x, pad_y) = (
        (WIDTH - width * scale) / 2.0,
        (HEIGHT - height * scale) / 2.0,
    );
    for (x, y) in strokes.iter_mut().flat_map(|s| s.points.iter_mut()) {
        *x = (*x - low.0 + MARGIN) * scale + pad_x;
        *y = (*y - low.1 + MARGIN) * scale + pad_y;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn square() -> TurtleHost {
        let mut turtle = TurtleHost::default();
        for _ in 0..4 {
            turtle
                .call("turtle", "forward", &[HostValue::Number(100.0)])
                .unwrap();
            turtle
                .call("turtle", "right", &[HostValue::Number(90.0)])
                .unwrap();
        }
        turtle
    }

    fn vertices(frame: &[u8]) -> Vec<(f64, f64)> {
        let mut seen = Vec::new();
        goat_mir::frame::replay(frame, |name, args| {
            if let ("vertex", [HostValue::Number(x), HostValue::Number(y)]) = (name, args) {
                seen.push((*x, *y));
            }
            Ok(())
        })
        .expect("a well-formed frame");
        seen
    }

    #[test]
    fn a_drawing_is_shown_four_segments_at_a_time() {
        let mut drawing = TurtleHost::default();
        for _ in 0..10 {
            drawing
                .call("turtle", "forward", &[HostValue::Number(5.0)])
                .unwrap();
        }
        let mut drawing = drawing.into_drawing();
        let mut shown = Vec::new();
        loop {
            let (frame, last) = drawing.next_frame();
            shown.push(vertices(&frame).len());
            if last {
                break;
            }
        }
        assert_eq!(shown, [5, 9, 11]);
    }

    #[test]
    fn the_picture_fits_the_canvas_with_a_margin() {
        let mut drawing = square().into_drawing();
        let last = loop {
            let (frame, last) = drawing.next_frame();
            if last {
                break frame;
            }
        };
        for (x, y) in vertices(&last) {
            assert!(
                (0.0..=WIDTH).contains(&x) && (0.0..=HEIGHT).contains(&y),
                "{x},{y}"
            );
        }
    }

    #[test]
    fn pen_up_starts_a_new_stroke() {
        let mut turtle = TurtleHost::default();
        let step = |t: &mut TurtleHost, name: &str, args: &[HostValue]| {
            t.call("turtle", name, args).unwrap();
        };
        step(&mut turtle, "forward", &[HostValue::Number(10.0)]);
        step(&mut turtle, "pen_up", &[]);
        step(&mut turtle, "forward", &[HostValue::Number(10.0)]);
        step(&mut turtle, "pen_down", &[]);
        step(&mut turtle, "color", &[HostValue::Str("red".into())]);
        step(&mut turtle, "forward", &[HostValue::Number(10.0)]);
        assert_eq!(turtle.strokes.len(), 2);
        assert_eq!(turtle.strokes[1].color, "red");
        assert_eq!(turtle.segments, 2);
    }

    #[test]
    fn nothing_drawn_is_one_blank_frame() {
        let mut drawing = TurtleHost::default().into_drawing();
        let (frame, last) = drawing.next_frame();
        assert!(last);
        assert!(vertices(&frame).is_empty());
    }

    #[test]
    fn a_bad_color_or_number_is_the_programs_error() {
        let mut turtle = TurtleHost::default();
        let bad = turtle.call("turtle", "color", &[HostValue::Str("a b".into())]);
        assert!(bad.is_err());
        let nan = turtle.call("turtle", "forward", &[HostValue::Number(f64::NAN)]);
        assert!(nan.unwrap_err().contains("real number"));
    }
}
