//! The headless turtle: a `Host` that records the program's turtle commands
//! and replays them into an SVG. The SVG is a pure function of the command
//! log, so two runs that make the same calls draw byte-identical pictures.
//!
//! The turtle starts at the origin facing up, pen down, drawing black. `left`
//! and `right` turn by degrees; the picture's y axis points down, as in SVG.

use goat::Boundary::{self, Number, Str, Unit};
use goat::{Host, HostValue};
use std::fmt::Write;

/// A bound on a runaway program's memory, not on any honest drawing.
const MAX_COMMANDS: usize = 1_000_000;

const MARGIN: f64 = 10.0;
const EMPTY_VIEW_BOX: &str = "-50 -50 100 100";

#[derive(Debug, Clone, PartialEq)]
pub enum Command {
    Forward(f64),
    Back(f64),
    Left(f64),
    Right(f64),
    PenUp,
    PenDown,
    Color(String),
}

#[derive(Debug, Default, PartialEq)]
pub struct TurtleHost {
    pub commands: Vec<Command>,
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
        if self.commands.len() >= MAX_COMMANDS {
            return Err(format!("the turtle drew more than {MAX_COMMANDS} commands"));
        }
        let command = match (name, args) {
            ("forward", [HostValue::Number(x)]) => Command::Forward(finite(name, *x)?),
            ("back", [HostValue::Number(x)]) => Command::Back(finite(name, *x)?),
            ("left", [HostValue::Number(x)]) => Command::Left(finite(name, *x)?),
            ("right", [HostValue::Number(x)]) => Command::Right(finite(name, *x)?),
            ("pen_up", []) => Command::PenUp,
            ("pen_down", []) => Command::PenDown,
            ("color", [HostValue::Str(text)]) => Command::Color(color_name(text)?),
            _ => return Err(format!("bad call to turtle.{name}")),
        };
        self.commands.push(command);
        Ok(HostValue::Unit)
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

/// A color name or `#hex` code. Nothing else is accepted, so the text is safe
/// to write straight into an SVG attribute.
fn color_name(text: &str) -> Result<String, String> {
    let ok = !text.is_empty()
        && text.len() <= 32
        && text.chars().all(|c| c.is_ascii_alphanumeric() || c == '#');
    if ok {
        Ok(text.to_string())
    } else {
        Err(format!(
            "color wants a name like \"red\" or a code like \"#ff8800\", not {text:?}"
        ))
    }
}

struct Stroke<'a> {
    color: &'a str,
    points: Vec<(f64, f64)>,
}

impl TurtleHost {
    pub fn to_svg(&self) -> String {
        let strokes = self.strokes();
        let mut svg = format!(
            "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"{}\">\n\
             <g fill=\"none\" stroke-width=\"1\" stroke-linecap=\"round\" stroke-linejoin=\"round\">\n",
            view_box(&strokes)
        );
        for stroke in &strokes {
            let points: Vec<String> = stroke
                .points
                .iter()
                .map(|&(x, y)| format!("{},{}", number(x), number(y)))
                .collect();
            writeln!(
                svg,
                "<polyline stroke=\"{}\" points=\"{}\"/>",
                stroke.color,
                points.join(" ")
            )
            .expect("writing to a String");
        }
        svg.push_str("</g>\n</svg>\n");
        svg
    }

    /// The pen's trail: a run of pen-down moves in one color is one stroke.
    fn strokes(&self) -> Vec<Stroke<'_>> {
        let (mut x, mut y, mut heading) = (0.0_f64, 0.0_f64, 0.0_f64);
        let (mut pen_down, mut color, mut open) = (true, "black", false);
        let mut strokes: Vec<Stroke> = Vec::new();
        for command in &self.commands {
            match command {
                Command::Forward(d) | Command::Back(d) => {
                    let distance = if matches!(command, Command::Back(_)) {
                        -d
                    } else {
                        *d
                    };
                    let angle = heading.to_radians();
                    let (to_x, to_y) = (x + distance * angle.sin(), y - distance * angle.cos());
                    if pen_down {
                        if !open {
                            strokes.push(Stroke {
                                color,
                                points: vec![(x, y)],
                            });
                            open = true;
                        }
                        strokes
                            .last_mut()
                            .expect("an open stroke")
                            .points
                            .push((to_x, to_y));
                    }
                    (x, y) = (to_x, to_y);
                }
                Command::Left(degrees) => heading = (heading - degrees).rem_euclid(360.0),
                Command::Right(degrees) => heading = (heading + degrees).rem_euclid(360.0),
                Command::PenUp => (pen_down, open) = (false, false),
                Command::PenDown => pen_down = true,
                Command::Color(name) => (color, open) = (name, false),
            }
        }
        strokes
    }
}

fn view_box(strokes: &[Stroke]) -> String {
    let mut points = strokes.iter().flat_map(|s| s.points.iter());
    let Some(&(x, y)) = points.next() else {
        return EMPTY_VIEW_BOX.to_string();
    };
    let (mut min_x, mut max_x, mut min_y, mut max_y) = (x, x, y, y);
    for &(x, y) in points {
        (min_x, max_x) = (min_x.min(x), max_x.max(x));
        (min_y, max_y) = (min_y.min(y), max_y.max(y));
    }
    format!(
        "{} {} {} {}",
        number(min_x - MARGIN),
        number(min_y - MARGIN),
        number(max_x - min_x + 2.0 * MARGIN),
        number(max_y - min_y + 2.0 * MARGIN),
    )
}

/// Three decimals, trailing zeros dropped, and no `-0`: enough to be exact on
/// the right angles kids draw and steady across platforms' `sin` and `cos`.
fn number(x: f64) -> String {
    let fixed = format!("{x:.3}");
    let trimmed = fixed.trim_end_matches('0').trim_end_matches('.');
    if trimmed == "-0" { "0" } else { trimmed }.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn call(host: &mut TurtleHost, name: &str, args: &[HostValue]) -> Result<HostValue, String> {
        host.call("turtle", name, args)
    }

    fn n(x: f64) -> HostValue {
        HostValue::Number(x)
    }

    #[test]
    fn numbers_print_short_and_never_negative_zero() {
        assert_eq!(number(100.0), "100");
        assert_eq!(number(0.0), "0");
        assert_eq!(number(-0.0004), "0");
        assert_eq!(number(1.23456), "1.235");
        assert_eq!(number(-2.5), "-2.5");
    }

    #[test]
    fn a_right_angle_lands_exactly() {
        let mut host = TurtleHost::default();
        call(&mut host, "forward", &[n(10.0)]).unwrap();
        call(&mut host, "right", &[n(90.0)]).unwrap();
        call(&mut host, "forward", &[n(10.0)]).unwrap();
        assert!(host.to_svg().contains("points=\"0,0 0,-10 10,-10\""));
    }

    #[test]
    fn a_pen_up_move_draws_nothing_and_color_starts_a_new_stroke() {
        let mut host = TurtleHost::default();
        call(&mut host, "pen_up", &[]).unwrap();
        call(&mut host, "forward", &[n(5.0)]).unwrap();
        call(&mut host, "pen_down", &[]).unwrap();
        call(&mut host, "color", &[HostValue::Str("red".into())]).unwrap();
        call(&mut host, "forward", &[n(5.0)]).unwrap();
        call(&mut host, "color", &[HostValue::Str("#00f".into())]).unwrap();
        call(&mut host, "back", &[n(5.0)]).unwrap();
        let svg = host.to_svg();
        assert!(svg.contains("<polyline stroke=\"red\" points=\"0,-5 0,-10\"/>"));
        assert!(svg.contains("<polyline stroke=\"#00f\" points=\"0,-10 0,-5\"/>"));
        assert_eq!(svg.matches("<polyline").count(), 2);
    }

    #[test]
    fn an_empty_drawing_is_still_a_valid_svg() {
        let svg = TurtleHost::default().to_svg();
        assert!(svg.contains(&format!("viewBox=\"{EMPTY_VIEW_BOX}\"")));
        assert!(!svg.contains("<polyline"));
    }

    #[test]
    fn bad_arguments_are_refused() {
        let mut host = TurtleHost::default();
        assert!(call(&mut host, "forward", &[n(f64::NAN)]).is_err());
        assert!(call(&mut host, "left", &[n(f64::INFINITY)]).is_err());
        for bad in ["", "re d", "\"/><script>", &"x".repeat(33)] {
            let arg = [HostValue::Str(bad.into())];
            assert!(call(&mut host, "color", &arg).is_err(), "{bad:?}");
        }
        assert!(call(&mut host, "sideways", &[]).is_err());
        assert!(host.commands.is_empty());
    }

    #[test]
    fn a_runaway_program_is_stopped() {
        let mut host = TurtleHost {
            commands: vec![Command::PenUp; MAX_COMMANDS],
        };
        assert!(call(&mut host, "pen_up", &[]).is_err());
    }

    #[test]
    fn only_the_turtle_commands_are_provided() {
        let host = TurtleHost::default();
        assert_eq!(host.signature("turtle", "color"), Some((vec![Str], Unit)));
        assert_eq!(host.signature("turtle", "pen_up"), Some((vec![], Unit)));
        assert_eq!(host.signature("turtle", "jump"), None);
        assert_eq!(host.signature("other", "forward"), None);
    }
}
