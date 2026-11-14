//! Embed an interactive goat program: the host sends events, draws the frames
//! the program returns, and hot-reloads edited source without losing state.
//!
//!     cargo run -p goat --features native --example embed_live

use goat::native::{Event, Interactive, Reloaded};
use goat::{HostInterface, SceneSink};

/// Records each circle the program draws as `(x, radius)`.
#[derive(Default)]
struct Circles(Vec<(f64, f64)>);

impl SceneSink for Circles {
    fn begin(&mut self) {
        self.0.clear();
    }
    fn end(&mut self) {}
    fn circle(&mut self, center: (f64, f64), radius: f64, _: &str) {
        self.0.push((center.0, radius));
    }
    fn line(&mut self, _: (f64, f64), _: (f64, f64), _: &str) {}
    fn polyline_begin(&mut self, _: &str) {}
    fn vertex(&mut self, _: f64, _: f64) {}
    fn polyline_end(&mut self) {}
    fn rect(&mut self, _: (f64, f64), _: (f64, f64), _: &str) {}
    fn text(&mut self, _: (f64, f64), _: &str, _: &str) {}
}

fn script(radius: u32) -> String {
    format!(
        "init = {{ticks: 0}}\n\
         update = program(model, event) do\n\
           match event do Tick(dt) then {{ticks: model.ticks + 1}} done\n\
         done\n\
         draw = program(model) do\n\
           [Circle({{x: model.ticks, y: 0, r: {radius}, color: \"red\"}})]\n\
         done"
    )
}

fn main() -> Result<(), String> {
    let host = HostInterface::turtle();
    let compile = |source: String| {
        goat::compile_reloadable(&source, &host).map_err(|errors| errors[0].message.clone())
    };

    let mut program = Interactive::new(&compile(script(5))?, Circles::default())?;
    for _ in 0..3 {
        program.send(&Event::Tick(0.016))?;
    }
    program.draw()?;

    let reloaded = program.reload(&compile(script(9))?)?;
    program.draw()?;
    let (circles, leaked) = program.finish()?;

    println!(
        "{reloaded:?}: circles {:?}, {leaked} heap blocks leaked",
        circles.0
    );
    assert_eq!(reloaded, Reloaded::Refreshed);
    assert_eq!(circles.0, [(3.0, 9.0)]);
    assert_eq!(leaked, 0);
    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn runs() {
        super::main().expect("example runs");
    }
}
