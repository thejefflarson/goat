//! Per-frame timing of every `examples/canvas` program, on wasmtime's Pulley
//! interpreter or its default Cranelift backend. `bench` is the Rust entry;
//! `goat_pulley_bench` is the C entry an iOS app links as a static library.

use goat_canvas::{Canvas, Event};
use std::fmt::Write;
use std::time::Instant;

const PROGRAMS: [(&str, &str, &str); 3] = [
    (
        "bounce",
        include_str!("../../examples/canvas/bounce.goat"),
        include_str!("../../examples/canvas/bounce.events"),
    ),
    (
        "catch",
        include_str!("../../examples/canvas/catch.goat"),
        include_str!("../../examples/canvas/catch.events"),
    ),
    ("sky", include_str!("../../examples/canvas/sky.goat"), ""),
];

const WARMUP: usize = 30;
const FRAMES: usize = 600;

/// What one program's frames cost, in milliseconds per update plus draw.
pub struct Timing {
    pub name: &'static str,
    pub load_ms: f64,
    pub p50: f64,
    pub p95: f64,
    pub max: f64,
}

fn percentile(sorted: &[f64], fraction: f64) -> f64 {
    let rank = (sorted.len() as f64 * fraction).ceil() as usize;
    sorted[rank.clamp(1, sorted.len()) - 1]
}

fn time(name: &'static str, source: &str, events: &str, frames: usize) -> Result<Timing, String> {
    let started = Instant::now();
    let wasm = goat_canvas::compile(source)?;
    let mut canvas = Canvas::new(&wasm)?;
    let load_ms = started.elapsed().as_secs_f64() * 1e3;

    let mut script = Event::parse_script(events)?;
    script.resize(script.len().max(frames), Event::Frame(16.0));
    let mut costs = Vec::with_capacity(script.len());
    for event in &script {
        let started = Instant::now();
        canvas.send(event)?;
        canvas.draw()?;
        costs.push(started.elapsed().as_secs_f64() * 1e3);
    }
    let mut costs = costs.split_off(WARMUP.min(costs.len() - 1));
    costs.sort_by(f64::total_cmp);
    Ok(Timing {
        name,
        load_ms,
        p50: percentile(&costs, 0.50),
        p95: percentile(&costs, 0.95),
        max: costs[costs.len() - 1],
    })
}

/// Time every canvas example for `frames` frames each, under Pulley when
/// `pulley` is set.
///
/// Selecting the runtime sets `GOAT_RUNTIME`, which the engine reads when it is
/// built, so the caller must be the only thread running.
pub fn bench(pulley: bool, frames: usize) -> Result<String, String> {
    // SAFETY: documented above; the bench runs before the host starts threads.
    unsafe {
        if pulley {
            std::env::set_var("GOAT_RUNTIME", "pulley");
        } else {
            std::env::remove_var("GOAT_RUNTIME");
        }
    }
    let mut report = format!(
        "runtime {}\nprogram   load_ms    p50_ms    p95_ms    max_ms\n",
        if pulley { "pulley" } else { "cranelift" }
    );
    for (name, source, events) in PROGRAMS {
        let t = time(name, source, events, frames)?;
        let _ = writeln!(
            report,
            "{:<8} {:>8.2} {:>9.3} {:>9.3} {:>9.3}",
            t.name, t.load_ms, t.p50, t.p95, t.max
        );
    }
    Ok(report)
}

/// Write the Pulley report (or the error) into `out[..cap]` as UTF-8 and return
/// the byte count written. Call it once, from the app's main thread.
///
/// # Safety
/// `out` must be valid for `cap` bytes of writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn goat_pulley_bench(pulley: bool, out: *mut u8, cap: usize) -> usize {
    let text = bench(pulley, FRAMES).unwrap_or_else(|e| format!("error: {e}"));
    let n = text.len().min(cap);
    // SAFETY: the caller guarantees `out` holds `cap` bytes, and `n <= cap`.
    unsafe { std::ptr::copy_nonoverlapping(text.as_ptr(), out, n) };
    n
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_canvas_example_runs_under_both_runtimes() {
        for pulley in [false, true] {
            let report = bench(pulley, 40).expect("bench runs");
            for (name, ..) in PROGRAMS {
                assert!(report.contains(name), "{report}");
            }
        }
    }
}
