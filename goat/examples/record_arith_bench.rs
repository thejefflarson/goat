//! Times the per-frame record-arithmetic benchmark (`examples/bench/particles.goat`)
//! under wasmtime, with variants that isolate where a frame's time goes.
//!
//!     cargo run --release -p goat --features native --example record_arith_bench
//!     cargo run --release -p goat --features native --example record_arith_bench -- --emit DIR
//!
//!     cargo run --release -p goat --features native --example record_arith_bench -- --wasm A.wasm B.wasm
//!
//! `--emit DIR` writes each variant's `.wasm` instead of timing it, so another
//! engine can run the same module. `--wasm` times modules already built, such
//! as hand-edited ones.

use goat::native::{Guest, HostEvent, Interactive};
use goat::{Host, SceneSink};
use std::time::{Duration, Instant};
use std::{env, fs};

const SOURCE: &str = include_str!("../../examples/bench/particles.goat");
const FLAT: &str = include_str!("../../examples/bench/particles_flat.goat");
const WARMUP: usize = 30;
const FRAMES: usize = 300;

struct Frame(f64);

impl HostEvent for Frame {
    fn tag(&self) -> &'static str {
        "Frame"
    }

    fn construct<H: Host + 'static>(
        &self,
        guest: &mut Guest<H>,
        constructor: &str,
    ) -> Result<i32, String> {
        guest.call(constructor, self.0)
    }
}

#[derive(Default)]
struct Counting {
    shapes: usize,
}

impl SceneSink for Counting {
    fn begin(&mut self) {
        self.shapes = 0;
    }
    fn end(&mut self) {}
    fn circle(&mut self, _: (f64, f64), _: f64, _: &str) {
        self.shapes += 1;
    }
    fn line(&mut self, _: (f64, f64), _: (f64, f64), _: &str) {}
    fn polyline_begin(&mut self, _: &str) {}
    fn vertex(&mut self, _: f64, _: f64) {}
    fn polyline_end(&mut self) {}
    fn rect(&mut self, _: (f64, f64), _: (f64, f64), _: &str) {}
    fn text(&mut self, _: (f64, f64), _: &str, _: &str) {}
}

/// A variant replaces the `step` block and optionally the `dot`/`draw`
/// definitions, and sets the particle count.
struct Variant {
    name: &'static str,
    base: &'static str,
    step: &'static str,
    draw: &'static str,
    count: u32,
}

const fn variant(name: &'static str, step: &'static str) -> Variant {
    Variant {
        name,
        base: SOURCE,
        step,
        draw: "",
        count: 1000,
    }
}

const STEP_FULL: &str = "";
const LIST_ONLY: &str = "step = program(q) do q done";
const ADD_ONLY: &str = "step = program(q) do {p: q.p + q.v, v: q.v} done";
const MUL_ONLY: &str = "step = program(q) do {p: q.p, v: q.v * {x: 0.999, y: 0.999}} done";
const SCALAR_ADD: &str =
    "step = program(q) do {p: {x: q.p.x + q.v.x, y: q.p.y + q.v.y}, v: q.v} done";
const SCALAR_FULL: &str = "\
step = program(q) do
  px = q.p.x + q.v.x
  py = q.p.y + q.v.y
  vx = q.v.x * 0.999
  vy = q.v.y * 0.999
  hit_x = px < 0 or px > 400
  hit_y = py < 0 or py > 300
  {
    p: {x: px, y: py},
    v: {x: if hit_x then 0 - vx else vx done, y: if hit_y then 0 - vy else vy done}
  }
done";
const SCALAR_HEAVY: &str = "\
step = program(q) do
  px = q.p.x + q.v.x
  py = q.p.y + q.v.y
  vx = q.v.x * 0.999
  vy = q.v.y * 0.999
  a = px * 1.0001 + py * 0.9999 - vx * 0.5 + vy * 0.25
  b = px * 0.3333 - py * 0.6667 + vx * 1.5 - vy * 2.5
  c = a * b + a - b + a * 0.01 + b * 0.02
  d = c * 0.0000001
  {
    p: {x: px + d, y: py + d},
    v: {x: vx + d, y: vy + d}
  }
done";
const HOISTED: &str = "\
damping = {x: 0.999, y: 0.999}

step = program(q) do
  p = q.p + q.v
  v = q.v * damping
  hit_x = p.x < 0 or p.x > 400
  hit_y = p.y < 0 or p.y > 300
  {
    p: p,
    v: {
      x: if hit_x then 0 - v.x else v.x done,
      y: if hit_y then 0 - v.y else v.y done
    }
  }
done";
const DRAW_EMPTY: &str = "draw = program(model) do [] done";
const DRAW_BUILD: &str = "\
dot = program(q) do
  Dot({x: q.p.x, y: q.p.y, r: 2, fill: \"tomato\"})
done

draw = program(model) do
  dots = change_each(model.ps, dot)
  if length(dots) < 0 then dots else [] done
done";

const VARIANTS: &[Variant] = &[
    variant("full", STEP_FULL),
    variant("list-only", LIST_ONLY),
    variant("add-only", ADD_ONLY),
    variant("mul-only", MUL_ONLY),
    variant("scalar-add", SCALAR_ADD),
    variant("scalar-full", SCALAR_FULL),
    variant("scalar-heavy", SCALAR_HEAVY),
    variant("hoisted", HOISTED),
    Variant {
        base: FLAT,
        ..variant("flat", STEP_FULL)
    },
    Variant {
        base: FLAT,
        count: 100_000,
        ..variant("flat-100k", STEP_FULL)
    },
    Variant {
        draw: DRAW_BUILD,
        ..variant("draw-build", STEP_FULL)
    },
    Variant {
        draw: DRAW_EMPTY,
        ..variant("draw-empty", STEP_FULL)
    },
    Variant {
        count: 10_000,
        ..variant("full-10k", STEP_FULL)
    },
    Variant {
        count: 100_000,
        ..variant("full-100k", STEP_FULL)
    },
];

fn source(variant: &Variant) -> String {
    let mut text = variant
        .base
        .replace("count = 1000\n", &format!("count = {}\n", variant.count));
    let replace = |text: &mut String, from: &str, to: &str, with: &str| {
        let start = text.find(from).expect(from);
        let end = start + text[start..].find(to).expect(to) + to.len();
        text.replace_range(start..end, with);
    };
    if !variant.step.is_empty() {
        replace(
            &mut text,
            "# step begin\n",
            "# step end\n",
            &format!("{}\n", variant.step),
        );
    }
    if !variant.draw.is_empty() {
        let at = text.find("dot = program").expect("dot");
        text.replace_range(at.., &format!("{}\n", variant.draw));
    }
    text
}

fn median(mut samples: Vec<Duration>) -> Duration {
    samples.sort();
    samples[samples.len() / 2]
}

fn micros(d: Duration) -> f64 {
    d.as_secs_f64() * 1e6
}

fn measure(name: &str, wasm: &[u8]) -> Result<(), String> {
    let mut program: Interactive<Counting, Frame> = Interactive::new(wasm, Counting::default())?;
    let (mut updates, mut draws) = (Vec::new(), Vec::new());
    for frame in 0..WARMUP + FRAMES {
        let started = Instant::now();
        program.send(&Frame(16.0))?;
        let update = started.elapsed();
        let started = Instant::now();
        program.draw()?;
        let draw = started.elapsed();
        if frame >= WARMUP {
            updates.push(update);
            draws.push(draw);
        }
    }
    let shapes = program.sink_mut().shapes;
    let (_, leaked) = program.finish()?;
    println!(
        "{:<12} update {:>8.1} us  draw {:>8.1} us  shapes {:>5}  leaked {}",
        name,
        micros(median(updates)),
        micros(median(draws)),
        shapes,
        leaked
    );
    Ok(())
}

/// Runs `examples/bench/inner_loop.wat`: the step's arithmetic with no
/// allocation, scalar against `f64x2`.
fn inner_loop() -> Result<(), String> {
    const PARTICLES: i32 = 1000;
    const REPS: i32 = 20_000;
    let engine = wasmtime::Engine::default();
    let module =
        wasmtime::Module::new(&engine, include_str!("../../examples/bench/inner_loop.wat"))
            .map_err(|e| e.to_string())?;
    let mut store = wasmtime::Store::new(&engine, ());
    let instance = wasmtime::Instance::new(&mut store, &module, &[]).map_err(|e| e.to_string())?;
    let err = |e: wasmtime::Error| e.to_string();
    instance
        .get_typed_func::<i32, ()>(&mut store, "init")
        .map_err(err)?
        .call(&mut store, PARTICLES)
        .map_err(err)?;
    for _ in 0..3 {
        for name in ["scalar", "simd"] {
            let run = instance
                .get_typed_func::<(i32, i32), f64>(&mut store, name)
                .map_err(err)?;
            let started = Instant::now();
            run.call(&mut store, (PARTICLES, REPS)).map_err(err)?;
            let per_particle = started.elapsed().as_secs_f64() * 1e9 / (PARTICLES * REPS) as f64;
            println!("{name:<7} {per_particle:6.3} ns per particle");
        }
    }
    Ok(())
}

fn main() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();
    if args.iter().any(|a| a == "--inner") {
        return inner_loop();
    }
    if let Some(at) = args.iter().position(|a| a == "--wasm") {
        for file in &args[at + 1..] {
            measure(file, &fs::read(file).map_err(|e| e.to_string())?)?;
        }
        return Ok(());
    }
    let emit = args
        .iter()
        .position(|a| a == "--emit")
        .and_then(|at| args.get(at + 1));
    for variant in VARIANTS {
        let wasm = goat_canvas::compile(&source(variant))?;
        match emit {
            Some(dir) => fs::write(format!("{dir}/{}.wasm", variant.name), &wasm)
                .map_err(|e| e.to_string())?,
            None => measure(variant.name, &wasm)?,
        }
    }
    Ok(())
}
