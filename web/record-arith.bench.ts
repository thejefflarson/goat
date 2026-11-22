// Per-frame time of the record-arithmetic benchmark under V8, the engine a
// browser runs the same modules on:
//
//   cargo run --release -p goat --features native --example record_arith_bench -- --emit DIR
//   node web/record-arith.bench.ts DIR
//
// DIR holds the `.wasm` files the emit step wrote. Each module is driven the
// way the native harness drives it: `goat_event_Frame` then `goat_update`, then
// `goat_draw` with `scene.circle` validated through `sceneImports` into a
// counting scene, the same work a browser does before it touches a canvas.

import { readFileSync, readdirSync } from "node:fs";
import { join } from "node:path";
import { type Scene, sceneImports } from "./scene.ts";

const WARMUP = 100;
const FRAMES = 300;

interface Exports {
  memory: WebAssembly.Memory;
  goat_setup(): number;
  goat_update(model: number, event: number): number;
  goat_draw(model: number): void;
  goat_event_Frame(dt: number): number;
}

class Counting implements Scene {
  shapes = 0;
  begin() {
    this.shapes = 0;
  }
  circle() {
    this.shapes += 1;
  }
  end() {}
  line() {}
  polylineBegin() {}
  vertex() {}
  polylineEnd() {}
  rect() {}
  text() {}
  span() {}
  edit() {}
  swatch() {}
}

function median(samples: number[]): number {
  return [...samples].sort((a, b) => a - b)[samples.length >> 1];
}

function measure(name: string, bytes: Uint8Array<ArrayBuffer>) {
  const scene = new Counting();
  let exports: Exports;
  const imports = {
    goat: {
      print_number() {},
      print_bool() {},
      print_int() {},
      trap(ptr: number) {
        throw new Error(`trap at ${ptr}`);
      },
    },
    ...sceneImports(() => exports.memory, scene),
  };
  const instance = new WebAssembly.Instance(new WebAssembly.Module(bytes), imports);
  exports = instance.exports as unknown as Exports;
  let model = exports.goat_setup();
  const updates: number[] = [];
  const draws: number[] = [];
  for (let frame = 0; frame < WARMUP + FRAMES; frame++) {
    let started = performance.now();
    model = exports.goat_update(model, exports.goat_event_Frame(16));
    const update = performance.now() - started;
    started = performance.now();
    exports.goat_draw(model);
    const draw = performance.now() - started;
    if (frame >= WARMUP) {
      updates.push(update);
      draws.push(draw);
    }
  }
  const us = (ms: number) => (ms * 1000).toFixed(1).padStart(9);
  console.log(`${name.padEnd(13)} update ${us(median(updates))} us  draw ${us(median(draws))} us  shapes ${scene.shapes}`);
}

// The arithmetic with no allocation, scalar against f64x2 (examples/bench/inner_loop.wat).
function innerLoop(bytes: Uint8Array<ArrayBuffer>) {
  const PARTICLES = 1000;
  const REPS = 20_000;
  const exports = new WebAssembly.Instance(new WebAssembly.Module(bytes)).exports as unknown as {
    init(n: number): void;
    scalar(n: number, reps: number): number;
    simd(n: number, reps: number): number;
  };
  exports.init(PARTICLES);
  for (let round = 0; round < 3; round++) {
    for (const name of ["scalar", "simd"] as const) {
      const started = performance.now();
      exports[name](PARTICLES, REPS);
      const ns = ((performance.now() - started) * 1e6) / (PARTICLES * REPS);
      console.log(`${name.padEnd(7)} ${ns.toFixed(3)} ns per particle`);
    }
  }
}

const dir = process.argv[2];
if (!dir) throw new Error("usage: node web/record-arith.bench.ts DIR | --inner inner_loop.wasm");
if (dir === "--inner") {
  innerLoop(readFileSync(process.argv[3]));
  process.exit(0);
}
for (const file of readdirSync(dir).filter((f) => f.endsWith(".wasm")).sort()) {
  measure(file.replace(/\.wasm$/, ""), readFileSync(join(dir, file)));
}
