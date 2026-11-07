import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { compile } from "./compile.ts";
import { createHost } from "./runtime.ts";
import {
  CanvasScene,
  type DrawingContext,
  RecordingScene,
  constructEvent,
  newString,
  sceneImports,
  subscriptions,
} from "./scene.ts";

const compilerWasm = new URL(
  "../target/wasm32-unknown-unknown/release/goat_web.wasm",
  import.meta.url,
);
const compiler = await WebAssembly.compile(readFileSync(compilerWasm));

async function compileOk(source: string) {
  const result = await compile(compiler, source);
  if (!result.ok) assert.fail(result.diagnostics);
  return result.module;
}

// A 2D context that logs each call, and each stroke color as it is set.
function recordingContext() {
  const calls: string[] = [];
  const log = (name: string) => (...args: number[]) => calls.push(`${name}(${args.join(", ")})`);
  const ctx = {
    canvas: { width: 300, height: 200 },
    lineWidth: 0,
    lineCap: "butt",
    lineJoin: "miter",
    set strokeStyle(color: string) {
      calls.push(`strokeStyle=${color}`);
    },
    save: log("save"),
    restore: log("restore"),
    clearRect: log("clearRect"),
    beginPath: log("beginPath"),
    moveTo: log("moveTo"),
    lineTo: log("lineTo"),
    stroke: log("stroke"),
  };
  return { ctx: ctx as unknown as DrawingContext, calls };
}

test("a frame clears, strokes each shape as a path, and restores the context", () => {
  const { ctx, calls } = recordingContext();
  const scene = new CanvasScene(ctx);
  scene.begin();
  scene.line(0, 1, 2, 3, "red");
  scene.polylineBegin("#0a0");
  scene.vertex(5, 6);
  scene.vertex(7, 8);
  scene.vertex(9, 10);
  scene.polylineEnd();
  scene.end();
  assert.deepEqual(calls, [
    "save()",
    "clearRect(0, 0, 300, 200)",
    "strokeStyle=red",
    "beginPath()",
    "moveTo(0, 1)",
    "lineTo(2, 3)",
    "stroke()",
    "strokeStyle=#0a0",
    "beginPath()",
    "moveTo(5, 6)",
    "lineTo(7, 8)",
    "lineTo(9, 10)",
    "stroke()",
    "restore()",
  ]);
});

test("each polyline starts a new path at its first vertex", () => {
  const { ctx, calls } = recordingContext();
  const scene = new CanvasScene(ctx);
  for (const x of [1, 2]) {
    scene.polylineBegin("blue");
    scene.vertex(x, x);
    scene.vertex(x + 1, x + 1);
    scene.polylineEnd();
  }
  assert.equal(calls.filter((c) => c.startsWith("moveTo")).length, 2);
  assert.equal(calls.filter((c) => c.startsWith("lineTo")).length, 2);
});

test("the scene imports refuse a color outside the allowlist and a non-finite number", () => {
  const memory = new WebAssembly.Memory({ initial: 1 });
  const exports = {
    memory,
    goat_alloc: (size: number) => 64 + 0 * size,
  } as unknown as WebAssembly.Exports;
  const { scene } = sceneImports(() => memory, new RecordingScene());
  scene.line(0, 0, 1, 1, newString(exports, "red"));
  assert.throws(() => scene.line(0, 0, 1, 1, newString(exports, "re d")), /color wants a name/);
  assert.throws(() => scene.polyline_begin(newString(exports, "a".repeat(33))), /color wants a name/);
  assert.throws(() => scene.vertex(Number.NaN, 1), /real number/);
});

async function instantiate(source: string) {
  const scene = new RecordingScene();
  let memory: WebAssembly.Memory | undefined;
  const host = createHost(() => memory!);
  const { instance } = await WebAssembly.instantiate(await compileOk(source), {
    ...host.imports,
    ...sceneImports(() => memory!, scene),
  });
  memory = instance.exports.memory as WebAssembly.Memory;
  return { exports: instance.exports, scene };
}

type Exports = WebAssembly.Exports & {
  goat_setup(): number;
  goat_update(model: number, event: number): number;
  goat_draw(model: number): void;
  goat_release_model(model: number): void;
  goat_shutdown(): void;
  goat_live_allocs(): number;
};

const example = readFileSync(new URL("../examples/interactive.goat", import.meta.url), "utf8");

test("the module is subscribed to exactly the events update handles", async () => {
  const { exports } = await instantiate(example);
  assert.deepEqual(subscriptions(exports), ["Tick", "KeyDown"]);
  assert.equal(constructEvent(exports, { kind: "KeyUp", key: "a" }), null);
});

test("goat_event_KeyDown maps ArrowUp to the Up branch and the scene follows", async () => {
  const { exports: raw, scene } = await instantiate(example);
  const exports = raw as Exports;
  let model = exports.goat_setup();
  for (const key of ["ArrowUp", "ArrowRight", "x"]) {
    model = exports.goat_update(model, constructEvent(exports, { kind: "KeyDown", key })!);
    exports.goat_draw(model);
  }
  const lines = scene.commands.filter((c) => c.kind === "line");
  assert.deepEqual(
    lines.map((c) => [c.x2, c.y2]),
    [
      [0, -10],
      [10, -10],
      [10, -10],
    ],
  );
  assert.deepEqual(scene.commands.slice(0, 8), [
    { kind: "begin" },
    { kind: "line", x1: 0, y1: 0, x2: 0, y2: -10, color: "red" },
    { kind: "polyline_begin", color: "blue" },
    { kind: "vertex", x: 0, y: 0 },
    { kind: "vertex", x: 0, y: 0 },
    { kind: "vertex", x: 0, y: -10 },
    { kind: "polyline_end" },
    { kind: "end" },
  ]);
  exports.goat_release_model(model);
  exports.goat_shutdown();
  assert.equal(exports.goat_live_allocs(), 0);
});

test("Tick, pointer events and numbers reach their constructors", async () => {
  const { exports: raw, scene } = await instantiate(`
init = {x: 0, y: 0}
update = program(model, event) do
  match event do
    Tick(dt) then {x: model.x + dt, y: model.y}
    PointerDown(p) then {x: p.x, y: p.y}
  else model done
done
draw = program(model) do
  [Line({x1: 0, y1: 0, x2: model.x, y2: model.y, color: "black"})]
done
`);
  const exports = raw as Exports;
  assert.deepEqual(subscriptions(exports), ["Tick", "PointerDown"]);
  let model = exports.goat_setup();
  for (const event of [
    { kind: "Tick", dt: 2.5 },
    { kind: "PointerDown", x: 7, y: 9 },
    { kind: "Tick", dt: 1 },
  ] as const) {
    model = exports.goat_update(model, constructEvent(exports, event)!);
    exports.goat_draw(model);
  }
  const ends = scene.commands.flatMap((c) => (c.kind === "line" ? [[c.x2, c.y2]] : []));
  assert.deepEqual(ends, [[2.5, 0], [7, 9], [8, 9]]);
  exports.goat_release_model(model);
  exports.goat_shutdown();
  assert.equal(exports.goat_live_allocs(), 0);
});
