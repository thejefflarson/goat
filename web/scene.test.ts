import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { compile, compileEditor } from "./compile.ts";
import { createHost } from "./runtime.ts";
import {
  CanvasScene,
  type DrawingContext,
  MAX_SPANS,
  MAX_SWATCHES,
  RecordingScene,
  SpanScene,
  SwatchScene,
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
    font: "",
    textBaseline: "alphabetic",
    set strokeStyle(color: string) {
      calls.push(`strokeStyle=${color}`);
    },
    set fillStyle(color: string) {
      calls.push(`fillStyle=${color}`);
    },
    save: log("save"),
    restore: log("restore"),
    clearRect: log("clearRect"),
    beginPath: log("beginPath"),
    moveTo: log("moveTo"),
    lineTo: log("lineTo"),
    stroke: log("stroke"),
    arc: log("arc"),
    fill: log("fill"),
    fillRect: log("fillRect"),
    fillText: log("fillText"),
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

test("circles and rects are filled, text is drawn from its top left, all in canvas coordinates", () => {
  const { ctx, calls } = recordingContext();
  const scene = new CanvasScene(ctx);
  scene.begin();
  scene.circle(5, 6, 7, "blue");
  scene.rect(1, 2, 30, 40, "#fa0");
  scene.text(8, 9, "goat", "black");
  scene.end();
  assert.equal((ctx as unknown as { textBaseline: string }).textBaseline, "top");
  assert.deepEqual(calls.slice(2, -1), [
    "fillStyle=blue",
    "beginPath()",
    `arc(5, 6, 7, 0, ${2 * Math.PI})`,
    "fill()",
    "fillStyle=#fa0",
    "fillRect(1, 2, 30, 40)",
    "fillStyle=black",
    "fillText(goat, 8, 9)",
  ]);
});

test("a circle with a negative radius draws nothing", () => {
  const { ctx, calls } = recordingContext();
  new CanvasScene(ctx).circle(0, 0, -1, "red");
  assert.deepEqual(calls, []);
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
  assert.throws(() => scene.circle(0, 0, Number.POSITIVE_INFINITY, newString(exports, "red")), /real number/);
  assert.throws(() => scene.rect(0, 0, 1, Number.NaN, newString(exports, "red")), /real number/);
  assert.throws(() => scene.text(Number.NaN, 0, newString(exports, "hi"), newString(exports, "red")), /real number/);
  assert.throws(() => scene.circle(0, 0, 1, newString(exports, "re d")), /color wants a name/);
  assert.throws(() => scene.rect(0, 0, 1, 1, newString(exports, "re d")), /color wants a name/);
  assert.throws(() => scene.text(0, 0, newString(exports, "hi"), newString(exports, "re d")), /color wants a name/);
});

test("the text import reads its string from module memory", () => {
  const memory = new WebAssembly.Memory({ initial: 1 });
  let next = 64;
  const exports = {
    memory,
    goat_alloc: (size: number) => {
      const ptr = next;
      next += size;
      return ptr;
    },
  } as unknown as WebAssembly.Exports;
  const recording = new RecordingScene();
  const { scene } = sceneImports(() => memory, recording);
  scene.text(1, 2, newString(exports, "héllo ☃"), newString(exports, "red"));
  assert.deepEqual(recording.commands, [{ kind: "text", x: 1, y: 2, text: "héllo ☃", color: "red" }]);
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

const shapes = readFileSync(new URL("../examples/shapes.goat", import.meta.url), "utf8");

test("a draw of Rect, Circle and Text reaches the scene in order", async () => {
  const { exports: raw, scene } = await instantiate(shapes);
  const exports = raw as Exports;
  let model = exports.goat_setup();
  model = exports.goat_update(model, constructEvent(exports, { kind: "Tick", dt: 16 })!);
  exports.goat_draw(model);
  assert.deepEqual(scene.commands, [
    { kind: "begin" },
    { kind: "rect", x: 10, y: 10, w: 200, h: 80, color: "#fa0" },
    { kind: "circle", x: 50, y: 50, r: 20, color: "blue" },
    { kind: "text", x: 20, y: 20, text: "goat", color: "black" },
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

test("an editor program's spans reach the scene as numbers, and take empties the frame", async () => {
  const module = await compileEditor(
    compiler,
    `init = {n: 0}
update = program(m, e) do match e do Edited(x) then {n: 7} else m done done
draw = program(m) do [Span({from: 1, to: 3, kind: "keyword"}), Span({from: 4, to: 9, kind: "<evil>"})] done`,
  );
  assert.ok(module.ok);
  const scene = new SpanScene();
  let memory: WebAssembly.Memory | undefined;
  const { instance } = await WebAssembly.instantiate(module.module, {
    goat: createHost(() => memory!).imports.goat,
    ...sceneImports(() => memory!, scene),
  });
  memory = instance.exports.memory as WebAssembly.Memory;
  const exports = instance.exports as unknown as {
    goat_setup(): number;
    goat_update(model: number, event: number): number;
    goat_draw(model: number): void;
  };
  const edited = constructEvent(instance.exports, { kind: "Edited", text: "hello", cursor: 2 });
  assert.notEqual(edited, null);
  const model = exports.goat_update(exports.goat_setup(), edited!);
  exports.goat_draw(model);
  assert.deepEqual(scene.take(), [
    { from: 1, to: 3, kind: "keyword" },
    { from: 4, to: 9, kind: "<evil>" },
  ]);
  assert.deepEqual(scene.take(), []);
});

test("a frame with more spans than the cap traps the program", () => {
  const scene = new SpanScene();
  for (let i = 0; i < MAX_SPANS; i++) scene.span(i, i + 1, "number");
  assert.throws(() => scene.span(0, 1, "number"), /more than/);
  scene.begin();
  scene.span(0, 1, "number");
  assert.equal(scene.take().length, 1);
});

test("a theme with more swatches than the cap traps the program", () => {
  const scene = new SwatchScene();
  for (let i = 0; i < MAX_SWATCHES; i++) scene.swatch("keyword", "red", "blue");
  assert.throws(() => scene.swatch("keyword", "red", "blue"), /more than/);
  scene.begin();
  scene.swatch("keyword", "red", "blue");
  assert.deepEqual(scene.take(), [{ role: "keyword", light: "red", dark: "blue" }]);
});

test("the editor's events are subscriptions, and Edited and HostTags build with their payloads", async () => {
  const module = await compileEditor(
    compiler,
    `init = {n: 0}
update = program(m, e) do match e do Edited(x) then m HostTags(h) then m else m done done
draw = program(m) do [] done`,
  );
  assert.ok(module.ok);
  let memory: WebAssembly.Memory | undefined;
  const { instance } = await WebAssembly.instantiate(module.module, {
    goat: createHost(() => memory!).imports.goat,
    ...sceneImports(() => memory!, new SpanScene()),
  });
  memory = instance.exports.memory as WebAssembly.Memory;
  assert.deepEqual(subscriptions(instance.exports).sort(), ["Edited", "HostTags"]);
  for (const event of [
    { kind: "Edited", text: "\u00e9", cursor: 1 },
    { kind: "HostTags", names: "Dot Box" },
  ] as const) {
    assert.equal(typeof constructEvent(instance.exports, event), "number", event.kind);
  }
});
