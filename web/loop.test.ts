import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { compile } from "./compile.ts";
import {
  FRAME_BUDGET_MS,
  type DomEvent,
  type InteractiveExports,
  type LoopCanvas,
  STUCK_MESSAGE,
  isInteractiveModule,
  startLoop,
} from "./loop.ts";
import { createHost } from "./runtime.ts";
import { RecordingScene, sceneImports } from "./scene.ts";

const compiler = await WebAssembly.compile(
  readFileSync(new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", import.meta.url)),
);

async function instantiate(source: string) {
  const result = await compile(compiler, source);
  if (!result.ok) assert.fail(result.diagnostics);
  const scene = new RecordingScene();
  let memory: WebAssembly.Memory | undefined;
  const host = createHost(() => memory!);
  const { instance } = await WebAssembly.instantiate(result.module, {
    goat: host.imports.goat,
    ...sceneImports(() => memory!, scene),
  });
  memory = instance.exports.memory as WebAssembly.Memory;
  return { exports: instance.exports as InteractiveExports & { goat_live_allocs(): number }, scene };
}

type Listener = (event: DomEvent) => void;

// A page with no DOM: listeners are recorded, frames run when the test says.
function fakeEnv(rect = { left: 0, top: 0, width: 300, height: 300 }, step = 0) {
  const listeners = new Map<string, Listener[]>();
  const target = {
    addEventListener(type: string, listener: Listener) {
      listeners.set(type, [...(listeners.get(type) ?? []), listener]);
    },
    removeEventListener(type: string, listener: Listener) {
      listeners.set(type, (listeners.get(type) ?? []).filter((l) => l !== listener));
    },
  };
  const canvas: LoopCanvas = { ...target, width: 300, height: 300, getBoundingClientRect: () => rect };
  const keys = { ...target, addEventListener: canvas.addEventListener, removeEventListener: canvas.removeEventListener };
  let pending: Array<(time: number) => void> = [];
  let clock = 0;
  const errors: string[] = [];
  const env = {
    canvas,
    keys,
    raf: (callback: (time: number) => void) => pending.push(callback),
    cancelRaf: () => {
      pending = [];
    },
    now: () => (clock += step),
    onError: (message: string) => errors.push(message),
  };
  const fire = (type: string, event: DomEvent) => (listeners.get(type) ?? []).forEach((l) => l(event));
  const frame = (time: number) => {
    const callbacks = pending;
    pending = [];
    callbacks.forEach((callback) => callback(time));
  };
  const registered = () => [...listeners].filter(([, ls]) => ls.length > 0).map(([type]) => type);
  return { env, fire, frame, errors, registered };
}

const arrowDraw = readFileSync(new URL("../examples/arrow_draw.goat", import.meta.url), "utf8");

test("a module is interactive when it exports goat_setup", async () => {
  const compileModule = async (source: string) => {
    const result = await compile(compiler, source);
    if (!result.ok) assert.fail(result.diagnostics);
    return WebAssembly.compile(result.module);
  };
  assert.equal(isInteractiveModule(await compileModule(arrowDraw)), true);
  assert.equal(isInteractiveModule(await compileModule("forward(10)")), false);
});

test("a key press reaches update and the next frame draws the longer trail", async () => {
  const { exports, scene } = await instantiate(arrowDraw);
  const page = fakeEnv();
  const loop = startLoop(exports, page.env);
  assert.deepEqual(page.registered(), ["keydown"]);
  let prevented = 0;
  page.fire("keydown", { key: "ArrowRight", preventDefault: () => prevented++ });
  page.fire("keydown", { key: "ArrowUp" });
  page.fire("keydown", { key: "q" });
  page.frame(16);
  assert.equal(prevented, 1);
  const vertices = scene.commands.flatMap((c) => (c.kind === "vertex" ? [[c.x, c.y]] : []));
  assert.deepEqual(vertices, [[10, -10], [10, 0], [0, 0]]);
  assert.deepEqual(scene.commands.map((c) => c.kind).filter((k) => k === "begin" || k === "end"), ["begin", "end"]);
  loop.stop();
  assert.equal(exports.goat_live_allocs(), 0);
  assert.deepEqual(page.registered(), []);
  assert.deepEqual(page.errors, []);
});

test("only the sources the module subscribed to are wired", async () => {
  const { exports } = await instantiate(`
init = {x: 0}
update = program(model, event) do
  match event do
    PointerDown(p) then {x: p.x}
    KeyUp(k) then model
  else model done
done
draw = program(model) do [] done
`);
  const page = fakeEnv();
  startLoop(exports, page.env);
  assert.deepEqual(page.registered().sort(), ["keyup", "pointerdown"]);
});

test("Tick carries the frame delta and pointer events are canvas-relative", async () => {
  const { exports, scene } = await instantiate(`
init = {t: 0, x: 0, y: 0}
update = program(model, event) do
  match event do
    Tick(dt) then {t: model.t + dt, x: model.x, y: model.y}
    PointerMove(p) then {t: model.t, x: p.x, y: p.y}
  else model done
done
draw = program(model) do
  [Line({x1: model.t, y1: 0, x2: model.x, y2: model.y, color: "black"})]
done
`);
  const page = fakeEnv({ left: 50, top: 20, width: 150, height: 150 });
  startLoop(exports, page.env);
  page.frame(100);
  page.frame(116);
  page.frame(150);
  page.fire("pointermove", { clientX: 125, clientY: 95 });
  page.frame(160);
  const lines = scene.commands.flatMap((c) => (c.kind === "line" ? [[c.x1, c.x2, c.y2]] : []));
  assert.deepEqual(lines, [[0, 0, 0], [16, 0, 0], [50, 0, 0], [60, 150, 150]]);
});

const spinning = `
init = {n: 0}
spin = program(n) do if n < 0 then n else spin(n + 1) done done
update = program(model, event) do
  match event do Tick(dt) then {n: spin(0)} done
done
draw = program(model) do [] done
`;

test("a runaway update is stopped by fuel, reported as stuck, and the page survives", async () => {
  const { exports } = await instantiate(spinning);
  const page = fakeEnv();
  const loop = startLoop(exports, page.env);
  page.frame(16);
  assert.deepEqual(page.errors, [STUCK_MESSAGE]);
  assert.equal(loop.running, false);
  assert.deepEqual(page.registered(), []);
  page.frame(32);
  loop.stop();
  assert.deepEqual(page.errors, [STUCK_MESSAGE]);
});

test("refilled fuel lets a well-behaved program run many frames", async () => {
  const { exports } = await instantiate(arrowDraw);
  const page = fakeEnv();
  const loop = startLoop(exports, page.env);
  for (let i = 0; i < 500; i++) {
    page.fire("keydown", { key: "ArrowDown" });
    page.frame(i);
  }
  assert.equal(loop.running, true);
  loop.stop();
  assert.equal(exports.goat_live_allocs(), 0);
  assert.deepEqual(page.errors, []);
});

test("an update that returns but overruns the frame budget stops the loop", async () => {
  const { exports } = await instantiate(arrowDraw);
  const page = fakeEnv(undefined, FRAME_BUDGET_MS + 1);
  const loop = startLoop(exports, page.env);
  assert.equal(loop.running, false);
  assert.deepEqual(page.errors, [STUCK_MESSAGE]);
});

test("send delivers a host event without any DOM listener", async () => {
  const { exports, scene } = await instantiate(arrowDraw);
  const page = fakeEnv();
  const loop = startLoop(exports, page.env);
  loop.send({ kind: "KeyDown", key: "ArrowRight" });
  loop.send({ kind: "KeyUp", key: "ArrowRight" });
  page.frame(16);
  const vertices = scene.commands.flatMap((c) => (c.kind === "vertex" ? [[c.x, c.y]] : []));
  assert.deepEqual(vertices, [[10, 0], [0, 0]]);
  loop.stop();
  loop.send({ kind: "KeyDown", key: "ArrowRight" });
  assert.deepEqual(page.errors, []);
});

test("around wraps every call into goat and fuelBudget sets the refill", async () => {
  const { exports } = await instantiate(arrowDraw);
  const page = fakeEnv();
  const seen: number[] = [];
  const loop = startLoop(exports, {
    ...page.env,
    fuelBudget: 12345,
    around: (call) => {
      seen.push(exports.goat_fuel.value as number);
      return call();
    },
  });
  loop.send({ kind: "KeyDown", key: "ArrowDown" });
  page.frame(16);
  assert.equal(seen.length, 3);
  assert.deepEqual([...new Set(seen)], [12345]);
  loop.stop();
});
