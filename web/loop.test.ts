import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { compile, compileLive } from "./compile.ts";
import {
  FRAME_BUDGET_MS,
  type DomEvent,
  type Hosted,
  type InteractiveExports,
  type LoopCanvas,
  STUCK_MESSAGE,
  createHosted,
  isInteractiveModule,
  isReloadableModule,
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

const trapping = `
init = {n: 0}
update = program(model, event) do
  match event do Tick(dt) then first([]) done
done
draw = program(model) do [] done
`;

test("a trapping update is reported, stops the loop, and the page survives", async () => {
  const { exports } = await instantiate(trapping);
  const page = fakeEnv();
  const loop = startLoop(exports, page.env);
  page.frame(16);
  assert.equal(page.errors.length, 1);
  assert.match(page.errors[0]!, /^your program stopped: /);
  assert.equal(loop.running, false);
  assert.deepEqual(page.registered(), []);
  page.frame(32);
  loop.stop();
  assert.equal(page.errors.length, 1);
});

test("a well-behaved program runs many frames with nothing bounding it", async () => {
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

test("around wraps every call into goat", async () => {
  const { exports } = await instantiate(arrowDraw);
  const page = fakeEnv();
  let calls = 0;
  const loop = startLoop(exports, {
    ...page.env,
    around: (call) => {
      calls++;
      return call();
    },
  });
  loop.send({ kind: "KeyDown", key: "ArrowDown" });
  page.frame(16);
  assert.equal(calls, 3);
  loop.stop();
});

test("a host that supplies `around` sees every call into goat, even one that traps", async () => {
  const calls = { open: 0, closed: 0 };
  const around = <T>(call: () => T): T => {
    calls.open++;
    try {
      return call();
    } finally {
      calls.closed++;
    }
  };
  const fine = await instantiate(arrowDraw);
  const page = fakeEnv();
  const loop = startLoop(fine.exports, { ...page.env, around });
  page.fire("keydown", { key: "ArrowDown" });
  page.frame(16);
  loop.stop();
  assert.ok(calls.open >= 3, "setup, update, and draw each ran inside it");
  assert.equal(calls.open, calls.closed);

  const broken = await instantiate(trapping);
  const runaway = fakeEnv();
  const before = calls.open;
  startLoop(broken.exports, { ...runaway.env, around });
  runaway.frame(16);
  assert.ok(calls.open > before);
  assert.equal(calls.open, calls.closed);
});

async function instantiateLive(source: string, hosted: Hosted, scene = new RecordingScene()) {
  const result = await compileLive(compiler, source);
  if (!result.ok) assert.fail(result.diagnostics);
  const host = createHost(() => hosted.memory);
  const { instance } = await WebAssembly.instantiate(result.module, {
    goat: { ...host.imports.goat, ...hosted },
    ...sceneImports(() => hosted.memory, scene),
  });
  return instance.exports as InteractiveExports & { goat_live_allocs(): number };
}

const counter = (extra: string, drawn: string) => `
init = {x: 0${extra}}
update = program(model, event) do
  match event do KeyDown(key) then {...model, x: model.x + 10} else model done
done
draw = program(model) do [Line({x1: 0, y1: 0, x2: ${drawn}, y2: 0, color: "red"})] done
`;

const lineEnds = (scene: RecordingScene) =>
  scene.commands.flatMap((c) => (c.kind === "line" ? [c.x2] : []));

async function liveProgram(source: string) {
  const hosted = createHosted();
  const scene = new RecordingScene();
  const first = await instantiateLive(source, hosted, scene);
  const page = fakeEnv();
  const loop = startLoop(first, page.env);
  const reload = async (next: string) => loop.reload(await instantiateLive(next, hosted, scene));
  return { hosted, scene, page, loop, first, reload };
}

test("only an interactive program compiles reloadable", async () => {
  const module = async (source: string) => {
    const result = await compileLive(compiler, source);
    if (!result.ok) assert.fail(result.diagnostics);
    return WebAssembly.compile(result.module);
  };
  assert.equal(isReloadableModule(await module(arrowDraw)), true);
  assert.equal(isReloadableModule(await module("forward(10)")), false);
});

test("a reload that leaves the model's shape alone refreshes the model and swaps draw", async () => {
  const { scene, page, loop, first, reload } = await liveProgram(counter("", "model.x"));
  loop.send({ kind: "KeyDown", key: "a" });
  loop.send({ kind: "KeyDown", key: "a" });
  page.frame(16);
  assert.deepEqual(await reload(counter("", "model.x * 2")), { outcome: "refreshed" });
  page.frame(32);
  assert.deepEqual(lineEnds(scene), [20, 40]);
  loop.send({ kind: "KeyDown", key: "a" });
  page.frame(48);
  assert.deepEqual(lineEnds(scene), [20, 40, 60]);
  loop.stop();
  assert.equal(first.goat_live_allocs(), 0);
  assert.deepEqual(page.errors, []);
});

test("a field the new program adds comes from its init, and the model carries on", async () => {
  const { scene, page, loop, first, reload } = await liveProgram(counter("", "model.x"));
  loop.send({ kind: "KeyDown", key: "a" });
  assert.deepEqual(await reload(counter(", y: 5", "model.x + model.y")), { outcome: "refreshed" });
  page.frame(16);
  assert.deepEqual(lineEnds(scene), [15]);
  loop.stop();
  assert.equal(first.goat_live_allocs(), 0);
  assert.deepEqual(page.errors, []);
});

test("a field that changes type starts over from the new init, and the reason names both types", async () => {
  const { scene, page, loop, first, reload } = await liveProgram(counter("", "model.x"));
  loop.send({ kind: "KeyDown", key: "a" });
  const text = counter("", "5").replace("{x: 0}", '{x: "far"}').replace("{...model, x: model.x + 10}", "model");
  assert.deepEqual(await reload(text), {
    outcome: "reset",
    reason: { kind: "type_changed", args: ["x", "Number", "String"] },
  });
  page.frame(16);
  assert.deepEqual(lineEnds(scene), [5]);
  loop.stop();
  assert.equal(first.goat_live_allocs(), 0);
  assert.deepEqual(page.errors, []);
});

const balls = (speed: number, make = "make_ball") => `
speed = ${speed}
${make} = program(x) do
  {x: x, update: program(self) do {...self, x: self.x + speed} done}
done
init = {tick: 0, balls: [${make}(0), ${make}(10)]}
update = program(model, event) do
  match event do
    KeyDown(key) then {...model, tick: model.tick + 1, balls: change_each(model.balls, program(b) do b.update() done)}
    else model
  done
done
draw = program(model) do change_each(model.balls, program(b) do Line({x1: b.x, y1: 0, x2: b.x, y2: 1, color: "red"}) done) done
`;

test("a reload rebinds each method to the new program's closure and keeps the data", async () => {
  const { scene, page, loop, first, reload } = await liveProgram(balls(5));
  loop.send({ kind: "KeyDown", key: "a" });
  assert.deepEqual(await reload(balls(7)), { outcome: "refreshed" });
  loop.send({ kind: "KeyDown", key: "a" });
  page.frame(16);
  assert.deepEqual(lineEnds(scene), [12, 22]);
  loop.stop();
  assert.equal(first.goat_live_allocs(), 0);
  assert.deepEqual(page.errors, []);
});

test("renaming the binding that made a method resets the model and names the binding that is gone", async () => {
  const { scene, page, loop, first, reload } = await liveProgram(balls(5));
  loop.send({ kind: "KeyDown", key: "a" });
  assert.deepEqual(await reload(balls(5, "new_ball")), {
    outcome: "reset",
    reason: { kind: "binding_gone", args: ["make_ball"] },
  });
  page.frame(16);
  assert.deepEqual(lineEnds(scene), [0, 10]);
  loop.stop();
  assert.equal(first.goat_live_allocs(), 0);
  assert.deepEqual(page.errors, []);
});

test("many reloads leave the live count and the heap's high-water mark where the first left them", async () => {
  const { hosted, page, loop, first, reload } = await liveProgram(balls(1));
  const marks: Array<[number, number]> = [];
  for (let round = 2; round < 10; round++) {
    loop.send({ kind: "KeyDown", key: "a" });
    assert.equal((await reload(balls(round))).outcome, "refreshed");
    marks.push([first.goat_live_allocs(), hosted.heap.value as number]);
  }
  assert.deepEqual(marks.slice(1), marks.slice(1).map(() => marks[1]));
  loop.stop();
  assert.equal(first.goat_live_allocs(), 0);
  assert.deepEqual(page.errors, []);
});

test("a reloaded program that cannot start leaves the old one running", async () => {
  const { scene, page, loop, reload } = await liveProgram(counter("", "model.x"));
  loop.send({ kind: "KeyDown", key: "a" });
  await assert.rejects(reload(counter("", "model.x").replace("{x: 0}", "{x: first([])}")));
  assert.equal(loop.running, true);
  page.frame(16);
  assert.deepEqual(lineEnds(scene), [10]);
  assert.deepEqual(page.errors, []);
});
