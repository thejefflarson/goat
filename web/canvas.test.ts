import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { check, compile, compileLive } from "./compile.ts";
import { type InteractiveExports, type LoopEnv, startLoop } from "./loop.ts";
import { createHost } from "./runtime.ts";
import { RecordingScene, type SceneCommand, sceneImports, subscriptions } from "./scene.ts";

const compiler = await WebAssembly.compile(
  readFileSync(new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", import.meta.url)),
);

const example = (name: string) => readFileSync(new URL(`../examples/canvas/${name}.goat`, import.meta.url), "utf8");

async function start(source: string) {
  const result = await compile(compiler, source, "canvas");
  if (!result.ok) assert.fail(result.diagnostics);
  const scene = new RecordingScene();
  let memory: WebAssembly.Memory | undefined;
  const { instance } = await WebAssembly.instantiate(result.module, {
    goat: createHost(() => memory!).imports.goat,
    ...sceneImports(() => memory!, scene),
  });
  memory = instance.exports.memory as WebAssembly.Memory;
  const exports = instance.exports as InteractiveExports & { goat_live_allocs(): number };

  let pending: Array<(time: number) => void> = [];
  const errors: string[] = [];
  const nowhere = { addEventListener() {}, removeEventListener() {} };
  const env: LoopEnv = {
    canvas: { ...nowhere, width: 400, height: 300, getBoundingClientRect: () => ({ left: 0, top: 0, width: 400, height: 300 }) },
    keys: nowhere,
    raf: (callback) => pending.push(callback),
    cancelRaf: () => {
      pending = [];
    },
    now: () => 0,
    onError: (message) => errors.push(message),
  };
  const loop = startLoop(exports, env);
  const frame = (time: number) => {
    const callbacks = pending;
    pending = [];
    scene.commands.length = 0;
    callbacks.forEach((callback) => callback(time));
    return scene.commands.slice();
  };
  return { exports, loop, frame, errors };
}

const kinds = (commands: SceneCommand[]) => commands.map((c) => c.kind);

test("the canvas entry compiles what the turtle entry rejects, and the reverse", async () => {
  const bounce = example("bounce");
  assert.ok((await compile(compiler, bounce, "canvas")).ok);
  assert.ok((await compileLive(compiler, bounce, "canvas")).ok);
  assert.ok(!(await compile(compiler, bounce)).ok);
  assert.ok(!(await compile(compiler, "forward(10)", "canvas")).ok);
  assert.deepEqual(await check(compiler, bounce, "canvas"), []);
  assert.ok((await check(compiler, bounce)).length > 0);
  assert.ok((await check(compiler, "forward(10)", "canvas")).length > 0);
});

test("a canvas script subscribes under the canvas host's event names", async () => {
  const bounce = await start(example("bounce"));
  assert.deepEqual(subscriptions(bounce.exports), ["Tick"]);
  const catching = await start(example("catch"));
  assert.deepEqual(subscriptions(catching.exports), ["Tick", "KeyDown", "PointerMove"]);
});

test("Frame events move the ball and each frame streams Box, Segment and Dot", async () => {
  const { exports, loop, frame, errors } = await start(example("bounce"));
  const dot = (commands: SceneCommand[]) => commands.find((c) => c.kind === "circle");
  const first = frame(0);
  assert.deepEqual(kinds(first), ["begin", "rect", "line", "circle", "end"]);
  assert.deepEqual(
    first.map((c) => ("color" in c ? c.color : undefined)).filter(Boolean),
    ["green", "gray", "tomato"],
  );
  assert.deepEqual(dot(first), { kind: "circle", x: 40, y: 30, r: 20, color: "tomato" });
  loop.send({ kind: "Tick", dt: 100 });
  const moved = dot(frame(16));
  assert.ok(moved && moved.kind === "circle" && moved.x > 40 && moved.y > 30);
  loop.stop();
  assert.equal(exports.goat_live_allocs(), 0);
  assert.deepEqual(errors, []);
});

test("key and pointer events reach the canvas script's update", async () => {
  const { loop, frame, errors } = await start(example("catch"));
  const basket = (commands: SceneCommand[]) => {
    const rect = commands.find((c) => c.kind === "rect");
    return rect?.kind === "rect" ? rect.x + rect.w / 2 : NaN;
  };
  assert.equal(basket(frame(0)), 200);
  loop.send({ kind: "KeyDown", key: "ArrowLeft" });
  assert.equal(basket(frame(16)), 180);
  loop.send({ kind: "KeyDown", key: "ArrowRight" });
  loop.send({ kind: "KeyDown", key: "ArrowRight" });
  assert.equal(basket(frame(32)), 220);
  loop.send({ kind: "PointerMove", x: 100, y: 270 });
  assert.equal(basket(frame(48)), 100);
  loop.send({ kind: "KeyDown", key: "q" });
  assert.equal(basket(frame(64)), 100);
  assert.deepEqual(errors, []);
});

test("a fill outside the color allowlist traps the program", async () => {
  const { errors, frame } = await start(`
init = {n: 0}
update = program(model, event) do match event do Frame(dt) then model else model done done
draw = program(model) do [Dot({x: 1, y: 1, r: 1, fill: "not-a-color"})] done
`);
  frame(0);
  assert.equal(errors.length, 1);
  assert.match(errors[0]!, /color/);
});

test("the sky draws each thing with its own look method from a model that holds only the clock", async () => {
  const { exports, loop, frame, errors } = await start(example("sky"));
  const dots = (commands: SceneCommand[]) => commands.filter((c) => c.kind === "circle");
  const first = frame(0);
  assert.deepEqual(kinds(first), ["begin", "rect", "circle", "circle", "circle", "circle", "circle", "end"]);
  assert.deepEqual(
    dots(first).map((c) => ("color" in c ? c.color : undefined)),
    ["gold", "white", "white", "white", "white"],
  );
  assert.deepEqual(dots(first)[0], { kind: "circle", x: 90, y: 90, r: 30, color: "gold" });
  loop.send({ kind: "Tick", dt: 150 });
  const later = dots(frame(16));
  assert.notDeepEqual(later[0], dots(first)[0]);
  assert.notDeepEqual(later[1], dots(first)[1]);
  loop.stop();
  assert.equal(exports.goat_live_allocs(), 0);
  assert.deepEqual(errors, []);
});

test("the editor page offers the sky example exactly as the file reads", () => {
  const page = readFileSync(new URL("./index.html", import.meta.url), "utf8");
  assert.ok(page.includes(`    sky: \`${example("sky")}\`,`));
  assert.ok(page.includes('<option value="sky">'));
});
