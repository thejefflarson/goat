import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { compile, compileLive } from "./compile.ts";
import { type FromWorker, Heartbeat, type ToWorker } from "./protocol.ts";
import { createWorkerCore } from "./worker-core.ts";

const compiler = await WebAssembly.compile(
  readFileSync(new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", import.meta.url)),
);

async function moduleOf(source: string, build = compile) {
  const result = await build(compiler, source);
  if (!result.ok) assert.fail(result.diagnostics);
  return result.module;
}

// An OffscreenCanvas stand-in whose context remembers the calls drawn on it.
function fakeSurface() {
  const calls: string[] = [];
  const context = new Proxy({ canvas: { width: 300, height: 300 } } as Record<string, unknown>, {
    get: (target, key: string) => target[key] ?? ((...args: unknown[]) => calls.push(`${key}(${args.join(",")})`)),
    set: (target, key: string, value) => ((target[key] = value), true),
  });
  const canvas = { width: 300, height: 300, getContext: () => context } as unknown as OffscreenCanvas;
  return { canvas, calls };
}

// A worker with no threads: frames run when the test says, and `heartbeats`
// records the word as each frame sees it.
function worker() {
  const posted: FromWorker[] = [];
  let pending: Array<(time: number) => void> = [];
  const core = createWorkerCore({
    post: (message) => posted.push(message),
    raf: (callback) => pending.push(callback),
    cancelRaf: () => {
      pending = [];
    },
    now: () => 0,
  });
  const frame = (time: number) => {
    const callbacks = pending;
    pending = [];
    callbacks.forEach((callback) => callback(time));
  };
  const run = async (mode: "interactive" | "once", source: string, build = compile) => {
    const surface = fakeSurface();
    const heartbeat = new Heartbeat();
    const message: ToWorker = {
      type: "run",
      mode,
      module: await moduleOf(source, build),
      canvas: surface.canvas,
      heartbeat: heartbeat.buffer,
    };
    await core.handle(message);
    return { ...surface, heartbeat };
  };
  return { core, posted, frame, run };
}

const KEYS = `init = {x: 0}
update = program(model, event) do
  match event do KeyDown(key) then {x: model.x + 10} else model done
done
draw = program(model) do [Line({x1: 0, y1: 0, x2: model.x, y2: 5, color: "red"})] done
`;

test("an interactive program reports ready with the events it subscribed to", async () => {
  const { posted, run } = worker();
  const { heartbeat } = await run("interactive", KEYS);
  assert.deepEqual(posted, [{ type: "ready", subscriptions: ["KeyDown"] }]);
  assert.equal(Heartbeat.busy(heartbeat.read()), false);
  assert.ok(heartbeat.read() > 0, "setup ran inside a heartbeat");
});

test("forwarded input reaches update and the next frame draws the result", async () => {
  const { frame, core, run } = worker();
  const { calls } = await run("interactive", KEYS);
  await core.handle({ type: "input", event: { kind: "KeyDown", key: "x" } });
  await core.handle({ type: "input", event: { kind: "KeyUp", key: "x" } });
  frame(16);
  assert.ok(calls.includes("lineTo(10,5)"), calls.join(" "));
});

test("every call into goat is bracketed by the heartbeat", async () => {
  const { frame, core, run } = worker();
  const { heartbeat } = await run("interactive", KEYS);
  const afterSetup = heartbeat.read();
  await core.handle({ type: "input", event: { kind: "KeyDown", key: "x" } });
  assert.equal(heartbeat.read(), afterSetup + 2);
  frame(16);
  assert.equal(heartbeat.read(), afterSetup + 4);
  assert.equal(Heartbeat.busy(heartbeat.read()), false);
});

test("input before the program is running, or for an unsubscribed event, is dropped", async () => {
  const { core, posted, run } = worker();
  await core.handle({ type: "input", event: { kind: "KeyDown", key: "x" } });
  const { heartbeat } = await run("interactive", KEYS);
  const afterSetup = heartbeat.read();
  await core.handle({ type: "input", event: { kind: "PointerDown", x: 1, y: 1 } });
  assert.equal(heartbeat.read(), afterSetup);
  assert.deepEqual(posted.map((m) => m.type), ["ready"]);
});

test("a trap in setup fails the run and never reports ready", async () => {
  const { posted, run } = worker();
  await run("interactive", `init = {x: first([])}
update = program(model, event) do
  match event do KeyDown(key) then model else model done
done
draw = program(model) do [] done
`);
  assert.equal(posted.some((m) => m.type === "ready"), false);
  assert.equal(posted.length, 1);
  assert.equal(posted[0]!.type, "failed");
});

test("a run-once program posts its output, animates, then finishes", async () => {
  const { posted, frame, run } = worker();
  const pending = run("once", 'print("hello");\nforward(10)');
  while (!posted.some((m) => m.type === "finished")) {
    await new Promise((resolve) => setImmediate(resolve));
    frame(0);
  }
  const { heartbeat, calls } = await pending;
  assert.deepEqual(posted, [{ type: "output", lines: ["hello"] }, { type: "finished" }]);
  assert.ok(calls.some((call) => call.startsWith("lineTo")));
  assert.equal(Heartbeat.busy(heartbeat.read()), false);
  assert.equal(heartbeat.read(), 2);
});

test("a run-once trap is reported as a failure and leaves the heartbeat idle", async () => {
  const { posted, run } = worker();
  const { heartbeat } = await run("once", "first([])");
  assert.equal(posted.length, 1);
  assert.equal(posted[0]!.type, "failed");
  assert.match((posted[0] as Extract<FromWorker, { type: "failed" }>).message, /^your program stopped: /);
  assert.equal(Heartbeat.busy(heartbeat.read()), false);
});

test("a module that cannot be instantiated is a failure, not a crash", async () => {
  const { core, posted } = worker();
  const surface = fakeSurface();
  await core.handle({
    type: "run",
    mode: "interactive",
    module: new Uint8Array([1, 2, 3]),
    canvas: surface.canvas,
    heartbeat: new Heartbeat().buffer,
  });
  assert.equal(posted[0]!.type, "failed");
});

test("a reload refreshes the model when its shape is unchanged and swaps draw", async () => {
  const { core, posted, frame, run } = worker();
  const { calls } = await run("interactive", KEYS, compileLive);
  await core.handle({ type: "input", event: { kind: "KeyDown", key: "x" } });
  await core.handle({ type: "reload", module: await moduleOf(KEYS.replace("y2: 5", "y2: 7"), compileLive) });
  assert.deepEqual(posted.at(-1), { type: "reloaded", outcome: "refreshed", subscriptions: ["KeyDown"] });
  frame(16);
  assert.ok(calls.includes("lineTo(10,7)"), calls.join(" "));
});

test("a reload that changes a field's type starts over from the new init and says why", async () => {
  const { core, posted, frame, run } = worker();
  const { calls } = await run("interactive", KEYS, compileLive);
  await core.handle({ type: "input", event: { kind: "KeyDown", key: "x" } });
  const retyped = KEYS.replace("{x: 0}", "{x: 3, z: 0}")
    .replace("{x: model.x + 10}", "{...model, x: model.x + 10}")
    .replace("x2: model.x", "x2: model.x + model.z");
  await core.handle({ type: "reload", module: await moduleOf(retyped, compileLive) });
  assert.deepEqual(posted.at(-1), { type: "reloaded", outcome: "refreshed", subscriptions: ["KeyDown"] });
  frame(16);
  assert.ok(calls.includes("lineTo(10,5)"), calls.join(" "));

  const text = KEYS.replace("{x: 0}", '{x: "far"}').replace("x2: model.x", "x2: 4").replace("{x: model.x + 10}", "model");
  await core.handle({ type: "reload", module: await moduleOf(text, compileLive) });
  assert.deepEqual(posted.at(-1), {
    type: "reloaded",
    outcome: "reset",
    reason: { kind: "type_changed", args: ["x", "Number", "String"] },
    subscriptions: ["KeyDown"],
  });
});

test("a reload that cannot take the program leaves the old one running", async () => {
  const { core, posted, frame, run } = worker();
  const { calls } = await run("interactive", KEYS, compileLive);
  await core.handle({ type: "reload", module: await moduleOf("forward(10)", compileLive) });
  await core.handle({ type: "reload", module: await moduleOf(KEYS.replace("{x: 0}", "{x: first([])}"), compileLive) });
  assert.deepEqual(posted.slice(1).map((m) => m.type), ["reload_failed", "reload_failed"]);
  frame(16);
  assert.ok(calls.includes("lineTo(0,5)"), calls.join(" "));
});

test("a reload with nothing running, or into a program started the plain way, is refused", async () => {
  const { core, posted, run } = worker();
  await core.handle({ type: "reload", module: await moduleOf(KEYS, compileLive) });
  await run("interactive", KEYS);
  await core.handle({ type: "reload", module: await moduleOf(KEYS, compileLive) });
  assert.deepEqual(posted.map((m) => m.type), ["reload_failed", "ready", "reload_failed"]);
});
