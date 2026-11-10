import assert from "node:assert/strict";
import test from "node:test";
import { STUCK_MESSAGE } from "./loop.ts";
import { type FromWorker, Heartbeat, type ToWorker } from "./protocol.ts";
import {
  type Job,
  MAX_RESTARTS,
  RUN_ONCE_STOPPED_MESSAGE,
  type RunSink,
  Supervisor,
  type WorkerLike,
} from "./supervisor.ts";

const capable = { crossOriginIsolated: true, SharedArrayBuffer, Worker: class {}, OffscreenCanvas: class {} };
const LIMITS = { frameMs: 1000, onceMs: 5000, pollMs: 100 };
const interactive: Job = { mode: "interactive", module: new Uint8Array(0) };
const once: Job = { mode: "once", module: new Uint8Array(0) };

class FakeWorker implements WorkerLike {
  posted: Array<{ message: ToWorker; transfer?: Transferable[] }> = [];
  terminated = false;
  onmessage: WorkerLike["onmessage"] = null;
  onerror: WorkerLike["onerror"] = null;

  postMessage(message: ToWorker, transfer?: Transferable[]) {
    this.posted.push({ message, transfer });
  }
  terminate() {
    this.terminated = true;
  }
  emit(data: FromWorker) {
    this.onmessage?.({ data });
  }
  // The worker's side of the heartbeat, from the buffer the supervisor handed over.
  get heartbeat() {
    const run = this.posted.find((p) => p.message.type === "run")!.message;
    assert.equal(run.type, "run");
    return new Heartbeat((run as Extract<ToWorker, { type: "run" }>).heartbeat);
  }
  get inputs() {
    return this.posted.flatMap((p) => (p.message.type === "input" ? [p.message.event] : []));
  }
}

function harness(limits = LIMITS) {
  let clock = 0;
  const workers: FakeWorker[] = [];
  const timers: Array<{ tick: () => void; active: boolean; ms: number }> = [];
  const surfaces: object[] = [];
  const supervisor = new Supervisor(
    {
      spawn: () => {
        const worker = new FakeWorker();
        workers.push(worker);
        return worker;
      },
      surface: () => {
        const surface = {};
        surfaces.push(surface);
        return surface as OffscreenCanvas;
      },
      now: () => clock,
      every: (ms, tick) => {
        const timer = { tick, active: true, ms };
        timers.push(timer);
        return () => (timer.active = false);
      },
    },
    capable,
    limits,
  );
  const events: string[] = [];
  const sink: RunSink = {
    onReady: () => events.push("ready"),
    onOutput: (lines) => events.push(`output:${lines.join("|")}`),
    onFinished: () => events.push("finished"),
    onFailed: (message) => events.push(`failed:${message}`),
  };
  // Lets `ms` of wall-clock time pass, polling as the page's timer would.
  const advance = (ms: number) => {
    for (let elapsed = 0; elapsed < ms; elapsed += limits.pollMs) {
      clock += limits.pollMs;
      timers.filter((t) => t.active).forEach((t) => t.tick());
    }
  };
  const last = () => workers[workers.length - 1]!;
  return { supervisor, workers, timers, surfaces, events, sink, advance, last };
}

test("a page that is not cross-origin isolated is refused with the reason", () => {
  const env = { spawn: () => new FakeWorker(), surface: () => ({}) as OffscreenCanvas, now: () => 0, every: () => () => {} };
  assert.throws(() => new Supervisor(env, { ...capable, crossOriginIsolated: false }), /cross-origin isolated/);
  assert.throws(() => new Supervisor(env, { ...capable, SharedArrayBuffer: undefined }), /SharedArrayBuffer/);
});

test("start hands the worker its module, a fresh surface and the heartbeat", () => {
  const { supervisor, workers, surfaces, sink } = harness();
  supervisor.start(once, sink);
  assert.equal(workers.length, 1);
  const [{ message, transfer }] = workers[0]!.posted;
  assert.equal(message!.type, "run");
  const run = message as Extract<ToWorker, { type: "run" }>;
  assert.equal(run.mode, "once");
  assert.equal(run.module, once.module);
  assert.equal(run.canvas, surfaces[0]);
  assert.deepEqual(transfer, [surfaces[0]]);
  assert.ok(run.heartbeat instanceof SharedArrayBuffer);
});

test("a worker stuck inside a call past the frame deadline is terminated and restarted from init", () => {
  const { supervisor, workers, surfaces, events, sink, advance, last } = harness();
  supervisor.start(interactive, sink);
  last().emit({ type: "ready", subscriptions: ["Tick"] });
  last().heartbeat.enter();
  advance(LIMITS.frameMs);
  assert.equal(workers[0]!.terminated, false);
  advance(LIMITS.pollMs);
  assert.equal(workers[0]!.terminated, true);
  assert.deepEqual(events, ["ready", `failed:${STUCK_MESSAGE}`]);
  assert.equal(workers.length, 2);
  assert.equal(surfaces.length, 2);
  assert.equal(workers[1]!.posted[0]!.message.type, "run");
  assert.notEqual(workers[1]!.heartbeat.buffer, workers[0]!.heartbeat.buffer);
  workers[1]!.emit({ type: "ready", subscriptions: ["Tick"] });
  assert.deepEqual(events.slice(2), ["ready"]);
});

test("a worker that keeps making progress is never terminated", () => {
  const { supervisor, workers, sink, advance, last } = harness();
  supervisor.start(interactive, sink);
  last().emit({ type: "ready", subscriptions: ["Tick"] });
  const heartbeat = last().heartbeat;
  for (let frame = 0; frame < 100; frame++) {
    heartbeat.enter();
    advance(LIMITS.frameMs - 2 * LIMITS.pollMs);
    heartbeat.leave();
    advance(LIMITS.pollMs);
  }
  assert.equal(workers[0]!.terminated, false);
  assert.equal(workers.length, 1);
});

test("a worker bumping the heartbeat while inside goat counts as progress", () => {
  const { supervisor, workers, sink, advance, last } = harness();
  supervisor.start(interactive, sink);
  const heartbeat = last().heartbeat;
  heartbeat.enter();
  for (let i = 0; i < 20; i++) {
    advance(LIMITS.pollMs);
    heartbeat.leave();
    heartbeat.enter();
  }
  assert.equal(workers[0]!.terminated, false);
});

test("an idle worker is never terminated, however long it waits", () => {
  const { supervisor, workers, sink, advance, last } = harness();
  supervisor.start(interactive, sink);
  last().emit({ type: "ready", subscriptions: [] });
  advance(60 * LIMITS.frameMs);
  assert.equal(workers[0]!.terminated, false);
});

test("a run-once program gets the whole-program deadline and is not restarted", () => {
  const { supervisor, workers, events, sink, advance, last } = harness();
  supervisor.start(once, sink);
  last().heartbeat.enter();
  advance(LIMITS.onceMs);
  assert.equal(workers[0]!.terminated, false);
  advance(LIMITS.pollMs);
  assert.equal(workers[0]!.terminated, true);
  assert.deepEqual(events, [`failed:${RUN_ONCE_STOPPED_MESSAGE}`]);
  assert.equal(workers.length, 1);
});

test("an interactive program stuck before setup finishes stays stopped", () => {
  const { supervisor, workers, timers, events, sink, advance, last } = harness();
  supervisor.start(interactive, sink);
  last().heartbeat.enter();
  advance(LIMITS.frameMs + LIMITS.pollMs);
  assert.deepEqual(events, [`failed:${STUCK_MESSAGE}`]);
  assert.equal(workers.length, 1);
  assert.equal(timers.every((t) => !t.active), true);
});

test("a program that gets stuck again after every restart stops restarting", () => {
  const { supervisor, workers, events, sink, advance, last } = harness();
  supervisor.start(interactive, sink);
  for (let attempt = 0; attempt <= MAX_RESTARTS; attempt++) {
    last().emit({ type: "ready", subscriptions: [] });
    last().heartbeat.enter();
    advance(LIMITS.frameMs + LIMITS.pollMs);
  }
  assert.equal(workers.length, MAX_RESTARTS + 1);
  assert.equal(workers.every((w) => w.terminated), true);
  assert.equal(events.filter((e) => e === `failed:${STUCK_MESSAGE}`).length, MAX_RESTARTS + 1);
  supervisor.start(interactive, sink);
  assert.equal(workers.length, MAX_RESTARTS + 2);
  assert.equal(last().terminated, false);
});

test("stop terminates the worker, cancels the poll and ignores its late messages", () => {
  const { supervisor, workers, timers, events, sink, advance, last } = harness();
  supervisor.start(interactive, sink);
  const worker = last();
  worker.heartbeat.enter();
  supervisor.stop();
  assert.equal(worker.terminated, true);
  assert.equal(timers.every((t) => !t.active), true);
  worker.emit({ type: "ready", subscriptions: ["Tick"] });
  worker.onerror?.({ message: "late" });
  advance(10 * LIMITS.frameMs);
  assert.deepEqual(events, []);
  assert.equal(workers.length, 1);
});

test("starting a program stops the previous one", () => {
  const { supervisor, workers, sink } = harness();
  supervisor.start(interactive, sink);
  supervisor.start(once, sink);
  assert.equal(workers[0]!.terminated, true);
  assert.equal(workers[1]!.terminated, false);
});

test("worker messages reach the sink and a worker error is reported as a failure", () => {
  const { supervisor, events, sink, last } = harness();
  supervisor.start(once, sink);
  last().emit({ type: "output", lines: ["a", "b"] });
  last().emit({ type: "finished" });
  last().emit({ type: "failed", message: "first of an empty list" });
  last().onerror?.({ message: "boom" });
  last().onerror?.({});
  assert.deepEqual(events, [
    "output:a|b",
    "finished",
    "failed:first of an empty list",
    "failed:your program stopped: boom",
    "failed:your program stopped: the worker failed",
  ]);
});

test("input reaches only a ready worker and only events its program subscribed to", () => {
  const { supervisor, sink, last } = harness();
  supervisor.start(interactive, sink);
  assert.equal(supervisor.wants("KeyDown"), false);
  supervisor.input({ kind: "KeyDown", key: "a" });
  assert.deepEqual(last().inputs, []);
  last().emit({ type: "ready", subscriptions: ["KeyDown", "PointerDown"] });
  assert.equal(supervisor.wants("KeyDown"), true);
  assert.equal(supervisor.wants("KeyUp"), false);
  supervisor.input({ kind: "KeyDown", key: "a" });
  supervisor.input({ kind: "KeyUp", key: "a" });
  supervisor.input({ kind: "PointerDown", x: 1, y: 2 });
  assert.deepEqual(last().inputs, [
    { kind: "KeyDown", key: "a" },
    { kind: "PointerDown", x: 1, y: 2 },
  ]);
  supervisor.stop();
  assert.equal(supervisor.wants("KeyDown"), false);
  supervisor.input({ kind: "KeyDown", key: "b" });
  assert.equal(last().inputs.length, 2);
});

test("the poll runs on the configured interval", () => {
  const { supervisor, timers, sink } = harness({ ...LIMITS, pollMs: 50 });
  supervisor.start(interactive, sink);
  assert.deepEqual(timers.map((t) => t.ms), [50]);
});

const reloaded = new Uint8Array([1]);

test("a reload goes to a ready interactive program and its outcome reaches the sink", () => {
  const { supervisor, events, sink, last } = harness();
  const outcomes: string[] = [];
  supervisor.start(interactive, { ...sink, onReloaded: (o) => outcomes.push(o), onReloadFailed: (m) => outcomes.push(m) });
  assert.equal(supervisor.reload(reloaded), false);
  last().emit({ type: "ready", subscriptions: [] });
  assert.equal(supervisor.reload(reloaded), true);
  assert.deepEqual(last().posted.at(-1)!.message, { type: "reload", module: reloaded });
  last().emit({ type: "reloaded", outcome: "reset", subscriptions: ["KeyDown"] });
  last().emit({ type: "reload_failed", message: "no" });
  assert.deepEqual(outcomes, ["reset", "no"]);
  assert.equal(supervisor.wants("KeyDown"), true);
  assert.deepEqual(events, ["ready"]);
});

test("a run-once program takes no reload", () => {
  const { supervisor, sink, last } = harness();
  supervisor.start(once, sink);
  last().emit({ type: "ready", subscriptions: [] });
  assert.equal(supervisor.reload(reloaded), false);
});

test("a restart after a stuck call runs the last module that reloaded, not one that failed", () => {
  const { supervisor, workers, sink, advance, last } = harness();
  const failed = new Uint8Array([2]);
  supervisor.start(interactive, sink);
  last().emit({ type: "ready", subscriptions: [] });
  supervisor.reload(reloaded);
  last().emit({ type: "reloaded", outcome: "kept", subscriptions: [] });
  supervisor.reload(failed);
  last().emit({ type: "reload_failed", message: "no" });
  last().heartbeat.enter();
  advance(LIMITS.frameMs + LIMITS.pollMs);
  assert.equal(workers.length, 2);
  assert.equal((workers[1]!.posted[0]!.message as Extract<ToWorker, { type: "run" }>).module, reloaded);
});
