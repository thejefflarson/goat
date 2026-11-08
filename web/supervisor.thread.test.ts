// The supervisor against real threads: node's worker_threads stand in for Web
// Workers, so this checks what fakes cannot, that a worker spinning inside wasm
// is killed from outside while the heartbeat crosses a real SharedArrayBuffer.
// The browser's own Worker, OffscreenCanvas and rendering are not covered here.

import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { Worker } from "node:worker_threads";
import { compile } from "./compile.ts";
import { STUCK_MESSAGE } from "./loop.ts";
import type { FromWorker, ToWorker } from "./protocol.ts";
import {
  type Job,
  RUN_ONCE_STOPPED_MESSAGE,
  type RunSink,
  Supervisor,
  type WorkerLike,
} from "./supervisor.ts";

const compiler = await WebAssembly.compile(
  readFileSync(new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", import.meta.url)),
);

async function job(mode: Job["mode"], source: string): Promise<Job> {
  const result = await compile(compiler, source);
  if (!result.ok) assert.fail(result.diagnostics);
  return { mode, module: result.module };
}

class ThreadWorker implements WorkerLike {
  onmessage: WorkerLike["onmessage"] = null;
  onerror: WorkerLike["onerror"] = null;
  exited: Promise<void>;
  #thread = new Worker(new URL("./worker-thread.fixture.ts", import.meta.url));

  constructor() {
    this.#thread.on("message", (data: FromWorker) => this.onmessage?.({ data }));
    this.#thread.on("error", (e: Error) => this.onerror?.({ message: e.message }));
    this.exited = new Promise((resolve) => this.#thread.once("exit", () => resolve()));
  }
  postMessage(message: ToWorker) {
    this.#thread.postMessage(message);
  }
  terminate() {
    void this.#thread.terminate();
  }
}

const capable = { crossOriginIsolated: true, SharedArrayBuffer, Worker: class {}, OffscreenCanvas: class {} };

function harness(limits: { frameMs: number; onceMs: number }) {
  const threads: ThreadWorker[] = [];
  const supervisor = new Supervisor(
    {
      spawn: () => {
        const thread = new ThreadWorker();
        threads.push(thread);
        return thread;
      },
      surface: () => ({ width: 300, height: 300 }) as OffscreenCanvas,
      now: () => performance.now(),
      every: (ms, tick) => {
        const handle = setInterval(tick, ms);
        return () => clearInterval(handle);
      },
    },
    capable,
    { ...limits, pollMs: 20 },
  );
  const events: string[] = [];
  const waiters: Array<() => void> = [];
  const note = (event: string) => {
    events.push(event);
    waiters.splice(0).forEach((wake) => wake());
  };
  const sink: RunSink = {
    onReady: () => note("ready"),
    onOutput: (lines) => note(`output:${lines.join("|")}`),
    onFinished: () => note("finished"),
    onFailed: (message) => note(`failed:${message}`),
  };
  const until = async (predicate: () => boolean) => {
    const deadline = Date.now() + 20_000;
    while (!predicate()) {
      assert.ok(Date.now() < deadline, `timed out: ${events.join(", ")}`);
      await new Promise<void>((wake) => {
        waiters.push(wake);
        setTimeout(wake, 50);
      });
    }
  };
  return { supervisor, threads, events, sink, until };
}

const SPIN = "spin = program(n) do if n < 0 then n else spin(n + 1) done done";
const TICKS = `init = {t: 0}
update = program(model, event) do
  match event do Tick(dt) then {t: model.t + 1} else model done
done
draw = program(model) do [Line({x1: 0, y1: 0, x2: model.t, y2: 5, color: "red"})] done
`;
const SPINS_ON_TICK = `${SPIN}
init = {n: 0}
update = program(model, event) do
  match event do Tick(dt) then {n: spin(0)} else model done
done
draw = program(model) do [] done
`;

test("a thread spinning inside update is terminated, reported stuck, and restarted from init", async () => {
  const { supervisor, threads, events, sink, until } = harness({ frameMs: 300, onceMs: 5000 });
  supervisor.start(await job("interactive", SPINS_ON_TICK), sink);
  await until(() => events.includes(`failed:${STUCK_MESSAGE}`));
  await threads[0]!.exited;
  await until(() => events.filter((e) => e === "ready").length >= 2);
  assert.equal(threads.length >= 2, true);
  supervisor.stop();
  await Promise.all(threads.map((t) => t.exited));
});

test("a thread spinning in a run-once program is terminated at the whole-program deadline", async () => {
  const { supervisor, threads, events, sink, until } = harness({ frameMs: 300, onceMs: 300 });
  supervisor.start(await job("once", `${SPIN}\nspin(0)`), sink);
  await until(() => events.length > 0);
  assert.deepEqual(events, [`failed:${RUN_ONCE_STOPPED_MESSAGE}`]);
  await threads[0]!.exited;
  assert.equal(threads.length, 1);
});

test("a well-behaved program runs frames on a thread for several deadlines and is left alone", async () => {
  const { supervisor, threads, events, sink, until } = harness({ frameMs: 200, onceMs: 5000 });
  supervisor.start(await job("interactive", TICKS), sink);
  await until(() => events.includes("ready"));
  await new Promise((wake) => setTimeout(wake, 800));
  assert.deepEqual(events, ["ready"]);
  assert.equal(threads.length, 1);
  supervisor.stop();
  await threads[0]!.exited;
});
