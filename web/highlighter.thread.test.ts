// The goat highlighter against real threads: a highlighter that spins inside
// goat is terminated from outside by the supervisor's deadline, and the editor
// carries on with the built-in tokenizer. The browser's own Worker is not covered.

import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { Worker } from "node:worker_threads";
import { type Token, createTokenizer } from "./compile.ts";
import { GoatHighlighter } from "./highlighter.ts";
import type { FromWorker, ToWorker } from "./protocol.ts";
import { Supervisor, type WorkerLike } from "./supervisor.ts";

const compiler = await WebAssembly.compile(
  readFileSync(new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", import.meta.url)),
);
const highlighterSource = readFileSync(new URL("../editor/highlight.goat", import.meta.url), "utf8");

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

function threaded(frameMs: number) {
  const threads: ThreadWorker[] = [];
  const supervisor = new Supervisor(
    {
      spawn: () => {
        const thread = new ThreadWorker();
        threads.push(thread);
        return thread;
      },
      surface: () => ({ width: 1, height: 1 }) as OffscreenCanvas,
      now: () => performance.now(),
      every: (ms, tick) => {
        const handle = setInterval(tick, ms);
        return () => clearInterval(handle);
      },
    },
    capable,
    { frameMs, pollMs: 20 },
  );
  return { supervisor, threads };
}

const until = async (predicate: () => boolean) => {
  const deadline = Date.now() + 20_000;
  while (!predicate()) {
    assert.ok(Date.now() < deadline, "timed out");
    await new Promise((wake) => setTimeout(wake, 10));
  }
};

const SPINS_ON_EDIT = `spin = program(n) do if n < 0 then n else spin(n + 1) done done
init = {n: 0}
update = program(model, event) do
  match event do Edited(edit) then {n: spin(0)} else model done
done
draw = program(model) do [] done
`;

test("a highlighter spinning on an edit is terminated and the built-in tokenizer colors the text", async () => {
  const { supervisor, threads } = threaded(300);
  const goat = new GoatHighlighter({ compiler, source: SPINS_ON_EDIT, runner: supervisor });
  const heard: Token[][] = [];
  goat.onTokens((tokens) => heard.push(tokens));
  await goat.start();
  await until(() => goat.active);
  const text = "if x then 1 done";
  assert.equal(goat.request(text), null, "the worker is asked");
  await until(() => heard.length > 0);
  assert.deepEqual(heard[0], createTokenizer(compiler)(text));
  assert.equal(goat.active, false, "no request goes to a worker that is not ready");
  assert.deepEqual(goat.request("true"), createTokenizer(compiler)("true"));
  await threads[0]!.exited;
  goat.stop();
  await Promise.all(threads.map((thread) => thread.exited));
});

test("the real highlighter answers on a thread with the spans the tokenizer finds", async () => {
  const { supervisor, threads } = threaded(5000);
  const goat = new GoatHighlighter({ compiler, source: highlighterSource, runner: supervisor, host: () => "canvas" });
  const heard: Token[][] = [];
  goat.onTokens((tokens) => heard.push(tokens));
  await goat.start();
  await until(() => goat.active);
  const text = readFileSync(new URL("../examples/canvas/bounce.goat", import.meta.url), "utf8");
  assert.equal(goat.request(text), null);
  await until(() => heard.length > 0);
  assert.deepEqual(heard[0], createTokenizer(compiler, () => "canvas")(text));
  assert.ok(heard[0]!.some((token) => token.kind === "tag"));
  goat.stop();
  await Promise.all(threads.map((thread) => thread.exited));
});
