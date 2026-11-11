// Keystroke-to-decoration latency of the goat highlighter, on real threads:
//
//   cargo build -p goat_web --target wasm32-unknown-unknown --release
//   node web/highlighter.bench.ts
//
// Each iteration types one character into a 5 KB file and times the whole path
// a keystroke takes once CodeMirror has the new document: request, structured
// clone to the worker thread, goat `update` and `draw`, the span message back,
// validation, byte-to-UTF-16 conversion, and building the decoration set.
// Browser layout and paint come after and are not measured here.

import { readFileSync, readdirSync } from "node:fs";
import { Worker } from "node:worker_threads";
import { type Token, createTokenizer } from "./compile.ts";
import { tokenDecorations } from "./editor.ts";
import { GoatHighlighter } from "./highlighter.ts";
import type { FromWorker, ToWorker } from "./protocol.ts";
import { Supervisor, type WorkerLike } from "./supervisor.ts";

const compiler = await WebAssembly.compile(
  readFileSync(new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", import.meta.url)),
);
const source = readFileSync(new URL("../editor/highlight.goat", import.meta.url), "utf8");

class ThreadWorker implements WorkerLike {
  onmessage: WorkerLike["onmessage"] = null;
  onerror: WorkerLike["onerror"] = null;
  #thread = new Worker(new URL("./worker-thread.fixture.ts", import.meta.url));
  constructor() {
    this.#thread.on("message", (data: FromWorker) => this.onmessage?.({ data }));
  }
  postMessage(message: ToWorker) {
    this.#thread.postMessage(message);
  }
  terminate() {
    void this.#thread.terminate();
  }
}

const supervisor = new Supervisor(
  {
    spawn: () => new ThreadWorker(),
    surface: () => ({ width: 1, height: 1 }) as OffscreenCanvas,
    now: () => performance.now(),
    every: (ms, tick) => {
      const handle = setInterval(tick, ms);
      return () => clearInterval(handle);
    },
  },
  { crossOriginIsolated: true, SharedArrayBuffer, Worker: class {}, OffscreenCanvas: class {} },
);

const examples = new URL("../examples/canvas/", import.meta.url);
const pieces = [
  ...readdirSync(new URL("../examples/", import.meta.url)).filter((name) => name.endsWith(".goat")).map(
    (name) => readFileSync(new URL(`../examples/${name}`, import.meta.url), "utf8"),
  ),
  ...readdirSync(examples).filter((name) => name.endsWith(".goat")).map((name) => readFileSync(new URL(name, examples), "utf8")),
];
let file = "";
for (let i = 0; file.length < 5120; i++) file += pieces[i % pieces.length]!;
file = file.slice(0, 5120);

const percentile = (sorted: number[], p: number) => sorted[Math.min(sorted.length - 1, Math.floor(p * sorted.length))]!;
const summary = (label: string, samples: number[]) => {
  const sorted = [...samples].sort((a, b) => a - b);
  console.log(
    `${label}: n=${sorted.length} p50=${percentile(sorted, 0.5).toFixed(2)}ms p95=${percentile(sorted, 0.95).toFixed(2)}ms max=${sorted.at(-1)!.toFixed(2)}ms`,
  );
};

const goat = new GoatHighlighter({ compiler, source, runner: supervisor, host: () => "canvas" });
let arrived: ((tokens: Token[]) => void) | undefined;
goat.onTokens((tokens) => arrived?.(tokens));
await goat.start();
while (!goat.active) await new Promise((wake) => setTimeout(wake, 5));

const SAMPLES = 300;
const WARMUP = 30;
const viaGoat: number[] = [];
for (let i = 0; i < SAMPLES + WARMUP; i++) {
  const text = `${file}${i % 2 === 0 ? "x" : ""}`;
  const done = new Promise<Token[]>((resolve) => (arrived = resolve));
  const started = performance.now();
  goat.request(text);
  tokenDecorations(await done);
  if (i >= WARMUP) viaGoat.push(performance.now() - started);
}
goat.stop();

const tokenize = createTokenizer(compiler, () => "canvas");
const viaBuiltIn: number[] = [];
for (let i = 0; i < SAMPLES + WARMUP; i++) {
  const started = performance.now();
  tokenDecorations(tokenize(`${file}${i % 2 === 0 ? "x" : ""}`));
  if (i >= WARMUP) viaBuiltIn.push(performance.now() - started);
}

console.log(`file: ${file.length} bytes, ${file.split("\n").length} lines`);
summary("goat highlighter (worker round trip + scan + decorations)", viaGoat);
summary("built-in gw_tokenize (+ decorations)", viaBuiltIn);
