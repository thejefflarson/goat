// The goat highlighter end to end in one process: the real worker core stands in
// for the Web Worker behind the real supervisor, so a span travels the whole way
// (event, goat `update`, `draw`, `scene.span`, message, validation, decoration).
// Threads and the wall-clock deadline are in highlighter.thread.test.ts.

import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import test from "node:test";
import { type Host, type Token, createTokenizer, hostTags } from "./compile.ts";
import { tokenDecorations } from "./editor.ts";
import { GoatHighlighter, type HighlightRunner, acceptSpans } from "./highlighter.ts";
import type { FromWorker, ToWorker } from "./protocol.ts";
import { type RunSink, Supervisor, type WorkerLike } from "./supervisor.ts";
import { createWorkerCore } from "./worker-core.ts";

const compiler = await WebAssembly.compile(
  readFileSync(new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", import.meta.url)),
);
const source = readFileSync(new URL("../editor/highlight.goat", import.meta.url), "utf8");

const capable = { crossOriginIsolated: true, SharedArrayBuffer, Worker: class {}, OffscreenCanvas: class {} };

function inProcessWorker(): WorkerLike {
  let closed = false;
  const worker: WorkerLike = {
    onmessage: null,
    onerror: null,
    postMessage: (message: ToWorker) => void core.handle(message),
    terminate: () => {
      closed = true;
    },
  };
  const core = createWorkerCore({
    post: (message: FromWorker) => {
      if (!closed) worker.onmessage?.({ data: message });
    },
    raf: () => 0,
    cancelRaf: () => {},
    now: () => performance.now(),
  });
  return worker;
}

function inProcessSupervisor(): Supervisor {
  return new Supervisor(
    {
      spawn: inProcessWorker,
      surface: () => ({ width: 1, height: 1 }) as OffscreenCanvas,
      now: () => performance.now(),
      every: () => () => {},
    },
    capable,
  );
}

// The decorations CodeMirror would draw for `tokens`, as (from, to, class).
function decorated(tokens: Token[]): Array<[number, number, string]> {
  const found: Array<[number, number, string]> = [];
  tokenDecorations(tokens).between(0, Number.MAX_SAFE_INTEGER, (from, to, value) => {
    found.push([from, to, value.spec.class]);
  });
  return found;
}

// A started highlighter, and `colors(text)`: the tokens it ends up with.
async function highlighter(host: () => Host = () => "turtle", runner: HighlightRunner = inProcessSupervisor()) {
  const goat = new GoatHighlighter({ compiler, source, runner, host });
  let wake: ((tokens: Token[]) => void) | undefined;
  goat.onTokens((tokens) => wake?.(tokens));
  await goat.start();
  const ready = async () => {
    for (let i = 0; i < 200 && !goat.active; i++) await new Promise((r) => setTimeout(r, 5));
    assert.ok(goat.active, "the goat highlighter started");
  };
  const colors = async (text: string): Promise<Token[]> => {
    const arrival = new Promise<Token[]>((resolve) => (wake = resolve));
    const now = goat.request(text);
    return now ?? (await arrival);
  };
  return { goat, ready, colors, stop: () => goat.stop() };
}

function goatFiles(directory: string): Array<[string, string]> {
  const dir = new URL(`../examples/${directory}`, import.meta.url);
  return readdirSync(dir)
    .filter((name) => name.endsWith(".goat"))
    .map((name) => [name, readFileSync(new URL(name, `${dir.href}/`), "utf8")]);
}

test("the goat highlighter's decorations equal the built-in tokenizer's on every turtle example", async () => {
  const goat = await highlighter(() => "turtle");
  await goat.ready();
  const tokenize = createTokenizer(compiler, () => "turtle");
  const files = goatFiles("");
  assert.ok(files.length > 20);
  for (const [name, text] of files) {
    assert.deepEqual(decorated(await goat.colors(text)), decorated(tokenize(text)), name);
  }
  goat.stop();
});

test("the goat highlighter's decorations equal the built-in tokenizer's on every canvas example, host tags included", async () => {
  const goat = await highlighter(() => "canvas");
  await goat.ready();
  const tokenize = createTokenizer(compiler, () => "canvas");
  const files = goatFiles("canvas");
  assert.ok(files.length >= 2);
  for (const [name, text] of files) {
    const tokens = await goat.colors(text);
    assert.deepEqual(decorated(tokens), decorated(tokenize(text)), name);
    assert.ok(tokens.some((token) => token.kind === "tag"), `${name} has host tags`);
  }
  goat.stop();
});

test("the page's own examples color the same under both highlighters", async () => {
  const page = readFileSync(new URL("./index.html", import.meta.url), "utf8");
  const examples = [...page.matchAll(/^ {4}(\w+): `([^`]*)`/gm)].map((match) => [match[1]!, match[2]!] as const);
  assert.equal(examples.length, 6);
  const hosts: Record<string, Host> = { arrow_draw: "turtle", spiral: "turtle", bounce: "canvas", catch: "canvas", sky: "canvas", ordering: "turtle" };
  let host: Host = "turtle";
  const goat = await highlighter(() => host);
  await goat.ready();
  const tokenize = createTokenizer(compiler, () => host);
  for (const [name, text] of examples) {
    host = hosts[name]!;
    assert.deepEqual(decorated(await goat.colors(text)), decorated(tokenize(text)), name);
  }
  goat.stop();
});

test("switching hosts re-sends the tags, so the same word colors by the new host's vocabulary", async () => {
  let host: Host = "turtle";
  const goat = await highlighter(() => host);
  await goat.ready();
  const text = "Dot Segment Frame KeyDown Empty";
  const tokenize = createTokenizer(compiler, () => host);
  const turtle = await goat.colors(text);
  assert.deepEqual(decorated(turtle), decorated(tokenize(text)));
  host = "canvas";
  const canvas = await goat.colors(text);
  assert.deepEqual(decorated(canvas), decorated(tokenize(text)));
  assert.notDeepEqual(decorated(turtle), decorated(canvas));
  assert.ok(hostTags(compiler, "canvas").split(" ").includes("Segment"));
  goat.stop();
});

test("offsets are UTF-16 positions in text with multi-byte and astral characters", async () => {
  const goat = await highlighter();
  await goat.ready();
  const tokenize = createTokenizer(compiler, () => "turtle");
  const text = "# café \u{1f410}\nx = \"é\u{1f410}\" + 12 # ☃\nif true then 1.5 done";
  const tokens = await goat.colors(text);
  assert.deepEqual(decorated(tokens), decorated(tokenize(text)));
  assert.equal(text.slice(tokens[0]!.from, tokens[0]!.to), "# café \u{1f410}");
  goat.stop();
});

test("edits answer in order and a stale answer never replaces a newer one", async () => {
  const goat = await highlighter();
  await goat.ready();
  const seen: Token[][] = [];
  goat.goat.onTokens((tokens) => seen.push(tokens));
  goat.goat.request("1");
  goat.goat.request("if x then 1 done");
  goat.goat.request("true");
  for (let i = 0; i < 200 && seen.length === 0; i++) await new Promise((r) => setTimeout(r, 5));
  await new Promise((r) => setTimeout(r, 50));
  assert.deepEqual(seen.at(-1), [{ kind: "literal", from: 0, to: 4 }]);
  goat.stop();
});

test("until the worker is ready, and after it stops, the built-in tokenizer answers at once", async () => {
  const goat = await highlighter();
  const tokenize = createTokenizer(compiler, () => "turtle");
  assert.equal(goat.goat.active, false);
  assert.deepEqual(goat.goat.request("if x then 1 done"), tokenize("if x then 1 done"));
  await goat.ready();
  assert.equal(goat.goat.request("1"), null, "ready: the answer comes from the worker");
  goat.stop();
  assert.deepEqual(goat.goat.request("true"), tokenize("true"));
});

class RecordingRunner implements HighlightRunner {
  sink: RunSink | undefined;
  inputs: Array<{ kind: string; ticket?: number }> = [];
  stops = 0;
  start(_job: unknown, sink: RunSink) {
    this.sink = sink;
  }
  stop() {
    this.stops++;
  }
  input(event: { kind: string }, ticket?: number) {
    this.inputs.push({ kind: event.kind, ticket });
  }
}

test("a highlighter that fails falls back to the built-in tokenizer and is stopped", async () => {
  const runner = new RecordingRunner();
  const goat = await highlighter(() => "turtle", runner);
  const tokenize = createTokenizer(compiler, () => "turtle");
  const heard: Token[][] = [];
  goat.goat.onTokens((tokens) => heard.push(tokens));
  runner.sink!.onReady!();
  assert.equal(goat.goat.request("if x then 1 done"), null);
  assert.deepEqual(
    runner.inputs.map((input) => input.kind),
    ["HostTags", "Edited"],
  );
  runner.sink!.onFailed("your program stopped: boom");
  assert.equal(runner.stops, 1);
  assert.deepEqual(heard, [tokenize("if x then 1 done")], "the current text is recolored at once");
  assert.deepEqual(goat.goat.request("true"), tokenize("true"));
  assert.equal(runner.inputs.length, 2, "nothing more is sent to a failed worker");
});

test("a restarted worker is told the tags and the current text again", async () => {
  const runner = new RecordingRunner();
  const goat = await highlighter(() => "turtle", runner);
  runner.sink!.onReady!();
  goat.goat.request("x");
  runner.sink!.onReady!();
  assert.deepEqual(
    runner.inputs.map((input) => input.kind),
    ["HostTags", "Edited", "HostTags", "Edited"],
  );
  const tickets = runner.inputs.filter((input) => input.kind === "Edited").map((input) => input.ticket);
  assert.equal(tickets[0], tickets[1]);
});

test("a highlighter that does not compile leaves the built-in tokenizer in charge", async () => {
  const runner = new RecordingRunner();
  const goat = new GoatHighlighter({ compiler, source: "not a program (", runner });
  await goat.start();
  assert.equal(runner.sink, undefined);
  assert.deepEqual(goat.request("1 + 2"), createTokenizer(compiler)("1 + 2"));
});

test("a worker that cannot be told the text counts as failed", async () => {
  const runner = new RecordingRunner();
  runner.input = () => {
    throw new Error("worker gone");
  };
  const goat = await highlighter(() => "turtle", runner);
  runner.sink!.onReady!();
  assert.deepEqual(goat.goat.request("1"), createTokenizer(compiler)("1"));
  assert.equal(goat.goat.active, false);
});

test("a span's kind is allowlisted: an unknown kind is dropped, never used", () => {
  const text = "abcdefghij";
  const spans = [
    { from: 0, to: 1, kind: "keyword" },
    { from: 1, to: 2, kind: "keyword tok-evil" },
    { from: 2, to: 3, kind: '"><img src=x onerror=alert(1)>' },
    { from: 3, to: 4, kind: "__proto__" },
    { from: 4, to: 5, kind: "constructor" },
    { from: 5, to: 6, kind: "" },
    { from: 6, to: 7, kind: 7 },
    { from: 7, to: 8, kind: "tag" },
    { from: 8, to: 9, kind: "name" },
    { from: 9, to: 10, kind: "operator" },
  ];
  const kinds = acceptSpans(spans, text).map((token) => token.kind);
  assert.deepEqual(kinds, ["keyword", "tag", "operator"]);
  for (const kind of ["comment", "keyword", "literal", "number", "string", "tag", "operator"]) {
    assert.equal(acceptSpans([{ from: 0, to: 1, kind }], text).length, 1, kind);
  }
});

test("a malformed, out-of-range or out-of-order span is dropped", () => {
  const text = "abcdefghij";
  const span = (from: unknown, to: unknown, kind: unknown = "number") => ({ from, to, kind });
  assert.deepEqual(acceptSpans("nope", text), []);
  assert.deepEqual(acceptSpans(null, text), []);
  assert.deepEqual(
    acceptSpans(
      [
        null,
        7,
        "x",
        span(-1, 2),
        span(0, 11),
        span(1.5, 2),
        span("0", 1),
        span(Number.NaN, 2),
        span(3, 3),
        span(4, 3),
        span(2, 4),
        span(3, 5),
        span(4, 6),
        span(1, 2),
      ],
      text,
    ),
    [
      { kind: "number", from: 2, to: 4 },
      { kind: "number", from: 4, to: 6 },
    ],
  );
  assert.deepEqual(acceptSpans([{ from: 0, to: 1 }, { kind: "number" }, {}], text), []);
});

test("byte offsets become UTF-16 offsets, and a span cut inside a character never inverts", () => {
  const text = "é\u{1f410}x";
  assert.deepEqual(acceptSpans([{ from: 6, to: 7, kind: "number" }], text), [{ kind: "number", from: 3, to: 4 }]);
  assert.deepEqual(acceptSpans([{ from: 0, to: 2, kind: "string" }], text), [{ kind: "string", from: 0, to: 1 }]);
  assert.deepEqual(acceptSpans([{ from: 1, to: 2, kind: "string" }], text), [{ kind: "string", from: 0, to: 1 }]);
  assert.deepEqual(acceptSpans([{ from: 2, to: 3, kind: "string" }], text), []);
});
