import assert from "node:assert/strict";
import { existsSync, mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, resolve } from "node:path";
import test from "node:test";
import { assemble } from "./bundle.ts";
import { compile } from "./compile.ts";
import { type EngineMessage, createEngine, parseDiagnostics } from "./embed.ts";

const compilerUrl = new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", import.meta.url);
const compiler = await WebAssembly.compile(readFileSync(compilerUrl));

type Listener = () => void;

// A canvas with no DOM: drawing calls are accepted and ignored, and frames run
// as timers so animations finish.
function fakeCanvas() {
  const context = new Proxy({} as Record<string, unknown>, {
    get: (target, key: string) => target[key] ?? (() => {}),
    set: (target, key: string, value) => ((target[key] = value), true),
  });
  const listeners = new Map<string, Listener[]>();
  return {
    width: 300,
    height: 300,
    getContext: () => context,
    focus() {},
    getBoundingClientRect: () => ({ left: 0, top: 0, width: 300, height: 300 }),
    addEventListener: (type: string, listener: Listener) =>
      listeners.set(type, [...(listeners.get(type) ?? []), listener]),
    removeEventListener: (type: string, listener: Listener) =>
      listeners.set(type, (listeners.get(type) ?? []).filter((l) => l !== listener)),
    listenerCount: () => [...listeners.values()].reduce((n, l) => n + l.length, 0),
  };
}

function engine() {
  const canvas = fakeCanvas();
  const messages: EngineMessage[] = [];
  const built = createEngine({
    canvas: canvas as unknown as HTMLCanvasElement,
    compiler,
    post: (message) => messages.push(message),
  });
  return { canvas, messages, ...built };
}

globalThis.requestAnimationFrame = (frame) => setTimeout(() => frame(0), 0) as unknown as number;
globalThis.cancelAnimationFrame = (handle) => clearTimeout(handle);

const ARROWS = `init = {t: 0}
update = program(model, event) do
  match event do Tick(dt) then {t: model.t + dt} else model done
done
draw = program(model) do [Line({x1: 0, y1: 0, x2: model.t, y2: 5, color: "red"})] done
`;

test("diagnostics carry the checker's line, column and underline length", async () => {
  const result = await compile(compiler, 'forward(1);\nforward("a")');
  assert.ok(!result.ok);
  const [first] = parseDiagnostics(result.diagnostics);
  assert.equal(first!.line, 2);
  assert.equal(first!.column, 1);
  assert.ok(first!.length >= 1);
  assert.doesNotMatch(first!.message, /\^|\n/);
});

test("rendered errors without a location keep their text at line 0", () => {
  assert.deepEqual(parseDiagnostics("source exceeds size limit"), [
    { line: 0, column: 0, length: 0, message: "source exceeds size limit" },
  ]);
});

test("several errors parse into one diagnostic each", () => {
  const rendered = "1:1: first\n  a\n  ^\n\n2:3: second\n  bb\n    ^^";
  assert.deepEqual(parseDiagnostics(rendered), [
    { line: 1, column: 1, length: 1, message: "first" },
    { line: 2, column: 3, length: 2, message: "second" },
  ]);
});

test("a compile error posts diagnostics then fails", async () => {
  const { messages, run } = engine();
  await run("foo(2)");
  assert.equal(messages[0]!.type, "diagnostics");
  assert.deepEqual(messages[1], { type: "state", state: "failed", message: "your program has problems" });
});

test("a run-once program posts its output and finishes", async () => {
  const { messages, run } = engine();
  await run('print("hello");\nforward(10)');
  assert.deepEqual(messages, [
    { type: "state", state: "running" },
    { type: "output", lines: ["hello"] },
    { type: "state", state: "finished" },
  ]);
});

test("an interactive program keeps running until stopped", async () => {
  const { canvas, messages, run, stop } = engine();
  await run(ARROWS);
  assert.deepEqual(messages, [{ type: "state", state: "running" }]);
  stop();
  assert.equal(canvas.listenerCount(), 0);
});

test("a stopped run posts nothing more", async () => {
  const { messages, run, stop } = engine();
  const pending = run('print("hi")');
  stop();
  await pending;
  assert.deepEqual(messages, []);
});

test("the embed bundle is the canvas page, relative and self-contained", async () => {
  const outDir = mkdtempSync(`${tmpdir()}/goat-embed-`);
  try {
    assemble(outDir, ["embed.html"]);
    assert.ok(!existsSync(`${outDir}/index.html`), "the editor page is not shipped");
    const html = readFileSync(`${outDir}/embed.html`, "utf8");
    assert.doesNotMatch(html, /<textarea|<button/);
    assert.doesNotMatch(html, /\b(?:src|href)\s*=\s*["'](?:[a-z]+:)?\/\//i);
    const entry = html.match(/<script[^>]*src="([^"]+)"/)![1]!;
    assert.match(entry, /^\.\/[^.]/);

    const specifiers = (source: string) =>
      [...source.matchAll(/(?:from\s+|import\s*\(\s*)["']([^"']+)["']/g)].map((m) => m[1]!);
    const seen = new Set<string>();
    const queue = [resolve(outDir, entry)];
    while (queue.length > 0) {
      const file = queue.pop()!;
      if (seen.has(file)) continue;
      seen.add(file);
      assert.ok(existsSync(file), `${file} is served`);
      for (const spec of specifiers(readFileSync(file, "utf8"))) {
        assert.match(spec, /^\.\.?\//, `${file} imports ${spec}`);
        queue.push(resolve(dirname(file), spec));
      }
    }

    const main = readFileSync(resolve(outDir, entry), "utf8");
    const wasmPath = main.match(/new URL\("([^"]+goat_web\.wasm)", import\.meta\.url\)/)![1]!;
    assert.match(wasmPath, /^\.\.?\//);
    const bundled = await WebAssembly.compile(readFileSync(resolve(dirname(resolve(outDir, entry)), wasmPath)));
    const result = await compile(bundled, "forward(10)");
    assert.ok(result.ok);
  } finally {
    rmSync(outDir, { recursive: true, force: true });
  }
});
