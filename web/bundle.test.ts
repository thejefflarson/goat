import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import type { AddressInfo } from "node:net";
import { tmpdir } from "node:os";
import test from "node:test";
import { assemble } from "./bundle.ts";
import { compile, loadCompiler } from "./compile.ts";
import { ISOLATION_HEADERS, createSiteServer } from "./serve.ts";

const outDir = mkdtempSync(`${tmpdir()}/goat-site-`);
assemble(outDir);

const server = createSiteServer(outDir);
await new Promise<void>((done) => server.listen(0, "127.0.0.1", done));
const origin = `http://127.0.0.1:${(server.address() as AddressInfo).port}`;
const page = new URL("/", origin);

test.after(() => {
  server.close();
  rmSync(outDir, { recursive: true, force: true });
});

const html = readFileSync(`${outDir}/index.html`, "utf8");

function relativeSpecifiers(source: string): string[] {
  return [...source.matchAll(/(?:from\s+|import\s*\(\s*)["']([^"']+)["']/g)].map((m) => m[1]);
}

const compilerUrl = html.match(/COMPILER_URL = "([^"]+)"/)![1];

test("the page references only relative paths", () => {
  assert.equal(compilerUrl, "./goat_web.wasm");
  for (const spec of [...relativeSpecifiers(html), compilerUrl]) {
    assert.match(spec, /^\.\/[^.]/, spec);
  }
  assert.doesNotMatch(html, /\b(?:src|href)\s*=\s*["'](?:[a-z]+:)?\/\//i);
});

async function servedClosure(entries: URL[]): Promise<Set<string>> {
  const seen = new Set<string>();
  const queue = [...entries];
  while (queue.length > 0) {
    const url = queue.pop()!;
    if (seen.has(url.href)) continue;
    seen.add(url.href);
    assert.equal(url.origin, origin);
    const response = await fetch(url);
    assert.equal(response.status, 200, url.href);
    for (const spec of relativeSpecifiers(await response.text())) {
      assert.match(spec, /^\.\.?\//, `${url.pathname} imports ${spec}`);
      queue.push(new URL(spec, url));
    }
  }
  return seen;
}

test("every module the page imports is served, transitively", async () => {
  const seen = await servedClosure(relativeSpecifiers(html).map((spec) => new URL(spec, page)));
  assert.ok([...seen].some((href) => href.endsWith("/dist/runtime.js")));
});

test("the worker the supervisor spawns is served with all it imports", async () => {
  const workerUrl = new URL("dist/worker.js", page);
  const seen = await servedClosure([workerUrl]);
  assert.ok(seen.has(workerUrl.href));
  assert.ok([...seen].some((href) => href.endsWith("/dist/worker-core.js")));
  assert.ok(readFileSync(`${outDir}/dist/browser.js`, "utf8").includes('"./worker.js"'));
});

test("every response carries the headers that cross-origin isolate the page", async () => {
  for (const path of ["/", "/dist/worker.js", "/goat_web.wasm", "/missing"]) {
    const response = await fetch(new URL(path, origin));
    for (const [name, value] of Object.entries(ISOLATION_HEADERS)) {
      assert.equal(response.headers.get(name), value, `${path} ${name}`);
    }
  }
});

test("nginx sends the same isolation headers", () => {
  const conf = readFileSync(new URL("nginx.conf", import.meta.url), "utf8");
  for (const [name, value] of Object.entries(ISOLATION_HEADERS)) {
    assert.match(conf, new RegExp(`add_header ${name} ${value} always;`, "i"));
  }
});

test("the compiler loads from the page's relative URL and compiles", async () => {
  const compiler = await loadCompiler(new URL(compilerUrl, page));
  const result = await compile(compiler, "forward(10)");
  assert.ok(result.ok);
});
