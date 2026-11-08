import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { createServer } from "node:http";
import type { AddressInfo } from "node:net";
import { tmpdir } from "node:os";
import { extname } from "node:path";
import test from "node:test";
import { assemble } from "./bundle.ts";
import { compile, loadCompiler } from "./compile.ts";

const outDir = mkdtempSync(`${tmpdir()}/goat-site-`);
assemble(outDir);

const types: Record<string, string> = {
  ".html": "text/html",
  ".js": "text/javascript",
  ".wasm": "application/wasm",
};
const server = createServer((req, res) => {
  try {
    const path = new URL(req.url ?? "/", "http://x").pathname;
    const file = path.endsWith("/") ? `${path}index.html` : path;
    const body = readFileSync(`${outDir}${file}`);
    res.writeHead(200, { "content-type": types[extname(file)] ?? "application/octet-stream" });
    res.end(body);
  } catch {
    res.writeHead(404).end();
  }
});
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

test("every module the page imports is served, transitively", async () => {
  const seen = new Set<string>();
  const queue = relativeSpecifiers(html).map((spec) => new URL(spec, page));
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
  assert.ok([...seen].some((href) => href.endsWith("/dist/runtime.js")));
});

test("the compiler loads from the page's relative URL and compiles", async () => {
  const compiler = await loadCompiler(new URL(compilerUrl, page));
  const result = await compile(compiler, "forward(10)");
  assert.ok(result.ok);
});
