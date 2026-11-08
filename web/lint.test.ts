import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { check } from "./compile.ts";
import { lintDiagnostics } from "./lint.ts";

const compiler = await WebAssembly.compile(
  readFileSync(new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", import.meta.url)),
);

async function lint(source: string) {
  return lintDiagnostics(await check(compiler, source), source.length);
}

test("a clean program has no lint diagnostics", async () => {
  assert.deepEqual(await lint('color("red"); forward(10)'), []);
});

test("an erroring program is underlined where the error is", async () => {
  const source = "forward(10);\nforward(true)";
  const found = await lint(source);
  assert.equal(found.length, 1);
  assert.equal(found[0].severity, "error");
  assert.ok(found[0].from >= source.indexOf("\n") && found[0].to > found[0].from);
  assert.ok(found[0].message.length > 0);
});

test("fixing the error clears the diagnostic", async () => {
  assert.equal((await lint("forward(true)")).length, 1);
  assert.deepEqual(await lint("forward(1)"), []);
});

test("a span with no width is widened to one character", () => {
  const widened = (from: number, length: number) => lintDiagnostics([{ from, to: from, message: "m" }], length);
  assert.deepEqual(widened(2, 5), [{ from: 2, to: 3, severity: "error", message: "m" }]);
  assert.deepEqual(widened(5, 5), [{ from: 4, to: 5, severity: "error", message: "m" }]);
  assert.deepEqual(widened(0, 0), [{ from: 0, to: 0, severity: "error", message: "m" }]);
});

test("spans past the end of the document are clamped to it", () => {
  assert.deepEqual(lintDiagnostics([{ from: 3, to: 99, message: "m" }], 6), [
    { from: 3, to: 6, severity: "error", message: "m" },
  ]);
});
