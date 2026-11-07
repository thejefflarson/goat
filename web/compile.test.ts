import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { compile } from "./compile.ts";

const compiler = await WebAssembly.compile(
  readFileSync(new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", import.meta.url)),
);

test("a turtle program compiles to a wasm module", async () => {
  const source = readFileSync(new URL("../examples/spiral.goat", import.meta.url), "utf8");
  const result = await compile(compiler, source);
  assert.ok(result.ok);
  assert.deepEqual([...result.module.slice(0, 4)], [0, 0x61, 0x73, 0x6d]);
});

test("a type error returns the checker's rendered diagnostics", async () => {
  const result = await compile(compiler, "1 + true");
  assert.ok(!result.ok);
  assert.match(result.diagnostics, /\^/);
});

test("the compiler module is reusable across compiles", async () => {
  for (const source of ["forward(1)", "1 + true", "forward(2)"]) {
    assert.equal((await compile(compiler, source)).ok, !source.includes("true"));
  }
});
