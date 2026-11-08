import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { check, compile, createTokenizer } from "./compile.ts";

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

// Where the first rendered diagnostic (`line:col: message`, then a caret line)
// puts its caret: a UTF-16 index and a width in bytes (the renderer draws one
// caret per byte of the span).
function renderedSpan(source: string, rendered: string): { from: number; width: number } {
  const [, line, col] = rendered.match(/^(\d+):(\d+):/)!.map(Number);
  const lineStart = source
    .split("\n")
    .slice(0, line - 1)
    .reduce((n, l) => n + l.length + 1, 0);
  const prefix = [...source.slice(lineStart)].slice(0, col - 1).join("");
  const caret = rendered.split("\n")[2];
  return { from: lineStart + prefix.length, width: caret.trim().length };
}

test("check is empty for a program that compiles", async () => {
  assert.deepEqual(await check(compiler, "forward(10)"), []);
});

test("check points where compile's diagnostic points", async () => {
  for (const source of ["1 + true", "x = 1\n1 + true", "# é😀\nprint(\"日本😀\") + true", "if then"]) {
    const rendered = await compile(compiler, source);
    assert.ok(!rendered.ok);
    const found = await check(compiler, source);
    const expected = renderedSpan(source, rendered.diagnostics);
    assert.equal(found.length, 1, source);
    assert.equal(found[0].from, expected.from, source);
    const covered = source.slice(found[0].from, found[0].to);
    assert.equal(Math.max(1, new TextEncoder().encode(covered).length), expected.width, source);
    assert.ok(found[0].message.length > 0);
  }
});

test("check reports every error compile does", async () => {
  const source = "1 + true\n2 + false";
  const found = await check(compiler, source);
  const rendered = await compile(compiler, source);
  assert.ok(!rendered.ok);
  assert.equal(found.length, rendered.diagnostics.split("\n\n").length);
});

test("tokenize colors a program by the lexer's categories", () => {
  const source = '# hi\ntag Dot\nx = "é" + 1.5\nif true then Dot else 0 done';
  const tokens = createTokenizer(compiler)(source);
  assert.deepEqual(
    tokens.map((t) => [t.kind, source.slice(t.from, t.to)]),
    [
      ["comment", "# hi"],
      ["keyword", "tag"],
      ["tag", "Dot"],
      ["string", '"é"'],
      ["operator", "+"],
      ["number", "1.5"],
      ["keyword", "if"],
      ["literal", "true"],
      ["keyword", "then"],
      ["tag", "Dot"],
      ["keyword", "else"],
      ["number", "0"],
      ["keyword", "done"],
    ],
  );
});

test("tokenize positions are UTF-16 indices", () => {
  const [string, number] = createTokenizer(compiler)('"😀" 1');
  assert.deepEqual([string.from, string.to, number.from, number.to], [0, 4, 5, 6]);
});

test("tokenize still colors a program with a syntax error, call after call", () => {
  const tokenize = createTokenizer(compiler);
  for (let i = 0; i < 50; i++) {
    assert.ok(tokenize('if x then ))) "oops').some((t) => t.kind === "keyword"));
  }
  assert.deepEqual(tokenize(""), []);
});
