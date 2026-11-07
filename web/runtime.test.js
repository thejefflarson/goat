import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { formatNumber, readString, run, strokes } from "./runtime.js";

const compilerWasm = new URL(
  "../target/wasm32-unknown-unknown/release/goat_web.wasm",
  import.meta.url,
);

async function compile(source) {
  const { instance } = await WebAssembly.instantiate(readFileSync(compilerWasm), {});
  const { memory, gw_alloc, gw_free, gw_compile, gw_free_result } = instance.exports;
  const text = new TextEncoder().encode(source);
  const src = gw_alloc(text.length);
  new Uint8Array(memory.buffer, src, text.length).set(text);
  const rec = gw_compile(src, text.length);
  gw_free(src, text.length);
  const view = new DataView(memory.buffer);
  const tag = view.getUint8(rec);
  const payload = new Uint8Array(memory.buffer, rec + 5, view.getUint32(rec + 1, true)).slice();
  gw_free_result(rec);
  assert.equal(tag, 0, new TextDecoder().decode(payload));
  return payload;
}

test("turtle commands are recorded in order", async () => {
  const wasm = await compile(
    'color("red"); for i from 1 to 2 do forward(10); right(90) done; pen_up(); back(5); pen_down(); left(45)',
  );
  const { commands, output, liveAllocs } = await run(wasm);
  assert.deepEqual(commands, [
    { kind: "color", value: "red" },
    { kind: "forward", value: 10 },
    { kind: "right", value: 90 },
    { kind: "forward", value: 10 },
    { kind: "right", value: 90 },
    { kind: "pen_up" },
    { kind: "back", value: 5 },
    { kind: "pen_down" },
    { kind: "left", value: 45 },
  ]);
  assert.deepEqual(output, []);
  assert.equal(liveAllocs, 0);
});

test("the spiral example records its commands and leaks nothing", async () => {
  const source = readFileSync(new URL("../examples/spiral.goat", import.meta.url), "utf8");
  const { commands, liveAllocs } = await run(await compile(source));
  assert.equal(commands.length, 121);
  assert.deepEqual(commands[0], { kind: "color", value: "purple" });
  assert.deepEqual(commands[1], { kind: "forward", value: 3 });
  assert.deepEqual(commands[2], { kind: "right", value: 89 });
  assert.equal(liveAllocs, 0);
});

test("printed text matches the CLI's formatting", async () => {
  const wasm = await compile(
    'print(55); print(0.1 + 0.2); print(1 / 3); print(true); print("hi")',
  );
  const { output, liveAllocs } = await run(wasm);
  assert.deepEqual(output, ["55", "0.3", "0.333333333333333", "true", "hi"]);
  assert.equal(liveAllocs, 0);
});

test("composite values stream through the write_* imports as one line", async () => {
  const { output } = await run(await compile('print([1, 2.5]); print("a")'));
  assert.deepEqual(output, ["[1, 2.5]", "a"]);
});

test("formatNumber ports goat::format_number", () => {
  const cases = [
    [55, "55"], [-0, "0"], [-7, "-7"], [1e17, "100000000000000000"],
    [1e18, "1e+18"], [1.5, "1.5"], [0.1 + 0.2, "0.3"], [1 / 3, "0.333333333333333"],
    [123456789012345.6, "123456789012346"], [1e-5, "1e-05"], [0.0001, "0.0001"],
    [1.5e300, "1.5e+300"], [-2.5e-10, "-2.5e-10"], [Infinity, "inf"],
    [-Infinity, "-inf"], [NaN, "nan"],
  ];
  for (const [x, text] of cases) assert.equal(formatNumber(x), text, String(x));
});

test("strings are read at the documented offsets and bounds-checked", () => {
  const memory = new WebAssembly.Memory({ initial: 1 });
  const bytes = new TextEncoder().encode("héllo");
  new DataView(memory.buffer).setUint32(16 + 8, bytes.length, true);
  new Uint8Array(memory.buffer).set(bytes, 16 + 12);
  assert.equal(readString(memory, 16), "héllo");
  assert.throws(() => readString(memory, 65536 - 4), /out of bounds/);
  new DataView(memory.buffer).setUint32(8, 0xffffff, true);
  assert.throws(() => readString(memory, 0), /out of bounds/);
});

test("strokes mirror the CLI replay", () => {
  const log = [
    { kind: "forward", value: 10 },
    { kind: "right", value: 90 },
    { kind: "forward", value: 10 },
    { kind: "pen_up" },
    { kind: "forward", value: 5 },
    { kind: "pen_down" },
    { kind: "color", value: "red" },
    { kind: "back", value: 5 },
  ];
  const near = (a, b) => a.every((v, i) => Math.abs(v - b[i]) < 1e-9);
  const result = strokes(log);
  assert.equal(result.length, 2);
  assert.equal(result[0].color, "black");
  assert.equal(result[0].points.length, 3);
  assert.ok(near(result[0].points[2], [10, -10]));
  assert.equal(result[1].color, "red");
  assert.ok(near(result[1].points[0], [15, -10]));
  assert.ok(near(result[1].points[1], [10, -10]));
});

test("an invalid color and a non-finite number trap", async () => {
  const bad = await compile('color("re d"); forward(1)');
  await assert.rejects(run(bad), /color wants a name/);
  const nan = await compile("forward(0 / 0)");
  await assert.rejects(run(nan), /real number/);
});
