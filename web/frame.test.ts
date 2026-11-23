import assert from "node:assert/strict";
import test from "node:test";
import { FrameDecoder, type FrameValue } from "./frame.ts";
import { RecordingScene, sceneImports } from "./scene.ts";

const enc = new TextEncoder();

type Wire = "i" | "f" | "b" | "s";

function header(calls: Array<[string, Wire[]]>, version = 1): number[] {
  const out = [version, calls.length];
  for (const [name, wires] of calls) {
    const bytes = enc.encode(name);
    out.push(bytes.length, ...bytes, wires.length, ...wires.map((w) => w.charCodeAt(0)));
  }
  return out;
}

function f64(x: number): number[] {
  return [...new Uint8Array(new Float64Array([x]).buffer)];
}

function i64(n: bigint): number[] {
  return [...new Uint8Array(new BigInt64Array([n]).buffer)];
}

function str(s: string): number[] {
  const bytes = enc.encode(s);
  return [...new Uint8Array(new Uint32Array([bytes.length]).buffer), ...bytes];
}

const CIRCLE: [string, Wire[]] = ["circle", ["f", "f", "f", "s"]];

function circleFrame(): Uint8Array {
  return Uint8Array.from([...header([CIRCLE]), 0, ...f64(1), ...f64(2), ...f64(3), ...str("red")]);
}

function replayed(bytes: Uint8Array): Array<[string, FrameValue[]]> {
  const seen: Array<[string, FrameValue[]]> = [];
  new FrameDecoder((name) => (args) => seen.push([name, [...args]])).replay(bytes);
  return seen;
}

test("a frame replays the calls it declares, one per record", () => {
  const bytes = Uint8Array.from([
    ...header([CIRCLE, ["edit", ["i", "i", "b"]]]),
    0, ...f64(1), ...f64(-2.5), ...f64(3), ...str("héllo"),
    1, ...i64(-7n), ...i64(9n), 1,
    0, ...f64(0), ...f64(0), ...f64(0), ...str(""),
  ]);
  assert.deepEqual(replayed(bytes), [
    ["circle", [1, -2.5, 3, "héllo"]],
    ["edit", [-7, 9, true]],
    ["circle", [0, 0, 0, ""]],
  ]);
});

test("a frame with a header and no records replays nothing", () => {
  assert.deepEqual(replayed(Uint8Array.from(header([CIRCLE]))), []);
});

test("every cut of a frame short of a whole record is rejected", () => {
  const whole = circleFrame();
  const record = whole.length - (1 + 24 + 4 + 3);
  for (let len = 0; len < whole.length; len++) {
    const cut = whole.slice(0, len);
    if (len === record) assert.deepEqual(replayed(cut), []);
    else assert.throws(() => replayed(cut), Error, `cut at ${len}`);
  }
});

test("a string that claims more bytes than the frame has is rejected", () => {
  const bytes = circleFrame();
  new DataView(bytes.buffer).setUint32(bytes.length - 7, 0xffffffff, true);
  assert.throws(() => replayed(bytes), /ends in the middle/);
});

test("a wrong version, an undeclared call, an unknown wire and a bad name are rejected", () => {
  assert.throws(() => replayed(Uint8Array.from(header([CIRCLE], 2))), /version 2/);
  const undeclared = circleFrame();
  undeclared[header([CIRCLE]).length] = 9;
  assert.throws(() => replayed(undeclared), /did not declare/);
  assert.throws(() => replayed(Uint8Array.from(header([["x", ["?" as Wire]]]))), /unknown value type/);
  const named = Uint8Array.from(header([["abc", []]]));
  named[3] = 0xff;
  assert.throws(() => replayed(named), /not text/);
  assert.throws(() => replayed(new Uint8Array(0)), /ends in the middle/);
  assert.throws(() => replayed(Uint8Array.from([1, 200])), /ends in the middle/);
});

test("a call the host has no handler for is rejected", () => {
  const decoder = new FrameDecoder(() => undefined);
  assert.throws(() => decoder.replay(circleFrame()), /no scene call circle/);
});

test("a changed header is read again, and an unchanged one is reused", () => {
  const seen: string[] = [];
  const resolved: string[] = [];
  const decoder = new FrameDecoder((name) => {
    resolved.push(name);
    return () => seen.push(name);
  });
  decoder.replay(circleFrame());
  decoder.replay(circleFrame());
  assert.deepEqual(resolved, ["circle"]);
  const other = Uint8Array.from([...header([["edit", ["i"]]]), 0, ...i64(1n)]);
  decoder.replay(other);
  assert.deepEqual(resolved, ["circle", "edit"]);
  assert.deepEqual(seen, ["circle", "circle", "edit"]);
});

function wasmWith(bytes: Uint8Array, at: number) {
  const memory = new WebAssembly.Memory({ initial: 1 });
  new Uint8Array(memory.buffer).set(bytes, at);
  const scene = new RecordingScene();
  return { memory, scene, imports: sceneImports(() => memory, scene).scene };
}

test("scene.frame draws what the frame encodes and checks colors and coordinates", () => {
  const frame = circleFrame();
  const { scene, imports } = wasmWith(frame, 128);
  imports.frame(128, frame.length);
  assert.deepEqual(scene.commands, [{ kind: "circle", x: 1, y: 2, r: 3, color: "red" }]);

  const bad = Uint8Array.from([...header([CIRCLE]), 0, ...f64(1), ...f64(2), ...f64(3), ...str('"/><script>')]);
  const evil = wasmWith(bad, 0);
  assert.throws(() => evil.imports.frame(0, bad.length), /color wants a name/);

  const infinite = Uint8Array.from([...header([CIRCLE]), 0, ...f64(Infinity), ...f64(2), ...f64(3), ...str("red")]);
  const far = wasmWith(infinite, 0);
  assert.throws(() => far.imports.frame(0, infinite.length), /real number/);
});

test("scene.frame rejects a range outside the module's memory", () => {
  const { imports } = wasmWith(circleFrame(), 0);
  for (const [ptr, len] of [
    [65536, 1],
    [65535, 2],
    [-1, 1],
    [0, -1],
    [-1, -1],
  ] as const) {
    assert.throws(() => imports.frame(ptr, len), /out of bounds/, `(${ptr}, ${len})`);
  }
  assert.throws(() => imports.frame(0, 0), Error);
});
