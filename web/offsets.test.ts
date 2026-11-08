import assert from "node:assert/strict";
import test from "node:test";
import { utf16Offsets } from "./offsets.ts";

test("ASCII offsets are unchanged", () => {
  const index = utf16Offsets("abc");
  assert.deepEqual([0, 1, 2, 3].map(index), [0, 1, 2, 3]);
});

test("a multi-byte character is one UTF-16 unit, or two when astral", () => {
  // a is 1 byte, é 2, 日 3, 😀 4 (and two UTF-16 units).
  const index = utf16Offsets("aé日😀b");
  assert.deepEqual([0, 1, 3, 6, 10, 11].map(index), [0, 1, 2, 3, 5, 6]);
});

test("offsets past the end clamp to the end", () => {
  assert.equal(utf16Offsets("é")(99), 1);
  assert.equal(utf16Offsets("")(5), 0);
});
