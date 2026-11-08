import assert from "node:assert/strict";
import test from "node:test";
import { type BeatMessage, createBeat } from "./beat.ts";

test("a call is bracketed by an odd then an even count", () => {
  const seen: BeatMessage[] = [];
  const beat = createBeat((m) => seen.push(m));
  assert.equal(
    beat.around("frame", () => {
      assert.deepEqual(seen, [{ type: "beat", count: 1, call: "frame" }]);
      return 42;
    }),
    42,
  );
  beat.around("once", () => {});
  assert.deepEqual(
    seen.map((m) => [m.count, m.call]),
    [
      [1, "frame"],
      [2, "frame"],
      [3, "once"],
      [4, "once"],
    ],
  );
});

test("a trapping call still reports that it left", () => {
  const seen: BeatMessage[] = [];
  const beat = createBeat((m) => seen.push(m));
  assert.throws(
    () =>
      beat.around("frame", () => {
        throw new Error("trap");
      }),
    /trap/,
  );
  assert.deepEqual(
    seen.map((m) => m.count),
    [1, 2],
  );
});
