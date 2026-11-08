import assert from "node:assert/strict";
import test from "node:test";
import { Heartbeat, missingCapability } from "./protocol.ts";

test("the heartbeat is odd while goat runs and even while the worker idles", () => {
  const heartbeat = new Heartbeat();
  assert.equal(Heartbeat.busy(heartbeat.read()), false);
  let during = -1;
  heartbeat.during(() => (during = heartbeat.read()));
  assert.equal(Heartbeat.busy(during), true);
  assert.equal(Heartbeat.busy(heartbeat.read()), false);
  assert.equal(heartbeat.read(), 2);
});

test("a call that throws still leaves the heartbeat idle", () => {
  const heartbeat = new Heartbeat();
  assert.throws(() => heartbeat.during(() => { throw new Error("trap"); }), /trap/);
  assert.equal(Heartbeat.busy(heartbeat.read()), false);
});

test("both sides of a shared buffer see the same word", () => {
  const worker = new Heartbeat();
  const supervisor = new Heartbeat(worker.buffer);
  worker.enter();
  assert.equal(supervisor.read(), 1);
  assert.equal(Heartbeat.busy(supervisor.read()), true);
});

test("parity survives the counter wrapping around", () => {
  const buffer = new SharedArrayBuffer(4);
  new Int32Array(buffer)[0] = 2 ** 31 - 1;
  const heartbeat = new Heartbeat(buffer);
  assert.equal(Heartbeat.busy(heartbeat.read()), true);
  heartbeat.leave();
  assert.equal(heartbeat.read(), -(2 ** 31));
  assert.equal(Heartbeat.busy(heartbeat.read()), false);
});

const capable = { crossOriginIsolated: true, SharedArrayBuffer, Worker: class {}, OffscreenCanvas: class {} };

test("a page missing isolation, SharedArrayBuffer, Worker or OffscreenCanvas is named", () => {
  assert.equal(missingCapability(capable), null);
  assert.match(missingCapability({ ...capable, crossOriginIsolated: false })!, /cross-origin isolated/);
  assert.match(missingCapability({ ...capable, crossOriginIsolated: undefined })!, /Cross-Origin-Opener-Policy/);
  assert.match(missingCapability({ ...capable, SharedArrayBuffer: undefined })!, /SharedArrayBuffer/);
  assert.match(missingCapability({ ...capable, Worker: undefined })!, /Worker/);
  assert.match(missingCapability({ ...capable, OffscreenCanvas: undefined })!, /OffscreenCanvas/);
});
