import assert from "node:assert/strict";
import test from "node:test";
import { forwardInput } from "./input.ts";
import type { DomEvent } from "./loop.ts";
import type { EventKind, HostEvent } from "./scene.ts";

type Listener = (event: DomEvent) => void;

function page(wanted: EventKind[], rect = { left: 10, top: 20, width: 150, height: 150 }) {
  const listeners = new Map<string, Listener[]>();
  const events: ListenerTargetLike = {
    addEventListener: (type, listener) => listeners.set(type, [...(listeners.get(type) ?? []), listener]),
    removeEventListener: (type, listener) =>
      listeners.set(type, (listeners.get(type) ?? []).filter((l) => l !== listener)),
  };
  const sent: HostEvent[] = [];
  const set = new Set(wanted);
  const detach = forwardInput(
    events,
    () => ({ width: 300, height: 300, getBoundingClientRect: () => rect }),
    { wants: (kind) => set.has(kind), input: (event) => sent.push(event) },
  );
  const fire = (type: string, event: DomEvent) => (listeners.get(type) ?? []).forEach((l) => l(event));
  const count = () => [...listeners.values()].reduce((n, l) => n + l.length, 0);
  return { fire, sent, detach, count, wanted: set };
}

interface ListenerTargetLike {
  addEventListener(type: string, listener: Listener): void;
  removeEventListener(type: string, listener: Listener): void;
}

test("a subscribed key press is forwarded and swallowed; an unsubscribed one is left alone", () => {
  const { fire, sent } = page(["KeyDown"]);
  let prevented = 0;
  fire("keydown", { key: "ArrowUp", preventDefault: () => prevented++ });
  fire("keyup", { key: "ArrowUp", preventDefault: () => prevented++ });
  assert.deepEqual(sent, [{ kind: "KeyDown", key: "ArrowUp" }]);
  assert.equal(prevented, 1);
});

test("pointer events are forwarded in the canvas's pixel space", () => {
  const { fire, sent } = page(["PointerMove", "PointerUp"]);
  fire("pointermove", { clientX: 85, clientY: 95 });
  fire("pointerdown", { clientX: 85, clientY: 95 });
  fire("pointerup", { clientX: 160, clientY: 170 });
  assert.deepEqual(sent, [
    { kind: "PointerMove", x: 150, y: 150 },
    { kind: "PointerUp", x: 300, y: 300 },
  ]);
});

test("a canvas with no size forwards no pointer events", () => {
  const { fire, sent } = page(["PointerMove"], { left: 0, top: 0, width: 0, height: 0 });
  fire("pointermove", { clientX: 5, clientY: 5 });
  assert.deepEqual(sent, []);
});

test("subscriptions that arrive after the listeners were attached take effect", () => {
  const { fire, sent, wanted } = page([]);
  fire("keydown", { key: "a" });
  wanted.add("KeyDown");
  fire("keydown", { key: "b" });
  assert.deepEqual(sent, [{ kind: "KeyDown", key: "b" }]);
});

test("detaching removes every listener", () => {
  const { fire, sent, detach, count } = page(["KeyDown"]);
  assert.equal(count(), 5);
  detach();
  assert.equal(count(), 0);
  fire("keydown", { key: "a" });
  assert.deepEqual(sent, []);
});
