import assert from "node:assert/strict";
import test from "node:test";
import { Stage } from "./stage.ts";

// Just enough of a DOM: an element knows its parent and can be replaced.
class FakeCanvas {
  parentElement: { children: FakeCanvas[] };
  transferred = false;
  focused = false;

  constructor(parent: { children: FakeCanvas[] }) {
    this.parentElement = parent;
  }
  cloneNode(): FakeCanvas {
    return new FakeCanvas(this.parentElement);
  }
  replaceWith(next: FakeCanvas) {
    const children = this.parentElement.children;
    children[children.indexOf(this)] = next;
  }
  transferControlToOffscreen() {
    assert.equal(this.transferred, false, "a canvas can be transferred only once");
    this.transferred = true;
    return { from: this };
  }
  focus() {
    this.focused = true;
  }
}

function stage() {
  const parent = { children: [] as FakeCanvas[] };
  const original = new FakeCanvas(parent);
  parent.children.push(original);
  return { parent, original, stage: new Stage(original as unknown as HTMLCanvasElement) };
}

test("every surface is a fresh canvas swapped into the same place", () => {
  const { parent, original, stage: s } = stage();
  const first = s.surface() as unknown as { from: FakeCanvas };
  const second = s.surface() as unknown as { from: FakeCanvas };
  assert.notEqual(first.from, second.from);
  assert.notEqual(first.from, original);
  assert.deepEqual(parent.children, [second.from]);
  assert.equal(s.canvas as unknown, second.from);
  assert.equal(s.container as unknown, parent);
});

test("focus goes to the current canvas", () => {
  const { stage: s } = stage();
  const { from } = s.surface() as unknown as { from: FakeCanvas };
  s.focus();
  assert.equal(from.focused, true);
});
