import assert from "node:assert/strict";
import test from "node:test";
import type { Token } from "./compile.ts";
import { tokenDecorations } from "./editor.ts";

test("each token becomes a decoration with its kind's class", () => {
  const tokens: Token[] = [
    { kind: "keyword", from: 0, to: 2 },
    { kind: "string", from: 5, to: 9 },
  ];
  const found: [number, number, string][] = [];
  tokenDecorations(tokens).between(0, 20, (from, to, value) => {
    found.push([from, to, value.spec.class]);
  });
  assert.deepEqual(found, [
    [0, 2, "tok-keyword"],
    [5, 9, "tok-string"],
  ]);
});

test("no tokens, no decorations", () => {
  assert.equal(tokenDecorations([]).size, 0);
});
