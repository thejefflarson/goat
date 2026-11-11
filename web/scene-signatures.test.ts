import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { RecordingScene, newString, sceneImports } from "./scene.ts";

// The wire protocol's arity table, one `name type...` line per scene call.
// mir/tests/vocab.rs checks the same file against Vocab::turtle() and the Rust
// scene host, so a mismatch on either side fails CI.
const golden = new Map(
  readFileSync(new URL("./scene-signatures.txt", import.meta.url), "utf8")
    .trim()
    .split("\n")
    .map((line) => {
      const [name, ...params] = line.split(" ");
      return [name!, params] as const;
    }),
);

test("each scene import takes the golden arity and records the golden field types", () => {
  const memory = new WebAssembly.Memory({ initial: 1 });
  let next = 64;
  const exports = {
    memory,
    goat_alloc: (size: number) => {
      const at = next;
      next += size + 16;
      return at;
    },
  } as unknown as WebAssembly.Exports;
  const recording = new RecordingScene();
  const { scene } = sceneImports(() => memory, recording) as unknown as {
    scene: Record<string, (...args: Array<number | bigint>) => void>;
  };

  assert.deepEqual(Object.keys(scene).sort(), [...golden.keys()].sort());
  for (const [name, params] of golden) {
    const call = scene[name]!;
    assert.equal(call.length, params.length, `scene.${name} arity`);
    recording.commands.length = 0;
    // An Int crosses the wasm boundary as a BigInt and is recorded as a number.
    call(...params.map((type) => (type === "string" ? newString(exports, "red") : type === "int" ? 1n : 1.5)));
    assert.equal(recording.commands.length, 1, `scene.${name} records one command`);
    const [{ kind, ...fields }] = recording.commands as [{ kind: string }];
    assert.equal(kind, name);
    const recorded = params.map((type) => (type === "int" ? "number" : type));
    assert.deepEqual(Object.values(fields).map((value) => typeof value), recorded, `scene.${name} fields`);
  }
});
