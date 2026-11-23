// The goat formatter end to end in one process: the real worker core stands in
// for the Web Worker behind the real supervisor, so an edit travels the whole
// way (event, goat `update`, `draw`, `scene.edit`, message, validation, one
// CodeMirror transaction).

import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import test from "node:test";
import { history, undo } from "@codemirror/commands";
import { EditorState } from "@codemirror/state";
import { formatTransaction } from "./editor.ts";
import { GoatFormatter, type TextEdit, acceptEdits } from "./formatter.ts";
import type { FromWorker, ToWorker } from "./protocol.ts";
import { Supervisor, type WorkerLike } from "./supervisor.ts";
import { createWorkerCore } from "./worker-core.ts";

const compiler = await WebAssembly.compile(
  readFileSync(new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", import.meta.url)),
);
const source = readFileSync(new URL("../editor/format.goat", import.meta.url), "utf8");

const capable = { crossOriginIsolated: true, SharedArrayBuffer, Worker: class {}, OffscreenCanvas: class {} };

function inProcessWorker(): WorkerLike {
  const worker: WorkerLike = {
    onmessage: null,
    onerror: null,
    postMessage: (message: ToWorker) => void core.handle(message),
    terminate: () => {},
  };
  const core = createWorkerCore({
    post: (message: FromWorker) => worker.onmessage?.({ data: message }),
    raf: () => 0,
    cancelRaf: () => {},
    now: () => performance.now(),
  });
  return worker;
}

async function formatter(): Promise<GoatFormatter> {
  const runner = new Supervisor(
    {
      spawn: inProcessWorker,
      surface: () => ({ width: 1, height: 1 }) as OffscreenCanvas,
      now: () => performance.now(),
      every: () => () => {},
    },
    capable,
  );
  const goat = new GoatFormatter({ compiler, source, runner });
  assert.equal(await goat.start(), true, "the formatter started");
  return goat;
}

function apply(text: string, edits: TextEdit[]): string {
  return edits.reduceRight((out, { from, to, insert }) => out.slice(0, from) + insert + out.slice(to), text);
}

test("the formatter program's edits lay the text out in the house style", async () => {
  const goat = await formatter();
  const text = "f = program(x) do\nx+1\ndone\n\n\n\ny   = [1,2]";
  assert.equal(apply(text, await goat.format(text)), "f = program(x) do\n  x + 1\ndone\n\ny = [1, 2]\n");
  goat.stop();
});

test("every example and the prelude are already formatted, so the formatter has nothing to say", async () => {
  const goat = await formatter();
  const files: URL[] = [];
  for (const directory of ["../examples/", "../examples/canvas/", "../prelude/"]) {
    const dir = new URL(directory, import.meta.url);
    for (const name of readdirSync(dir).filter((name) => name.endsWith(".goat"))) files.push(new URL(name, dir));
  }
  assert.ok(files.length > 30);
  for (const file of files) assert.deepEqual(await goat.format(readFileSync(file, "utf8")), [], file.pathname);
  goat.stop();
});

test("edits are in UTF-16 offsets, though the program counts bytes", async () => {
  const goat = await formatter();
  const text = 'a = "é"   +   1 # é\n';
  assert.equal(apply(text, await goat.format(text)), 'a = "é" + 1 # é\n');
  goat.stop();
});

test("a formatted document is one undoable transaction", async () => {
  const goat = await formatter();
  const doc = "f = program(x) do\nx+1\ndone\n\n\n\ny   = [1,2]";
  const edits = await goat.format(doc);
  assert.ok(edits.length > 2, "several edits");
  let state = EditorState.create({ doc, extensions: [history()] });
  state = state.update(formatTransaction(edits)).state;
  assert.equal(state.doc.toString(), "f = program(x) do\n  x + 1\ndone\n\ny = [1, 2]\n");
  const dispatch = (transaction: { state: EditorState }) => void (state = transaction.state);
  assert.equal(undo({ state, dispatch }), true);
  assert.equal(state.doc.toString(), doc, "one undo restores the whole document");
  goat.stop();
});

test("an edit that is malformed, out of order or over more than whitespace is dropped", () => {
  const text = "a = 1\nb = 2\n";
  const edit = (from: unknown, to: unknown, newlines: unknown = 0, indent: unknown = 1) => ({
    from,
    to,
    newlines,
    indent,
  });
  assert.deepEqual(acceptEdits("nope", text), []);
  assert.deepEqual(acceptEdits(null, text), []);
  assert.deepEqual(
    acceptEdits(
      [
        null,
        42,
        {},
        edit(0, 1),
        edit(-1, 2),
        edit(1.5, 2),
        edit("1", 2),
        edit(2, 1),
        edit(1, 999),
        edit(1, 2, -1),
        edit(1, 2, 0, 9999),
        edit(1, 2, 99, 0),
        edit(1, 2, 0, Number.NaN),
        edit(1, 2, 0, 1),
        edit(1, 2, 0, 1),
        edit(3, 4, 0, 1),
      ],
      text,
    ),
    [
      { from: 1, to: 2, insert: " " },
      { from: 3, to: 4, insert: " " },
    ],
  );
});

test("an edit may not start or end inside a character", () => {
  const text = "é x";
  assert.deepEqual(acceptEdits([{ from: 1, to: 2, newlines: 0, indent: 1 }], text), []);
  assert.deepEqual(acceptEdits([{ from: 2, to: 3, newlines: 0, indent: 0 }], text), [{ from: 1, to: 2, insert: "" }]);
});

test("an edit that would make start at, or join a comment to the next line, refuses the format", () => {
  const edit = (from: number, to: number, newlines: number, indent: number) => ({ from, to, newlines, indent });
  assert.throws(() => acceptEdits([edit(5, 7, 0, 1)], "start  at 1\n"), /start at/);
  assert.deepEqual(acceptEdits([edit(5, 7, 0, 3)], "start  at 1\n"), [{ from: 5, to: 7, insert: "   " }]);
  assert.deepEqual(acceptEdits([edit(6, 8, 0, 1)], "xstart  at 1\n"), [{ from: 6, to: 8, insert: " " }]);

  const commented = "a = 1 # one\nb = 2\n";
  assert.throws(() => acceptEdits([edit(11, 12, 0, 1)], commented), /comment/);
  assert.throws(() => acceptEdits([edit(11, 12, 0, 0)], commented), /comment/);
  assert.deepEqual(acceptEdits([edit(11, 12, 2, 0)], commented), [{ from: 11, to: 12, insert: "\n\n" }]);
  assert.deepEqual(acceptEdits([edit(5, 6, 0, 2)], commented), [{ from: 5, to: 6, insert: "  " }]);

  const quoted = 'a = "#" + 1\n';
  assert.deepEqual(acceptEdits([edit(7, 8, 0, 1)], quoted), [{ from: 7, to: 8, insert: " " }]);
});

test("an edit over whitespace the lexer does not read refuses the format", () => {
  assert.throws(() => acceptEdits([{ from: 3, to: 5, newlines: 0, indent: 1 }], "a = 1\n"), /not whitespace/);
  assert.throws(() => acceptEdits([{ from: 3, to: 6, newlines: 0, indent: 1 }], "a =  1\n"), /not whitespace/);
});

test("a formatter that is not running rejects", async () => {
  const goat = await formatter();
  goat.stop();
  await assert.rejects(goat.format("x = 1"), /not running/);
});
