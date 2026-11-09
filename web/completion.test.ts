import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { CompletionContext } from "@codemirror/autocomplete";
import { EditorState } from "@codemirror/state";
import { createCompleter, decodeCompletions, loadVocabulary } from "./compile.ts";
import { goatCompletions } from "./completion.ts";

const compiler = await WebAssembly.compile(
  readFileSync(new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", import.meta.url)),
);
const complete = createCompleter(compiler);

// The completions for `marked` with its cursor at the last `|` (a tag
// declaration has its own). Every source below is a half-typed buffer.
function at(marked: string) {
  const cursor = marked.lastIndexOf("|");
  const source = marked.slice(0, cursor) + marked.slice(cursor + 1);
  const found = complete(source, cursor);
  return found && { from: found.from, labels: found.options.map((o) => o.label), options: found.options };
}

const option = (found: NonNullable<ReturnType<typeof at>>, label: string) => {
  const hit = found.options.find((o) => o.label === label);
  assert.ok(hit, `${label} offered: ${found.labels.join()}`);
  return hit;
};

test("the vocabulary export still lists the grammar's keywords and the host's names", () => {
  const named = (kind: string) => loadVocabulary(compiler).filter((w) => w.kind === kind).map((w) => w.name);
  assert.ok(named("keyword").includes("match"));
  assert.ok(named("function").includes("forward"));
});

test("a dot offers the members of the value's type, and only those", () => {
  const found = at('p = {x: 1, name: "goat"}\nturtle = {heading: 90, pen_down: true}\np.|')!;
  assert.deepEqual(found.labels, ["x", "name"]);
  assert.equal(option(found, "x").kind, "field");
  assert.equal(option(found, "x").detail, "Number");
  assert.equal(option(found, "name").detail, "String");
  const turtle = at('p = {x: 1}\nturtle = {heading: 90, pen_down: true}\nturtle.|')!;
  assert.deepEqual(turtle.labels, ["heading", "pen_down"]);
  assert.equal(option(turtle, "pen_down").detail, "Bool");
});

test("a half-typed member narrows the same list and a chain follows each step's type", () => {
  const found = at("turtle = {heading: 90, height: 2, pen: true}\nturtle.he|")!;
  assert.deepEqual(found.labels, ["heading", "height"]);
  assert.equal(found.from, "turtle = {heading: 90, height: 2, pen: true}\nturtle.".length);
  assert.deepEqual(at("w = {pos: {x: 1, y: 2}, n: 0}\nw.pos.|")!.labels, ["x", "y"]);
});

test("a dot after something with no members offers nothing", () => {
  assert.equal(at("n = 1\nn.|"), null);
});

test("a binding's value offers the names in scope, the builtins and the tags", () => {
  const found = at('size = 40\nname = "goat"\nc = |')!;
  const rank = (label: string) => {
    const place = found.labels.indexOf(label);
    assert.ok(place >= 0, `${label} offered`);
    return place;
  };
  assert.ok(rank("name") < rank("size"), "the latest binding first");
  assert.ok(rank("size") < rank("forward"), "the program's names before the host's");
  assert.ok(rank("forward") < rank("Tick") && rank("Tick") < rank("match"));
  assert.equal(option(found, "size").kind, "variable");
  assert.equal(option(found, "size").detail, "Number");
  assert.equal(option(found, "forward").kind, "function");
  assert.equal(option(found, "forward").detail, "(Number) -> Unit");
  assert.equal(option(found, "item").detail, "(xs, n)");
  assert.equal(option(found, "print").kind, "function");
  assert.equal(option(found, "Tick").kind, "tag");
  assert.equal(option(found, "match").kind, "keyword");
  assert.ok(!found.labels.includes("c"), "not the name being defined");
});

test("tags the program declares come before the host's", () => {
  const labels = at("tag Blob\ntag Shape = Circle(Number) | Dot\nx = |")!.labels;
  assert.ok(labels.indexOf("Blob") < labels.indexOf("Empty"));
  assert.ok(labels.indexOf("Circle") < labels.indexOf("Tick"));
});

test("a match arm offers the scrutinee's tags with their payloads, minus the arms already written", () => {
  const head = "tag Shape = Circle(Number) | Square(Number) | Dot\ns = Dot\n";
  const fresh = at(`${head}match s do\n  |`)!;
  const tags = fresh.options.filter((o) => o.kind === "tag");
  assert.deepEqual(tags.map((o) => o.label), ["Circle", "Square", "Dot"]);
  assert.equal(option(fresh, "Circle").detail, "Number");
  assert.equal(option(fresh, "Dot").detail, "");
  assert.ok(!fresh.labels.includes("Tick"), "the host's tags are not this value's");
  const later = at(`${head}match s do\n  Circle(r) then r\n  |`)!;
  assert.ok(!later.labels.includes("Circle") && later.labels.includes("Square") && later.labels.includes("Dot"));
  assert.deepEqual(at(`${head}match s do\n  Sq|`)!.labels, ["Square"]);
});

test("a match arm, a binding value and a member all complete on a buffer that does not parse", () => {
  assert.ok(at("p = {x: 1, y: 2}\nforward(p.|\nback(3")!.labels.includes("y"));
  assert.ok(at("a = 1\nb = {x: 2\nc = |")!.labels.includes("b"));
  assert.ok(at("tag T = A | B\nf = program(t) do\n  match t do\n    A then 1\n    |")!.labels.includes("B"));
});

test("a prefix narrows the list and a complete word is not offered again", () => {
  const found = at("size = 4\nx = si|")!;
  assert.equal(found.labels[0], "size");
  assert.ok(found.labels.every((l) => l.toLowerCase().startsWith("si")));
  assert.ok(!at("size = 4\nx = size|")!.labels.includes("size"));
});

test("a construct waiting for a keyword offers it", () => {
  assert.deepEqual(at("if x |")!.labels, ["then", "done"]);
});

test("nothing is offered in a comment, a string, a number or where a name is introduced", () => {
  for (const marked of ["# fo|", 'x = "fo|"', "x = 12|", "f = program(a, |", "for |", "tag |"])
    assert.equal(at(marked), null, marked);
});

test("positions count UTF-16 units, not bytes", () => {
  const found = at("é = {ü: 1, ñ: 2}\né.|")!;
  assert.deepEqual(found.labels, ["ü", "ñ"]);
  assert.equal(found.from, "é = {ü: 1, ñ: 2}\né.".length);
});

test("an empty payload decodes to nothing", () => {
  assert.equal(decodeCompletions(new Uint8Array(), ""), null);
});

test("typing a letter or a dot opens the list but an empty position needs Ctrl-Space", () => {
  const source = goatCompletions(complete);
  const ask = (doc: string, explicit: boolean) =>
    source(new CompletionContext(EditorState.create({ doc }), doc.length, explicit)) as {
      options: unknown[];
      from: number;
    } | null;
  assert.ok(ask("fo", false)!.options.length > 0);
  assert.ok(ask("p = {x: 1}\np.", false)!.options.length > 0);
  assert.equal(ask("forward(10);\n", false), null);
  assert.ok(ask("forward(10);\n", true)!.options.length > 0);
});

test("the editor receives the compiler's order and kinds, unfiltered", () => {
  const doc = "p = {x: 1}\np.";
  const result = goatCompletions(complete)(
    new CompletionContext(EditorState.create({ doc }), doc.length, true),
  ) as unknown as { options: { label: string; type: string; detail?: string }[]; filter: boolean };
  assert.equal(result.filter, false);
  assert.deepEqual(result.options, [{ label: "x", detail: "Number", type: "property" }]);
});
