import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { CompletionContext } from "@codemirror/autocomplete";
import { EditorState } from "@codemirror/state";
import { createTokenizer, loadVocabulary } from "./compile.ts";
import { boundNames, completionsAt, goatCompletions } from "./completion.ts";

const compiler = await WebAssembly.compile(
  readFileSync(new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", import.meta.url)),
);
const words = loadVocabulary(compiler);
const tokenize = createTokenizer(compiler);

// The completions for `marked` with its cursor at the `|`.
function at(marked: string) {
  const cursor = marked.indexOf("|");
  const source = marked.replace("|", "");
  const found = completionsAt(source, cursor, words, tokenize(source));
  return found && { from: found.from, labels: found.options.map((o) => o.label), options: found.options };
}

const typeOf = (found: NonNullable<ReturnType<typeof at>>, label: string) =>
  found.options.find((o) => o.label === label)?.type;

test("the vocabulary comes from the compiler: keywords, turtle commands, tags", () => {
  const named = (kind: string) => words.filter((w) => w.kind === kind).map((w) => w.name);
  for (const keyword of ["program", "if", "then", "else", "match", "repeat", "times", "for", "done", "true", "foreign"])
    assert.ok(named("keyword").includes(keyword), keyword);
  for (const fn of ["forward", "back", "left", "right", "pen_up", "pen_down", "color", "print", "sort"])
    assert.ok(named("function").includes(fn), fn);
  for (const tag of ["KeyDown", "Polyline", "Line", "Up", "Link"]) assert.ok(named("tag").includes(tag), tag);
  assert.equal(words.find((w) => w.name === "forward")?.detail, "(Number) -> Unit");
  assert.equal(words.find((w) => w.name === "item")?.detail, "(xs, n)");
});

test("a keyword prefix offers keywords", () => {
  const found = at("x = 1\nre|")!;
  assert.equal(found.from, "x = 1\n".length);
  assert.equal(typeOf(found, "repeat"), "keyword");
});

test("a prefix narrows to the names that start with it", () => {
  const found = at("co|")!;
  assert.ok(found.labels.includes("color"));
  assert.ok(found.labels.every((l) => l.toLowerCase().startsWith("co")), found.labels.join());
});

test("a bare position offers the builtins and keywords alike", () => {
  const found = at("|")!;
  assert.equal(found.from, 0);
  for (const label of ["forward", "right", "color", "print", "if", "repeat"]) assert.ok(found.labels.includes(label), label);
  assert.equal(found.options.find((o) => o.label === "forward")?.detail, "(Number) -> Unit");
});

test("a binding before the cursor is offered ahead of the builtins", () => {
  const found = at("size = 40\nforward(si|")!;
  assert.equal(found.labels[0], "size");
  assert.equal(typeOf(found, "size"), "variable");
});

test("parameters, loop variables and match bindings are in scope", () => {
  const source =
    "step = program(model, dx) do\nfor i from 1 to 3 do\nmatch e do\nOther(name) then 1\n[head, ...tail] then 2\n";
  const keywords = new Set(words.filter((w) => w.kind === "keyword").map((w) => w.name));
  assert.deepEqual(
    new Set(boundNames(source, tokenize(source), keywords)),
    new Set(["step", "model", "dx", "i", "name", "head", "tail"]),
  );
});

test("later bindings come first and a name is listed once", () => {
  assert.deepEqual(boundNames("a = 1\nb = 2\na = 3\n", [], new Set()), ["a", "b"]);
});

test("a name bound after the cursor is not offered", () => {
  assert.ok(!at("|\nlater = 1")!.labels.includes("later"));
});

test("comparisons, comments and strings bind nothing", () => {
  const source = 'a == 1\n# hidden = 1\nmsg = "inner = 2"\n';
  assert.deepEqual(boundNames(source, tokenize(source), new Set()), ["msg"]);
});

test("a user name that is also a builtin is offered once, as the user's", () => {
  const found = at("color = 7\ncolo|")!;
  assert.deepEqual(found.labels.filter((l) => l === "color"), ["color"]);
  assert.equal(typeOf(found, "color"), "variable");
});

test("a word that is already complete is not offered again", () => {
  assert.ok(!at("forward|")!.labels.includes("forward"));
});

test("tags the program declares are offered", () => {
  const found = at("tag Blob\nx = Bl|")!;
  assert.equal(typeOf(found, "Blob"), "class");
});

test("half-typed code still completes", () => {
  assert.ok(at("x = program(a, b do\n  if a then fo|")!.labels.includes("forward"));
});

test("nothing is offered in a comment, a string, a field name or a number", () => {
  assert.equal(at("# fo|"), null);
  assert.equal(at('"fo|"'), null);
  assert.equal(at("model.fo|"), null);
  assert.equal(at("12fo|"), null);
  assert.ok(at("{...mo|}"));
});

test("typing a letter opens the list but an empty position needs Ctrl-Space", () => {
  const complete = goatCompletions(words, tokenize);
  const ask = (doc: string, explicit: boolean) =>
    complete(new CompletionContext(EditorState.create({ doc }), doc.length, explicit)) as {
      options: unknown[];
    } | null;
  assert.ok(ask("fo", false)!.options.length > 0);
  assert.equal(ask("forward(10);\n", false), null);
  assert.ok(ask("forward(10);\n", true)!.options.length > 0);
});
