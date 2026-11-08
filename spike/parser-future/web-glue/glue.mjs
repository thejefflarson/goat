// SPIKE: the browser-split architecture for a tree-sitter parser.
//   source --(web-tree-sitter wasm + grammar wasm)--> tree --(this glue)--> JSON --> goat checker wasm
// Runs the same wasm files in Node that a page would fetch; node:fs stands in
// for fetch. The checker-side deserializer does not exist (see the writeup).
import { readFileSync } from "node:fs";
import { Language, Parser } from "web-tree-sitter";

await Parser.init();
const parser = new Parser();
parser.setLanguage(
  await Language.load(readFileSync(new URL("../tree-sitter-goat-slice/goat_slice.wasm", import.meta.url))),
);

/** The wire format handed to the Rust side: one flat, serializable record per node. */
function toWire(node) {
  return {
    kind: node.type,
    start: node.startIndex,
    end: node.endIndex,
    missing: node.isMissing,
    error: node.isError,
    children: node.children.map(toWire),
  };
}

/** Tree-sitter has no messages: diagnostics are synthesized from ERROR / MISSING nodes. */
function diagnostics(node, out = []) {
  if (node.isMissing) out.push(`${node.startIndex}: missing \`${node.type}\``);
  else if (node.isError) out.push(`${node.startIndex}..${node.endIndex}: unexpected input`);
  for (const child of node.children) diagnostics(child, out);
  return out;
}

const inputs = {
  good: "a = 1 + 2;\nb = match a do\n  3 then 4\ndone",
  missingValue: "a = ;\nb = 2;\nb",
  matchNoDone: "match x do",
  unterminated: "m = match x do\n  A then 1\ny = 2;\ny",
};
for (const [name, src] of Object.entries(inputs)) {
  const tree = parser.parse(src);
  const wire = JSON.stringify(toWire(tree.rootNode));
  console.log(`${name}: wire=${wire.length}B diagnostics=${JSON.stringify(diagnostics(tree.rootNode))}`);
  console.log("  ", tree.rootNode.toString());
}
