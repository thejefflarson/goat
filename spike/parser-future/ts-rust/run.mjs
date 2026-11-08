// Loads the wasm32-unknown-unknown build of the Rust `tree-sitter` binding and
// drives it from JS: node run.mjs ../target/wasm32-unknown-unknown/release/ts_rust.wasm
import { readFileSync } from "node:fs";

const module = await WebAssembly.compile(readFileSync(process.argv[2]));
console.log("imports:", WebAssembly.Module.imports(module));
const { exports } = await WebAssembly.instantiate(module, {});
const hasError = (src) => {
  const bytes = new TextEncoder().encode(src);
  const ptr = exports.alloc(bytes.length);
  new Uint8Array(exports.memory.buffer, ptr, bytes.length).set(bytes);
  return exports.has_error(ptr, bytes.length);
};
for (const src of ["a = 1; b = a + 2", "match x do", "a = ;\nb = 2", "(1 + "]) {
  console.log(JSON.stringify(src), "-> has_error =", hasError(src));
}
