import { copyFileSync, cpSync, mkdirSync, rmSync } from "node:fs";
import { fileURLToPath } from "node:url";

const here = new URL(".", import.meta.url);
const wasmSource = new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", here);

// Lays out the page, its compiled modules and the compiler at the relative
// paths index.html references, so the directory can be served as-is.
export function assemble(outDir: string): void {
  rmSync(outDir, { recursive: true, force: true });
  mkdirSync(outDir, { recursive: true });
  copyFileSync(new URL("index.html", here), `${outDir}/index.html`);
  cpSync(new URL("dist", here), `${outDir}/dist`, { recursive: true });
  copyFileSync(wasmSource, `${outDir}/goat_web.wasm`);
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  assemble(fileURLToPath(new URL("site", here)));
}
