import { copyFileSync, cpSync, mkdirSync, rmSync } from "node:fs";
import { fileURLToPath } from "node:url";

const here = new URL(".", import.meta.url);
const wasmSource = new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", here);
const highlighterSource = new URL("../editor/highlight.goat", here);

// Lays out the pages, their compiled modules and the compiler at the relative
// paths the pages reference, so the directory can be served as-is.
export function assemble(outDir: string, pages: string[] = ["index.html"]): void {
  rmSync(outDir, { recursive: true, force: true });
  mkdirSync(outDir, { recursive: true });
  for (const page of pages) copyFileSync(new URL(page, here), `${outDir}/${page}`);
  cpSync(new URL("dist", here), `${outDir}/dist`, { recursive: true });
  copyFileSync(wasmSource, `${outDir}/goat_web.wasm`);
  copyFileSync(highlighterSource, `${outDir}/highlight.goat`);
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const args = process.argv.slice(2);
  const embed = args[0] === "--embed";
  if (embed) args.shift();
  assemble(args[0] ?? fileURLToPath(new URL("site", here)), embed ? ["embed.html"] : undefined);
}
