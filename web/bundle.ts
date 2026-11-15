import { createHash } from "node:crypto";
import { copyFileSync, cpSync, mkdirSync, readFileSync, readdirSync, renameSync, rmSync, writeFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

const here = new URL(".", import.meta.url);
const wasmSource = new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", here);
const highlighterSource = new URL("../editor/highlight.goat", here);
const themeSource = new URL("../editor/theme.goat", here);

export const BUILD_PLACEHOLDER = "__BUILD__";

function contentHash(dir: string): string {
  const hash = createHash("sha256");
  const files = (readdirSync(dir, { recursive: true }) as string[]).filter((f) => f.includes(".")).sort();
  for (const file of files) hash.update(file).update(readFileSync(`${dir}/${file}`));
  return hash.digest("hex").slice(0, 12);
}

// Lays out the pages, their compiled modules and the compiler at the relative
// paths the pages reference, so the directory can be served as-is. The editor
// page keeps its modules, wasm and goat sources in `v/<content hash>/`, so the
// files of one build can never be mixed with another's by a cache. The embed
// page is staged into a host's bundle, never cached by a CDN, and stays flat.
export function assemble(outDir: string, pages: string[] = ["index.html"], versioned = pages.includes("index.html")): string {
  rmSync(outDir, { recursive: true, force: true });
  mkdirSync(outDir, { recursive: true });
  const assetDir = versioned ? `${outDir}/v/staging` : outDir;
  mkdirSync(assetDir, { recursive: true });
  cpSync(new URL("dist", here), `${assetDir}/dist`, { recursive: true });
  copyFileSync(wasmSource, `${assetDir}/goat_web.wasm`);
  copyFileSync(highlighterSource, `${assetDir}/highlight.goat`);
  copyFileSync(themeSource, `${assetDir}/theme.goat`);
  let build = "";
  if (versioned) {
    build = contentHash(assetDir);
    renameSync(assetDir, `${outDir}/v/${build}`);
  }
  for (const page of pages) {
    const html = readFileSync(new URL(page, here), "utf8").replaceAll(BUILD_PLACEHOLDER, build);
    writeFileSync(`${outDir}/${page}`, html);
  }
  return build;
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const args = process.argv.slice(2);
  const embed = args[0] === "--embed";
  if (embed) args.shift();
  assemble(args[0] ?? fileURLToPath(new URL("site", here)), embed ? ["embed.html"] : undefined);
}
