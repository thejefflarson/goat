import { fileURLToPath } from "node:url";
import { build } from "esbuild";

// The page loads modules straight from dist/ without a bundler, but CodeMirror
// is imported by package name, so the editor is bundled into one file.
await build({
  entryPoints: [fileURLToPath(new URL("editor.ts", import.meta.url))],
  outfile: fileURLToPath(new URL("dist/editor.bundle.js", import.meta.url)),
  bundle: true,
  format: "esm",
  target: "es2022",
  minify: true,
  legalComments: "none",
  logLevel: "warning",
});
