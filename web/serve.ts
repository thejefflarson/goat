import { readFileSync } from "node:fs";
import { createServer, type Server } from "node:http";
import { extname } from "node:path";
import { fileURLToPath } from "node:url";

const TYPES: Record<string, string> = {
  ".html": "text/html",
  ".js": "text/javascript",
  ".wasm": "application/wasm",
};

// Same-origin isolation, as web/nginx.conf sets it: the page needs it for the
// SharedArrayBuffer its worker shares with the supervisor (ADR 0021).
export const ISOLATION_HEADERS = {
  "cross-origin-opener-policy": "same-origin",
  "cross-origin-embedder-policy": "require-corp",
  "cross-origin-resource-policy": "same-origin",
};

// Serves an assembled site (`npm run bundle`) the way production does, for
// local development and for tests.
export function createSiteServer(root: string): Server {
  return createServer((req, res) => {
    try {
      const path = decodeURIComponent(new URL(req.url ?? "/", "http://x").pathname);
      const file = path.endsWith("/") ? `${path}index.html` : path;
      if (file.split("/").includes("..")) throw new Error("outside the site");
      const body = readFileSync(`${root}${file}`);
      res.writeHead(200, { "content-type": TYPES[extname(file)] ?? "application/octet-stream", ...ISOLATION_HEADERS });
      res.end(body);
    } catch {
      res.writeHead(404, ISOLATION_HEADERS).end();
    }
  });
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const root = process.argv[2] ?? fileURLToPath(new URL("site", import.meta.url));
  const port = Number(process.argv[3] ?? 8080);
  createSiteServer(root).listen(port, "127.0.0.1", () => console.log(`http://localhost:${port}/`));
}
