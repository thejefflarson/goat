// Boots the engine inside a host's web view and exposes it as `window.goat`.

import { canSupervise, superviseCanvas } from "./browser.ts";
import { loadCompiler } from "./compile.ts";
import { createEngine, type Engine, type EngineMessage } from "./embed.ts";

declare global {
  interface Window {
    goat: Engine;
    webkit?: { messageHandlers: { goat: { postMessage(body: string): void } } };
  }
}

const post = (message: EngineMessage) => window.webkit?.messageHandlers.goat.postMessage(JSON.stringify(message));

try {
  const compiler = await loadCompiler(new URL("../goat_web.wasm", import.meta.url));
  const canvas = document.getElementById("canvas") as HTMLCanvasElement;
  // A host that cannot cross-origin isolate its web view keeps goat on the page's
  // own thread; one that can gets the terminable worker (ADR 0021).
  if (canSupervise()) {
    const { stage, supervisor } = superviseCanvas(canvas);
    window.goat = createEngine({ canvas, compiler, post, runner: supervisor, focus: () => stage.focus() });
  } else {
    window.goat = createEngine({ canvas, compiler, post });
  }
  post({ type: "ready" });
} catch (e) {
  post({ type: "state", state: "failed", message: e instanceof Error ? e.message : String(e) });
}
