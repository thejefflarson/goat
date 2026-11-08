// Boots the engine inside a host's web view and exposes it as `window.goat`.

import { canSupervise, superviseCanvas } from "./browser.ts";
import { loadCompiler } from "./compile.ts";
import { createEngine, type Engine, type EngineMessage, UNPROTECTED_MESSAGE } from "./embed.ts";

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
  // Goat carries no execution bound, so every path needs a stop it does not own
  // (ADR 0021): the terminable worker when the page is cross-origin isolated, else
  // the native watchdog of the host that registered the `goat` message handler.
  // With neither, the engine refuses to run.
  if (canSupervise()) {
    const { stage, supervisor } = superviseCanvas(canvas);
    window.goat = createEngine({ canvas, compiler, post, runner: supervisor, focus: () => stage.focus() });
  } else {
    const watched = window.webkit?.messageHandlers.goat !== undefined;
    if (!watched) document.body.textContent = UNPROTECTED_MESSAGE;
    window.goat = createEngine({ canvas, compiler, post, heartbeat: watched });
  }
  post({ type: "ready" });
} catch (e) {
  post({ type: "state", state: "failed", message: e instanceof Error ? e.message : String(e) });
}
