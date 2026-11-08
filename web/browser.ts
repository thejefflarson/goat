// Wires the supervisor to the real browser: a module Worker, the page's timers,
// and a Stage for the canvas. Nothing here runs in node; the glue it connects
// (supervisor, worker core, input) is what the tests cover.

import { forwardInput } from "./input.ts";
import { missingCapability } from "./protocol.ts";
import { Stage } from "./stage.ts";
import { Supervisor, type WorkerLike } from "./supervisor.ts";

export interface SupervisedPage {
  stage: Stage;
  supervisor: Supervisor;
}

// Throws, with the reason, if the page is not cross-origin isolated or lacks
// Worker, SharedArrayBuffer or OffscreenCanvas.
export function superviseCanvas(canvas: HTMLCanvasElement): SupervisedPage {
  const stage = new Stage(canvas);
  const supervisor = new Supervisor(
    {
      spawn: () => new Worker(new URL("./worker.js", import.meta.url), { type: "module" }) as unknown as WorkerLike,
      surface: () => stage.surface(),
      now: () => performance.now(),
      every: (ms, tick) => {
        const handle = setInterval(tick, ms);
        return () => clearInterval(handle);
      },
    },
    globalThis,
  );
  forwardInput(stage.container, () => stage.canvas, supervisor);
  return { stage, supervisor };
}

// The page can supervise, as `superviseCanvas` would find out by throwing.
export function canSupervise(): boolean {
  return missingCapability(globalThis) === null;
}
