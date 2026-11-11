// Wires the supervisor to the real browser: a module Worker, the page's timers,
// and a Stage for the canvas. Nothing here runs in node; the glue it connects
// (supervisor, worker core, input) is what the tests cover.

import { HIGHLIGHT_BUDGET_MS } from "./highlighter.ts";
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

// A supervisor for a highlighter (ADR 0021): the same worker and the same
// preemption, with no stage, over a 1x1 surface the worker never draws on.
// A call stuck past `HIGHLIGHT_BUDGET_MS` is terminated; the editor falls back
// to the built-in tokenizer.
export function superviseHighlighter(): Supervisor {
  return new Supervisor(
    {
      spawn: () => new Worker(new URL("./worker.js", import.meta.url), { type: "module" }) as unknown as WorkerLike,
      surface: () => new OffscreenCanvas(1, 1),
      now: () => performance.now(),
      every: (ms, tick) => {
        const handle = setInterval(tick, ms);
        return () => clearInterval(handle);
      },
    },
    globalThis,
    { frameMs: HIGHLIGHT_BUDGET_MS },
  );
}

// The page can supervise, as `superviseCanvas` would find out by throwing.
export function canSupervise(): boolean {
  return missingCapability(globalThis) === null;
}
