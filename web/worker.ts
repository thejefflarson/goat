// The Web Worker entry point: the page's supervisor spawns this module and may
// terminate it at any time. All behavior lives in worker-core.ts.

import type { FromWorker, ToWorker } from "./protocol.ts";
import { createWorkerCore } from "./worker-core.ts";

interface WorkerScope {
  postMessage(message: FromWorker): void;
  onmessage: ((event: { data: ToWorker }) => void) | null;
  requestAnimationFrame?(callback: (time: number) => void): number;
  cancelAnimationFrame?(handle: number): void;
}

const scope = globalThis as unknown as WorkerScope;
const FRAME_MS = 16;

// Dedicated workers have requestAnimationFrame where the browser supports it
// for OffscreenCanvas; a timer stands in elsewhere.
const core = createWorkerCore({
  post: (message) => scope.postMessage(message),
  raf: (callback) =>
    scope.requestAnimationFrame
      ? scope.requestAnimationFrame(callback)
      : (setTimeout(() => callback(performance.now()), FRAME_MS) as unknown as number),
  cancelRaf: (handle) =>
    scope.cancelAnimationFrame ? scope.cancelAnimationFrame(handle) : clearTimeout(handle),
  now: () => performance.now(),
});

scope.onmessage = (event) => void core.handle(event.data);
