// Stands in for worker.ts when a test runs the worker core on a real thread:
// node's worker_threads for the browser's Worker, a recording object for the
// OffscreenCanvas. Only the transport differs from worker.ts.

import { parentPort } from "node:worker_threads";
import type { ToWorker } from "./protocol.ts";
import { createWorkerCore } from "./worker-core.ts";

const port = parentPort!;
const FRAME_MS = 5;

const core = createWorkerCore({
  post: (message) => port.postMessage(message),
  raf: (callback) => setTimeout(() => callback(performance.now()), FRAME_MS) as unknown as number,
  cancelRaf: (handle) => clearTimeout(handle),
  now: () => performance.now(),
});

const ignoring = new Proxy({} as Record<string, unknown>, {
  get: (target, key: string) => target[key] ?? (() => {}),
  set: (target, key: string, value) => ((target[key] = value), true),
});

port.on("message", (message: ToWorker) => {
  if (message.type === "run") {
    const { width, height } = message.canvas;
    message.canvas = { width, height, getContext: () => ignoring } as unknown as OffscreenCanvas;
  }
  void core.handle(message);
});
