// What the page's supervisor and the goat worker say to each other (ADR 0021).
// Messages are plain structured-clone data; the one thing that is not a message
// is the heartbeat, a SharedArrayBuffer word the worker bumps and the supervisor
// polls, because a worker spinning inside wasm can send nothing.

import type { EventKind, HostEvent, RawSpan, RawSwatch } from "./scene.ts";

// `highlight` runs a program over the editor vocabulary: it draws once per
// `Edited` input, not once per animation frame, and has no canvas.
// `theme` runs a program over the theme vocabulary: it draws once, on start,
// and takes no input.
export type Mode = "interactive" | "once" | "highlight" | "theme";

export type ToWorker =
  | {
      type: "run";
      mode: Mode;
      module: Uint8Array<ArrayBuffer>;
      canvas: OffscreenCanvas;
      heartbeat: SharedArrayBuffer;
    }
  | { type: "input"; event: HostEvent; ticket?: number }
  | { type: "reload"; module: Uint8Array<ArrayBuffer> };

export type FromWorker =
  | { type: "ready"; subscriptions: EventKind[] }
  | { type: "reloaded"; outcome: "kept" | "reset"; subscriptions: EventKind[] }
  | { type: "reload_failed"; message: string }
  | { type: "output"; lines: string[] }
  | { type: "spans"; ticket: number; spans: RawSpan[] }
  | { type: "swatches"; swatches: RawSwatch[] }
  | { type: "finished" }
  | { type: "failed"; message: string };

// One Int32 that counts times goat was entered or left: odd while goat runs,
// even while the worker is idle. The supervisor kills a worker whose word stays
// odd and unchanged past a deadline, and never one that is merely idle (a hidden
// tab pauses animation frames, which must not look like a hang).
export class Heartbeat {
  #word: Int32Array;

  constructor(buffer: SharedArrayBuffer = new SharedArrayBuffer(4)) {
    this.#word = new Int32Array(buffer);
  }

  get buffer(): SharedArrayBuffer {
    return this.#word.buffer as SharedArrayBuffer;
  }

  enter(): void {
    Atomics.add(this.#word, 0, 1);
  }

  leave(): void {
    Atomics.add(this.#word, 0, 1);
  }

  during<T>(call: () => T): T {
    this.enter();
    try {
      return call();
    } finally {
      this.leave();
    }
  }

  read(): number {
    return Atomics.load(this.#word, 0);
  }

  static busy(value: number): boolean {
    return (value & 1) === 1;
  }
}

export interface Capabilities {
  crossOriginIsolated?: boolean;
  SharedArrayBuffer?: unknown;
  Worker?: unknown;
  OffscreenCanvas?: unknown;
}

// Why this page cannot run goat under a supervisor, or null if it can.
export function missingCapability(scope: Capabilities): string | null {
  if (!scope.crossOriginIsolated) {
    return "this page is not cross-origin isolated: serve it with Cross-Origin-Opener-Policy: same-origin and Cross-Origin-Embedder-Policy: require-corp";
  }
  if (typeof scope.SharedArrayBuffer !== "function") return "this browser has no SharedArrayBuffer";
  if (typeof scope.Worker !== "function") return "this browser cannot run Web Workers";
  if (typeof scope.OffscreenCanvas !== "function") return "this browser has no OffscreenCanvas";
  return null;
}
