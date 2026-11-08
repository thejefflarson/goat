// The host loop for interactive goat modules (ADR 0015): the browser owns the
// loop and the goat program only answers it. Each turn builds an event with the
// module's `goat_event_*` constructor, hands it to `goat_update` together with
// the model, and every animation frame `goat_draw` streams the picture through
// the scene renderer.
//
// The module carries no execution bound; the host owns preemption (ADR 0021).
// Inside the worker (worker-core.ts) the supervisor's wall-clock deadline stops a
// runaway call. On the main thread (a native host's web view) the host's own
// watchdog does, fed by `around`. A call that returns but took longer than a
// frame budget stops the loop too.

import { createHost } from "./runtime.ts";
import {
  CanvasScene,
  type DrawingContext,
  type EventKind,
  type HostEvent,
  constructEvent,
  sceneImports,
  subscriptions,
} from "./scene.ts";

export const FRAME_BUDGET_MS = 1000;
export const STUCK_MESSAGE = "your program got stuck: it kept running without finishing, so it was stopped";

export interface DomEvent {
  key?: string;
  clientX?: number;
  clientY?: number;
  preventDefault?(): void;
}

export interface ListenerTarget {
  addEventListener(type: string, listener: (event: DomEvent) => void): void;
  removeEventListener(type: string, listener: (event: DomEvent) => void): void;
}

export interface LoopCanvas extends ListenerTarget {
  width: number;
  height: number;
  getBoundingClientRect(): { left: number; top: number; width: number; height: number };
}

// Everything the loop takes from the page, so a test can supply its own.
export interface LoopEnv {
  canvas: LoopCanvas;
  keys: ListenerTarget;
  raf(callback: (time: number) => void): number;
  cancelRaf(handle: number): void;
  now(): number;
  onError(message: string): void;
  // Wraps every call into goat, so a host can mark when goat is running.
  around?<T>(call: () => T): T;
}

export interface InteractiveExports extends WebAssembly.Exports {
  goat_setup(): number;
  goat_update(model: number, event: number): number;
  goat_draw(model: number): void;
  goat_release_model(model: number): void;
  goat_shutdown(): void;
}

export interface Loop {
  stop(): void;
  // Delivers a host event as if the page had raised it; ignored if unsubscribed.
  send(event: HostEvent): void;
  readonly running: boolean;
}

export function isInteractiveModule(module: WebAssembly.Module): boolean {
  return WebAssembly.Module.exports(module).some((e) => e.name === "goat_setup");
}

export const KEY_EVENTS = { keydown: "KeyDown", keyup: "KeyUp" } as const;
export const POINTER_EVENTS = {
  pointermove: "PointerMove",
  pointerdown: "PointerDown",
  pointerup: "PointerUp",
} as const;

// A pointer event in the canvas's own pixel space, or null while it has no size.
export function pointerPosition(
  canvas: Pick<LoopCanvas, "width" | "height" | "getBoundingClientRect">,
  e: DomEvent,
): { x: number; y: number } | null {
  const rect = canvas.getBoundingClientRect();
  if (rect.width === 0 || rect.height === 0) return null;
  return {
    x: ((e.clientX ?? 0) - rect.left) * (canvas.width / rect.width),
    y: ((e.clientY ?? 0) - rect.top) * (canvas.height / rect.height),
  };
}

export function startLoop(exports: InteractiveExports, env: LoopEnv): Loop {
  const wanted = new Set<EventKind>(subscriptions(exports));
  const removers: Array<() => void> = [];
  let handle: number | undefined;
  let running = true;
  let healthy = true;
  let last: number | undefined;

  // One call into goat: run it, and stop the loop if it traps or overruns.
  const guarded = <T>(call: () => T): T | undefined => {
    const started = env.now();
    try {
      const result = env.around ? env.around(call) : call();
      if (env.now() - started > FRAME_BUDGET_MS) {
        fail(STUCK_MESSAGE);
        return undefined;
      }
      return result;
    } catch (e) {
      fail(`your program stopped: ${e instanceof Error ? e.message : String(e)}`);
      return undefined;
    }
  };

  const fail = (message: string) => {
    healthy = false;
    stop();
    env.onError(message);
  };

  const stop = () => {
    if (!running) return;
    running = false;
    if (handle !== undefined) env.cancelRaf(handle);
    removers.forEach((remove) => remove());
    if (healthy) {
      exports.goat_release_model(model);
      exports.goat_shutdown();
    }
  };

  let model = 0;
  const first = guarded(() => exports.goat_setup());
  if (first === undefined) return { stop, send: () => {}, running: false };
  model = first;

  const send = (event: HostEvent) => {
    if (!running || !wanted.has(event.kind)) return;
    const next = guarded(() => {
      const built = constructEvent(exports, event);
      return built === null ? model : exports.goat_update(model, built);
    });
    if (next !== undefined) model = next;
  };

  const listen = (target: ListenerTarget, type: string, listener: (event: DomEvent) => void) => {
    target.addEventListener(type, listener);
    removers.push(() => target.removeEventListener(type, listener));
  };

  for (const [type, kind] of Object.entries(KEY_EVENTS)) {
    if (!wanted.has(kind)) continue;
    listen(env.keys, type, (e) => {
      if (typeof e.key !== "string") return;
      e.preventDefault?.();
      send({ kind, key: e.key });
    });
  }
  for (const [type, kind] of Object.entries(POINTER_EVENTS)) {
    if (!wanted.has(kind)) continue;
    listen(env.canvas, type, (e) => {
      const at = pointerPosition(env.canvas, e);
      if (at) send({ kind, ...at });
    });
  }

  const frame = (time: number) => {
    if (!running) return;
    if (wanted.has("Tick")) {
      send({ kind: "Tick", dt: last === undefined ? 0 : time - last });
    }
    last = time;
    if (running) guarded(() => exports.goat_draw(model));
    if (running) handle = env.raf(frame);
  };
  handle = env.raf(frame);

  return {
    stop,
    send,
    get running() {
      return running;
    },
  };
}

// Instantiates an interactive module drawing through `ctx`. `memory` is only
// known once the module exists, so the imports read it lazily.
export async function instantiateInteractive(
  moduleBytes: BufferSource,
  ctx: DrawingContext,
): Promise<InteractiveExports> {
  let memory: WebAssembly.Memory | undefined;
  const scene = new CanvasScene(ctx);
  const host = createHost(() => memory!);
  const { instance } = await WebAssembly.instantiate(moduleBytes, {
    goat: host.imports.goat,
    ...sceneImports(() => memory!, scene),
  });
  memory = instance.exports.memory as WebAssembly.Memory;
  return instance.exports as InteractiveExports;
}

// Instantiates an interactive module against a canvas and starts its loop.
export async function runInteractive(
  moduleBytes: BufferSource,
  canvas: HTMLCanvasElement,
  onError: (message: string) => void,
  around?: LoopEnv["around"],
): Promise<Loop> {
  const exports = await instantiateInteractive(moduleBytes, canvas.getContext("2d") as DrawingContext);
  return startLoop(exports, {
    canvas,
    keys: canvas,
    raf: (callback) => requestAnimationFrame(callback),
    cancelRaf: (handle) => cancelAnimationFrame(handle),
    now: () => performance.now(),
    onError,
    around,
  });
}
