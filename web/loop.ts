// The host loop for interactive goat modules (ADR 0015): the browser owns the
// loop and the goat program only answers it. Each turn builds an event with the
// module's `goat_event_*` constructor, hands it to `goat_update` together with
// the model, and every animation frame `goat_draw` streams the picture through
// the scene renderer.
//
// The browser cannot preempt wasm, so a runaway `update` is stopped by the
// module's own fuel (`goat_fuel`, spent one unit per call): the host refills it
// before each call into goat, and a trap with the fuel gone is "stuck". A call
// that returns but took longer than a frame budget stops the loop too.

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

export const FUEL_BUDGET = 5_000_000;
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
}

export interface InteractiveExports extends WebAssembly.Exports {
  goat_setup(): number;
  goat_update(model: number, event: number): number;
  goat_draw(model: number): void;
  goat_release_model(model: number): void;
  goat_shutdown(): void;
  goat_fuel: WebAssembly.Global;
}

export interface Loop {
  stop(): void;
  readonly running: boolean;
}

export function isInteractiveModule(module: WebAssembly.Module): boolean {
  return WebAssembly.Module.exports(module).some((e) => e.name === "goat_setup");
}

const KEY_EVENTS = { keydown: "KeyDown", keyup: "KeyUp" } as const;
const POINTER_EVENTS = { pointermove: "PointerMove", pointerdown: "PointerDown", pointerup: "PointerUp" } as const;

export function startLoop(exports: InteractiveExports, env: LoopEnv): Loop {
  const wanted = new Set<EventKind>(subscriptions(exports));
  const fuel = exports.goat_fuel;
  const refuel = () => {
    fuel.value = FUEL_BUDGET;
  };
  const removers: Array<() => void> = [];
  let handle: number | undefined;
  let running = true;
  let healthy = true;
  let last: number | undefined;

  // One call into goat: refuel, run, and stop the loop if it traps or overruns.
  const guarded = <T>(call: () => T): T | undefined => {
    refuel();
    const started = env.now();
    try {
      const result = call();
      if (env.now() - started > FRAME_BUDGET_MS) {
        fail(STUCK_MESSAGE);
        return undefined;
      }
      return result;
    } catch (e) {
      const spent = fuel.value <= 0;
      fail(spent ? STUCK_MESSAGE : `your program stopped: ${e instanceof Error ? e.message : String(e)}`);
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
  if (first === undefined) return { stop, running: false };
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
      const rect = env.canvas.getBoundingClientRect();
      if (rect.width === 0 || rect.height === 0) return;
      const x = ((e.clientX ?? 0) - rect.left) * (env.canvas.width / rect.width);
      const y = ((e.clientY ?? 0) - rect.top) * (env.canvas.height / rect.height);
      send({ kind, x, y });
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
    get running() {
      return running;
    },
  };
}

// Instantiates an interactive module against a canvas and starts its loop.
// `memory` is only known once the module exists, so the imports read it lazily.
export async function runInteractive(
  moduleBytes: BufferSource,
  canvas: HTMLCanvasElement,
  onError: (message: string) => void,
): Promise<Loop> {
  let memory: WebAssembly.Memory | undefined;
  const scene = new CanvasScene(canvas.getContext("2d") as DrawingContext);
  const host = createHost(() => memory!);
  const { instance } = await WebAssembly.instantiate(moduleBytes, {
    goat: host.imports.goat,
    ...sceneImports(() => memory!, scene),
  });
  memory = instance.exports.memory as WebAssembly.Memory;
  return startLoop(instance.exports as InteractiveExports, {
    canvas,
    keys: canvas,
    raf: (callback) => requestAnimationFrame(callback),
    cancelRaf: (handle) => cancelAnimationFrame(handle),
    now: () => performance.now(),
    onError,
  });
}
