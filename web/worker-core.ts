// What runs inside the goat worker (ADR 0021). The worker owns the module, the
// per-frame loop and the OffscreenCanvas, so `goat_update` and `goat_draw` stay
// synchronous exactly as ADR 0015 defines them. Input arrives by message; the
// heartbeat word tells the supervisor when goat is inside a call.

import {
  type DomEvent,
  type ListenerTarget,
  type LoopCanvas,
  instantiateInteractive,
  startLoop,
} from "./loop.ts";
import { type FromWorker, Heartbeat, type ToWorker } from "./protocol.ts";
import { animate, run } from "./runtime.ts";
import { type DrawingContext, subscriptions } from "./scene.ts";

// i32::MAX: the fuel tank is topped to its maximum before each call, so it never
// runs out before the supervisor's deadline does.
const FUEL_TANK = 2 ** 31 - 1;

export interface WorkerCoreEnv {
  post(message: FromWorker): void;
  raf(callback: (time: number) => void): number;
  cancelRaf(handle: number): void;
  now(): number;
}

// Input comes from the page as host events, so the loop has no listeners to wire.
const NO_LISTENERS: ListenerTarget = {
  addEventListener(_type: string, _listener: (event: DomEvent) => void) {},
  removeEventListener(_type: string, _listener: (event: DomEvent) => void) {},
};

export function createWorkerCore(env: WorkerCoreEnv) {
  let loop: ReturnType<typeof startLoop> | undefined;

  const runInteractiveProgram = async (message: Extract<ToWorker, { type: "run" }>) => {
    const heartbeat = new Heartbeat(message.heartbeat);
    const { canvas } = message;
    const exports = await instantiateInteractive(message.module, canvas.getContext("2d") as DrawingContext);
    const surface: LoopCanvas = {
      ...NO_LISTENERS,
      width: canvas.width,
      height: canvas.height,
      getBoundingClientRect: () => ({ left: 0, top: 0, width: canvas.width, height: canvas.height }),
    };
    loop = startLoop(exports, {
      canvas: surface,
      keys: NO_LISTENERS,
      raf: env.raf,
      cancelRaf: env.cancelRaf,
      now: env.now,
      onError: (failure) => env.post({ type: "failed", message: failure }),
      fuelBudget: FUEL_TANK,
      around: (call) => heartbeat.during(call),
    });
    if (loop.running) env.post({ type: "ready", subscriptions: subscriptions(exports) });
  };

  const runOnceProgram = async (message: Extract<ToWorker, { type: "run" }>) => {
    const heartbeat = new Heartbeat(message.heartbeat);
    heartbeat.enter();
    let result;
    try {
      result = await run(message.module);
    } finally {
      heartbeat.leave();
    }
    env.post({ type: "output", lines: result.output });
    await animate(message.canvas, result.commands, { raf: (frame) => void env.raf(frame) });
    env.post({ type: "finished" });
  };

  return {
    async handle(message: ToWorker): Promise<void> {
      try {
        if (message.type === "input") return loop?.send(message.event);
        await (message.mode === "interactive" ? runInteractiveProgram(message) : runOnceProgram(message));
      } catch (e) {
        env.post({ type: "failed", message: `your program stopped: ${e instanceof Error ? e.message : String(e)}` });
      }
    },
  };
}
