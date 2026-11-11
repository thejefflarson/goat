// What runs inside the goat worker (ADR 0021). The worker owns the module, the
// per-frame loop and the OffscreenCanvas, so `goat_update` and `goat_draw` stay
// synchronous exactly as ADR 0015 defines them. Input arrives by message; the
// heartbeat word tells the supervisor when goat is inside a call.

import {
  type DomEvent,
  type InteractiveExports,
  type ListenerTarget,
  type Hosted,
  type LoopCanvas,
  createHosted,
  instantiateInteractive,
  instantiateWithScene,
  isReloadableModule,
  startLoop,
} from "./loop.ts";
import { type FromWorker, Heartbeat, type ToWorker } from "./protocol.ts";
import { animate, run } from "./runtime.ts";
import { type DrawingContext, type HostEvent, SpanScene, SwatchScene, constructEvent, subscriptions } from "./scene.ts";

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

// A program over the editor vocabulary: `update` takes each input event, and
// `draw` runs once after an `Edited` one, so the spans cost one scan per edit.
interface Highlighter {
  exports: InteractiveExports;
  scene: SpanScene;
  heartbeat: Heartbeat;
  model: number;
}

export function createWorkerCore(env: WorkerCoreEnv) {
  let loop: ReturnType<typeof startLoop> | undefined;
  let highlighter: Highlighter | undefined;
  let reloadable: { ctx: DrawingContext; hosted: Hosted; heartbeat: Heartbeat } | undefined;

  const runInteractiveProgram = async (message: Extract<ToWorker, { type: "run" }>) => {
    const heartbeat = new Heartbeat(message.heartbeat);
    const { canvas } = message;
    const ctx = canvas.getContext("2d") as DrawingContext;
    const hosted = isReloadableModule(new WebAssembly.Module(message.module)) ? createHosted() : undefined;
    const exports = await instantiateInteractive(message.module, ctx, hosted);
    reloadable = hosted && { ctx, hosted, heartbeat };
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
      around: (call) => heartbeat.during(call),
    });
    if (loop.running) env.post({ type: "ready", subscriptions: subscriptions(exports) });
  };

  const runHighlighter = async (message: Extract<ToWorker, { type: "run" }>) => {
    const heartbeat = new Heartbeat(message.heartbeat);
    const scene = new SpanScene();
    const exports = await instantiateWithScene(message.module, scene);
    const model = heartbeat.during(() => exports.goat_setup());
    highlighter = { exports, scene, heartbeat, model };
    env.post({ type: "ready", subscriptions: subscriptions(exports) });
  };

  const runTheme = async (message: Extract<ToWorker, { type: "run" }>) => {
    const heartbeat = new Heartbeat(message.heartbeat);
    const scene = new SwatchScene();
    const exports = await instantiateWithScene(message.module, scene);
    heartbeat.during(() => exports.goat_draw(exports.goat_setup()));
    env.post({ type: "swatches", swatches: scene.take() });
  };

  const highlight = (session: Highlighter, event: HostEvent, ticket: number | undefined) => {
    const { exports, heartbeat, scene } = session;
    session.model = heartbeat.during(() => {
      const built = constructEvent(exports, event);
      return built === null ? session.model : exports.goat_update(session.model, built);
    });
    if (event.kind !== "Edited") return;
    heartbeat.during(() => exports.goat_draw(session.model));
    env.post({ type: "spans", ticket: ticket ?? 0, spans: scene.take() });
  };

  const reloadProgram = async (module: Uint8Array<ArrayBuffer>) => {
    if (!loop?.running || !reloadable || !isReloadableModule(new WebAssembly.Module(module))) {
      return env.post({ type: "reload_failed", message: "press Run to start this version" });
    }
    const { ctx, hosted, heartbeat } = reloadable;
    try {
      heartbeat.enter();
      let next;
      try {
        next = await instantiateInteractive(module, ctx, hosted);
      } finally {
        heartbeat.leave();
      }
      const outcome = loop.reload(next);
      if (loop.running) env.post({ type: "reloaded", outcome, subscriptions: subscriptions(next) });
    } catch (e) {
      env.post({ type: "reload_failed", message: e instanceof Error ? e.message : String(e) });
    }
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
        if (message.type === "input") {
          if (highlighter) return highlight(highlighter, message.event, message.ticket);
          return loop?.send(message.event);
        }
        if (message.type === "reload") return await reloadProgram(message.module);
        if (message.mode === "highlight") return await runHighlighter(message);
        if (message.mode === "theme") return await runTheme(message);
        await (message.mode === "interactive" ? runInteractiveProgram(message) : runOnceProgram(message));
      } catch (e) {
        env.post({ type: "failed", message: `your program stopped: ${e instanceof Error ? e.message : String(e)}` });
      }
    },
  };
}
