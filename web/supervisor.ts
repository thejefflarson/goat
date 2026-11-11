// The main-thread half of host-owned preemption (ADR 0021): goat runs in a Web
// Worker, and the supervisor holds a wall-clock deadline over it. It polls the
// worker's heartbeat (Atomics.wait is forbidden on the main thread, and a spinning
// worker cannot send a message), and when goat has been inside one call past the
// deadline it calls `terminate()` and, for an interactive program, starts over
// from `init`. The page never blocks, so it can always do this.

import { FRAME_BUDGET_MS, STUCK_MESSAGE } from "./loop.ts";
import {
  type Capabilities,
  type FromWorker,
  Heartbeat,
  type Mode,
  type ToWorker,
  missingCapability,
} from "./protocol.ts";
import type { EventKind, HostEvent, RawSpan } from "./scene.ts";

export const RUN_ONCE_BUDGET_MS = 10_000;
export const POLL_MS = 100;
export const MAX_RESTARTS = 3;
export const RUN_ONCE_STOPPED_MESSAGE =
  "your program was stopped: it ran too long without finishing";

export interface WorkerLike {
  postMessage(message: ToWorker, transfer?: Transferable[]): void;
  terminate(): void;
  onmessage: ((event: { data: FromWorker }) => void) | null;
  onerror: ((event: { message?: string }) => void) | null;
}

export interface SupervisorEnv {
  spawn(): WorkerLike;
  // A blank canvas the worker may own; each call replaces the page's canvas.
  surface(): OffscreenCanvas;
  now(): number;
  // Calls `tick` every `ms` until the returned function is called.
  every(ms: number, tick: () => void): () => void;
}

export interface Job {
  mode: Mode;
  module: Uint8Array<ArrayBuffer>;
}

export interface RunSink {
  // An interactive program finished `setup`, on the first start and after each restart.
  onReady?(): void;
  // A recompiled program replaced the running one: `kept` its state, or started over.
  onReloaded?(outcome: "kept" | "reset"): void;
  // The recompiled program could not replace the running one, which keeps running.
  onReloadFailed?(message: string): void;
  onOutput(lines: string[]): void;
  // A `highlight` program drew spans for the input sent with `ticket`. The
  // spans are the program's own words, to be validated before use.
  onSpans?(ticket: number, spans: RawSpan[]): void;
  onFinished?(): void;
  // A trap, a worker error, or a stuck program the supervisor stopped.
  onFailed(message: string): void;
}

export interface Limits {
  frameMs: number;
  onceMs: number;
  pollMs: number;
}

export interface Runner {
  start(job: Job, sink: RunSink): void;
  stop(): void;
}

interface Session {
  job: Job;
  sink: RunSink;
  worker: WorkerLike;
  heartbeat: Heartbeat;
  stopTimer: () => void;
  lastSeen: number;
  since: number;
  ready: boolean;
  subscriptions: ReadonlySet<EventKind>;
  restarts: number;
  pending: Array<Job["module"]>;
}

export class Supervisor implements Runner {
  #env: SupervisorEnv;
  #limits: Limits;
  #session: Session | undefined;

  // Throws if the page cannot give a worker a SharedArrayBuffer heartbeat.
  constructor(env: SupervisorEnv, scope: Capabilities, limits: Partial<Limits> = {}) {
    const missing = missingCapability(scope);
    if (missing !== null) throw new Error(`goat cannot run safely here: ${missing}`);
    this.#env = env;
    this.#limits = { frameMs: FRAME_BUDGET_MS, onceMs: RUN_ONCE_BUDGET_MS, pollMs: POLL_MS, ...limits };
  }

  start(job: Job, sink: RunSink): void {
    this.stop();
    this.#launch(job, sink, 0);
  }

  stop(): void {
    const session = this.#session;
    if (!session) return;
    this.#session = undefined;
    session.stopTimer();
    session.worker.terminate();
  }

  // Whether the running program subscribed to `kind`; the page asks before it
  // swallows a key press.
  wants(kind: EventKind): boolean {
    return this.#session?.subscriptions.has(kind) ?? false;
  }

  // Hands a recompiled module to the running interactive program; false if
  // nothing is ready to take it. A restart after a stuck call uses the newest
  // module that took.
  reload(module: Job["module"]): boolean {
    const session = this.#session;
    if (!session?.ready || session.job.mode !== "interactive") return false;
    session.pending.push(module);
    session.worker.postMessage({ type: "reload", module });
    return true;
  }

  // Delivers a host event to the running program; a `highlight` program's
  // answer comes back through `onSpans` with the same `ticket`.
  input(event: HostEvent, ticket?: number): void {
    const session = this.#session;
    if (session?.ready && session.subscriptions.has(event.kind)) {
      session.worker.postMessage({ type: "input", event, ticket });
    }
  }

  #launch(job: Job, sink: RunSink, restarts: number): void {
    const worker = this.#env.spawn();
    const heartbeat = new Heartbeat();
    const session: Session = {
      job,
      sink,
      worker,
      heartbeat,
      stopTimer: this.#env.every(this.#limits.pollMs, () => this.#check(session)),
      lastSeen: heartbeat.read(),
      since: this.#env.now(),
      ready: false,
      subscriptions: new Set(),
      restarts,
      pending: [],
    };
    this.#session = session;
    worker.onmessage = (event) => this.#receive(session, event.data);
    worker.onerror = (event) => this.#fail(session, `your program stopped: ${event.message ?? "the worker failed"}`);
    const canvas = this.#env.surface();
    worker.postMessage(
      { type: "run", mode: job.mode, module: job.module, canvas, heartbeat: heartbeat.buffer },
      [canvas],
    );
  }

  #receive(session: Session, message: FromWorker): void {
    if (this.#session !== session) return;
    switch (message.type) {
      case "ready":
        session.ready = true;
        session.subscriptions = new Set(message.subscriptions);
        session.sink.onReady?.();
        break;
      case "reloaded":
        session.subscriptions = new Set(message.subscriptions);
        session.job = { ...session.job, module: session.pending.shift() ?? session.job.module };
        session.sink.onReloaded?.(message.outcome);
        break;
      case "reload_failed":
        session.pending.shift();
        session.sink.onReloadFailed?.(message.message);
        break;
      case "output":
        session.sink.onOutput(message.lines);
        break;
      case "spans":
        session.sink.onSpans?.(message.ticket, message.spans);
        break;
      case "finished":
        session.sink.onFinished?.();
        break;
      case "failed":
        this.#fail(session, message.message);
        break;
    }
  }

  #fail(session: Session, message: string): void {
    if (this.#session !== session) return;
    session.sink.onFailed(message);
  }

  #check(session: Session): void {
    if (this.#session !== session) return;
    const value = session.heartbeat.read();
    const now = this.#env.now();
    if (value !== session.lastSeen) {
      session.lastSeen = value;
      session.since = now;
      return;
    }
    const deadline = session.job.mode === "once" ? this.#limits.onceMs : this.#limits.frameMs;
    if (Heartbeat.busy(value) && now - session.since >= deadline) this.#kill(session);
  }

  // An interactive program that got past `setup` starts over from `init`; one
  // that never did, or keeps getting stuck, stays stopped so a restart cannot loop.
  #kill(session: Session): void {
    this.stop();
    const { job, sink } = session;
    if (job.mode === "once") return sink.onFailed(RUN_ONCE_STOPPED_MESSAGE);
    sink.onFailed(STUCK_MESSAGE);
    if (session.ready && session.restarts < MAX_RESTARTS) this.#launch(job, sink, session.restarts + 1);
  }
}
