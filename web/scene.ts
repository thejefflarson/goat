// Picture and event plumbing for interactive goat modules (ADR 0015), the
// browser half of mir/src/host.rs (`SceneHost`) and cli/src/lib.rs (`Guest`).
//
//   imports  scene.{begin,end,line,polyline_begin,vertex,polyline_end}
//   exports  goat_setup, goat_update, goat_draw, goat_release_model,
//            goat_shutdown, goat_alloc, goat_event_<Tag> per handled event
//
// The exported `goat_event_*` constructors are the subscription: a host listens
// for exactly the events the module can build. The requestAnimationFrame loop
// that drives them is separate; this file is what each turn of it calls.

import { COLOR_PATTERN, readString } from "./runtime.ts";

const STR_LEN = 8;
const STR_BYTES = 12;

export type SceneCommand =
  | { kind: "begin" | "end" | "polyline_end" }
  | { kind: "line"; x1: number; y1: number; x2: number; y2: number; color: string }
  | { kind: "polyline_begin"; color: string }
  | { kind: "vertex"; x: number; y: number };

// What a renderer implements; `sceneImports` validates and forwards to it.
export interface Scene {
  begin(): void;
  line(x1: number, y1: number, x2: number, y2: number, color: string): void;
  polylineBegin(color: string): void;
  vertex(x: number, y: number): void;
  polylineEnd(): void;
  end(): void;
}

export interface SceneImports {
  scene: {
    begin(): void;
    end(): void;
    line(x1: number, y1: number, x2: number, y2: number, color: number): void;
    polyline_begin(color: number): void;
    vertex(x: number, y: number): void;
    polyline_end(): void;
  };
}

function finite(name: string, x: number): number {
  if (!Number.isFinite(x)) throw new Error(`${name} needs a real number, not ${x}`);
  return x;
}

// The scene.* imports over `scene`. A color outside ADR 0014's allowlist and a
// non-finite coordinate throw, which traps the program like turtle.color does.
export function sceneImports(memory: () => WebAssembly.Memory, scene: Scene): SceneImports {
  const color = (ptr: number) => {
    const value = readString(memory(), ptr);
    if (!COLOR_PATTERN.test(value)) {
      throw new Error(`color wants a name like "red" or a code like "#ff8800", not ${JSON.stringify(value)}`);
    }
    return value;
  };
  return {
    scene: {
      begin: () => scene.begin(),
      end: () => scene.end(),
      line: (x1, y1, x2, y2, ptr) =>
        scene.line(finite("line", x1), finite("line", y1), finite("line", x2), finite("line", y2), color(ptr)),
      polyline_begin: (ptr) => scene.polylineBegin(color(ptr)),
      vertex: (x, y) => scene.vertex(finite("vertex", x), finite("vertex", y)),
      polyline_end: () => scene.polylineEnd(),
    },
  };
}

// A scene that only remembers what it was told, for tests and for hosts that
// render later.
export class RecordingScene implements Scene {
  commands: SceneCommand[] = [];
  begin() {
    this.commands.push({ kind: "begin" });
  }
  line(x1: number, y1: number, x2: number, y2: number, color: string) {
    this.commands.push({ kind: "line", x1, y1, x2, y2, color });
  }
  polylineBegin(color: string) {
    this.commands.push({ kind: "polyline_begin", color });
  }
  vertex(x: number, y: number) {
    this.commands.push({ kind: "vertex", x, y });
  }
  polylineEnd() {
    this.commands.push({ kind: "polyline_end" });
  }
  end() {
    this.commands.push({ kind: "end" });
  }
}

export type DrawingContext = Pick<
  CanvasRenderingContext2D,
  | "canvas"
  | "strokeStyle"
  | "lineWidth"
  | "lineCap"
  | "lineJoin"
  | "save"
  | "restore"
  | "clearRect"
  | "beginPath"
  | "moveTo"
  | "lineTo"
  | "stroke"
>;

// Draws each frame in canvas coordinates, origin top left with y down, as
// shapes are specified. `begin` clears and `end` restores the context state
// `begin` saved, so a frame leaves the context as it found it.
export class CanvasScene implements Scene {
  #ctx: DrawingContext;
  #started = false;

  constructor(ctx: DrawingContext) {
    this.#ctx = ctx;
  }

  begin() {
    const ctx = this.#ctx;
    ctx.save();
    ctx.clearRect(0, 0, ctx.canvas.width, ctx.canvas.height);
    ctx.lineWidth = 1;
    ctx.lineCap = "round";
    ctx.lineJoin = "round";
  }

  line(x1: number, y1: number, x2: number, y2: number, color: string) {
    const ctx = this.#ctx;
    ctx.strokeStyle = color;
    ctx.beginPath();
    ctx.moveTo(x1, y1);
    ctx.lineTo(x2, y2);
    ctx.stroke();
  }

  polylineBegin(color: string) {
    this.#ctx.strokeStyle = color;
    this.#ctx.beginPath();
    this.#started = false;
  }

  vertex(x: number, y: number) {
    if (this.#started) this.#ctx.lineTo(x, y);
    else this.#ctx.moveTo(x, y);
    this.#started = true;
  }

  polylineEnd() {
    this.#ctx.stroke();
  }

  end() {
    this.#ctx.restore();
  }
}

export type HostEvent =
  | { kind: "Tick"; dt: number }
  | { kind: "KeyDown" | "KeyUp"; key: string }
  | { kind: "PointerMove" | "PointerDown" | "PointerUp"; x: number; y: number };

export type EventKind = HostEvent["kind"];

const EVENT_PREFIX = "goat_event_";
const EVENT_KINDS: readonly EventKind[] = ["Tick", "KeyDown", "KeyUp", "PointerMove", "PointerDown", "PointerUp"];

// The events the module handles: one per `goat_event_*` export.
export function subscriptions(exports: WebAssembly.Exports): EventKind[] {
  return EVENT_KINDS.filter((kind) => typeof exports[EVENT_PREFIX + kind] === "function");
}

function memoryOf(exports: WebAssembly.Exports): WebAssembly.Memory {
  const memory = exports.memory;
  if (!(memory instanceof WebAssembly.Memory)) throw new Error("module exports no memory");
  return memory;
}

// A goat string with count 1, which an event constructor takes ownership of.
export function newString(exports: WebAssembly.Exports, text: string): number {
  const bytes = new TextEncoder().encode(text);
  const alloc = exports.goat_alloc as (size: number) => number;
  const ptr = alloc(STR_BYTES + bytes.length);
  const memory = memoryOf(exports).buffer;
  new DataView(memory).setUint32(ptr + STR_LEN, bytes.length, true);
  new Uint8Array(memory).set(bytes, ptr + STR_BYTES);
  return ptr;
}

// Build `event` with the module's own constructor and hand back the owned
// pointer `goat_update` consumes, or null if the module does not handle it.
export function constructEvent(exports: WebAssembly.Exports, event: HostEvent): number | null {
  const make = exports[EVENT_PREFIX + event.kind];
  if (typeof make !== "function") return null;
  switch (event.kind) {
    case "Tick":
      return make(event.dt);
    case "KeyDown":
    case "KeyUp":
      return make(newString(exports, event.key));
    default:
      return make(event.x, event.y);
  }
}
