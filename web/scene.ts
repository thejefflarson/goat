// Picture and event plumbing for interactive goat modules (ADR 0015), the
// browser half of mir/src/host.rs (`SceneHost`) and cli/src/lib.rs (`Guest`).
//
//   imports  scene.{begin,end,frame}, and the per-shape calls (line, polyline_begin,
//            vertex, polyline_end, circle, rect, text, span, edit, swatch) a
//            frame replays; see frame.ts
//   exports  goat_setup, goat_update, goat_draw, goat_release_model,
//            goat_shutdown, goat_alloc, goat_event_<Tag> per handled event
//
// The exported `goat_event_*` constructors are the subscription: a host listens
// for exactly the events the module can build. The requestAnimationFrame loop
// that drives them is separate; this file is what each turn of it calls.

import { FrameDecoder, type FrameHandler, type FrameValue } from "./frame.ts";
import { checkColor, readString } from "./runtime.ts";

const STR_LEN = 8;
const STR_BYTES = 12;
const TEXT_FONT = "16px sans-serif";

export type SceneCommand =
  | { kind: "begin" | "end" | "polyline_end" }
  | { kind: "line"; x1: number; y1: number; x2: number; y2: number; color: string }
  | { kind: "polyline_begin"; color: string }
  | { kind: "vertex"; x: number; y: number }
  | { kind: "circle"; x: number; y: number; r: number; color: string }
  | { kind: "rect"; x: number; y: number; w: number; h: number; color: string }
  | { kind: "text"; x: number; y: number; text: string; color: string }
  | { kind: "span"; from: number; to: number; role: string }
  | { kind: "edit"; from: number; to: number; newlines: number; indent: number }
  | { kind: "swatch"; role: string; light: string; dark: string };

// A style span the editor vocabulary draws: byte offsets into the edited text
// and a role name the goat program chose, which the page must not trust.
export interface RawSpan {
  from: number;
  to: number;
  kind: string;
}

// A whitespace edit the editor vocabulary draws: replace the bytes `from` to
// `to` of the edited text with `newlines` line breaks and then `indent` spaces.
// The numbers are the goat program's words, which the page must not trust.
export interface RawEdit {
  from: number;
  to: number;
  newlines: number;
  indent: number;
}

// The colors a theme gives one style role, on a light page and a dark one. They
// are the goat program's words, which the page must not trust.
export interface RawSwatch {
  role: string;
  light: string;
  dark: string;
}

// What a renderer implements; `sceneImports` validates and forwards to it.
export interface Scene {
  begin(): void;
  line(x1: number, y1: number, x2: number, y2: number, color: string): void;
  polylineBegin(color: string): void;
  vertex(x: number, y: number): void;
  polylineEnd(): void;
  circle(x: number, y: number, r: number, color: string): void;
  rect(x: number, y: number, w: number, h: number, color: string): void;
  text(x: number, y: number, text: string, color: string): void;
  span(from: number, to: number, role: string): void;
  edit(from: number, to: number, newlines: number, indent: number): void;
  swatch(role: string, light: string, dark: string): void;
  end(): void;
}

export interface SceneImports {
  scene: {
    begin(): void;
    end(): void;
    frame(ptr: number, len: number): void;
    line(x1: number, y1: number, x2: number, y2: number, color: number): void;
    polyline_begin(color: number): void;
    vertex(x: number, y: number): void;
    polyline_end(): void;
    circle(x: number, y: number, r: number, color: number): void;
    rect(x: number, y: number, w: number, h: number, color: number): void;
    text(x: number, y: number, text: number, color: number): void;
    span(from: bigint, to: bigint, role: number): void;
    edit(from: bigint, to: bigint, newlines: bigint, indent: bigint): void;
    swatch(role: number, light: number, dark: number): void;
  };
}

function finite(name: string, x: number): number {
  if (!Number.isFinite(x)) throw new Error(`${name} needs a real number, not ${x}`);
  return x;
}

// The scene calls a frame replays, over decoded values. A color outside ADR
// 0014's allowlist and a non-finite coordinate throw, which traps the program
// like turtle.color does.
function sceneCalls(scene: Scene): Record<string, FrameHandler> {
  const num = (name: string, a: FrameValue[], at: number) => finite(name, a[at] as number);
  return {
    begin: () => scene.begin(),
    end: () => scene.end(),
    line: (a) =>
      scene.line(num("line", a, 0), num("line", a, 1), num("line", a, 2), num("line", a, 3), checkColor(a[4] as string)),
    polyline_begin: (a) => scene.polylineBegin(checkColor(a[0] as string)),
    vertex: (a) => scene.vertex(num("vertex", a, 0), num("vertex", a, 1)),
    polyline_end: () => scene.polylineEnd(),
    circle: (a) => scene.circle(num("circle", a, 0), num("circle", a, 1), num("circle", a, 2), checkColor(a[3] as string)),
    rect: (a) =>
      scene.rect(num("rect", a, 0), num("rect", a, 1), num("rect", a, 2), num("rect", a, 3), checkColor(a[4] as string)),
    text: (a) => scene.text(num("text", a, 0), num("text", a, 1), a[2] as string, checkColor(a[3] as string)),
    span: (a) => scene.span(a[0] as number, a[1] as number, a[2] as string),
    edit: (a) => scene.edit(a[0] as number, a[1] as number, a[2] as number, a[3] as number),
    swatch: (a) => scene.swatch(a[0] as string, a[1] as string, a[2] as string),
  };
}

// The scene.* imports over `scene`. `frame` replays a frame's bytes, which the
// module wrote into its own memory, as the per-shape calls it encodes; the
// per-shape imports stay for modules that make those calls themselves.
export function sceneImports(memory: () => WebAssembly.Memory, scene: Scene): SceneImports {
  const calls = sceneCalls(scene);
  const decoder = new FrameDecoder((name) => calls[name]);
  const str = (ptr: number) => readString(memory(), ptr);
  return {
    scene: {
      begin: () => scene.begin(),
      end: () => scene.end(),
      frame: (ptr, len) => {
        const data = memory().buffer;
        const start = ptr >>> 0;
        const length = len >>> 0;
        if (start + length > data.byteLength) throw new Error("frame out of bounds");
        decoder.replay(new Uint8Array(data, start, length));
      },
      line: (x1, y1, x2, y2, ptr) => calls.line!([x1, y1, x2, y2, str(ptr)]),
      polyline_begin: (ptr) => calls.polyline_begin!([str(ptr)]),
      vertex: (x, y) => calls.vertex!([x, y]),
      polyline_end: () => scene.polylineEnd(),
      circle: (x, y, r, ptr) => calls.circle!([x, y, r, str(ptr)]),
      rect: (x, y, w, h, ptr) => calls.rect!([x, y, w, h, str(ptr)]),
      text: (x, y, textPtr, ptr) => calls.text!([x, y, str(textPtr), str(ptr)]),
      span: (from, to, ptr) => calls.span!([Number(from), Number(to), str(ptr)]),
      edit: (from, to, newlines, indent) => calls.edit!([Number(from), Number(to), Number(newlines), Number(indent)]),
      swatch: (role, light, dark) => calls.swatch!([str(role), str(light), str(dark)]),
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
  circle(x: number, y: number, r: number, color: string) {
    this.commands.push({ kind: "circle", x, y, r, color });
  }
  rect(x: number, y: number, w: number, h: number, color: string) {
    this.commands.push({ kind: "rect", x, y, w, h, color });
  }
  text(x: number, y: number, text: string, color: string) {
    this.commands.push({ kind: "text", x, y, text, color });
  }
  span(from: number, to: number, role: string) {
    this.commands.push({ kind: "span", from, to, role });
  }
  edit(from: number, to: number, newlines: number, indent: number) {
    this.commands.push({ kind: "edit", from, to, newlines, indent });
  }
  swatch(role: string, light: string, dark: string) {
    this.commands.push({ kind: "swatch", role, light, dark });
  }
  end() {
    this.commands.push({ kind: "end" });
  }
}

export const MAX_SPANS = 1_000_000;

// The spans and edits of the frame being drawn, for the editor host: `begin`
// starts a frame over, and nothing else is drawn. More than `MAX_SPANS` spans
// or edits in one frame traps the program instead of growing without bound.
export class SpanScene implements Scene {
  #spans: RawSpan[] = [];
  #edits: RawEdit[] = [];
  begin() {
    this.#spans = [];
    this.#edits = [];
  }
  edit(from: number, to: number, newlines: number, indent: number) {
    if (this.#edits.length >= MAX_SPANS) throw new Error(`the formatter drew more than ${MAX_SPANS} edits`);
    this.#edits.push({ from, to, newlines, indent });
  }
  takeEdits(): RawEdit[] {
    const edits = this.#edits;
    this.#edits = [];
    return edits;
  }
  span(from: number, to: number, role: string) {
    if (this.#spans.length >= MAX_SPANS) throw new Error(`the highlighter drew more than ${MAX_SPANS} spans`);
    this.#spans.push({ from, to, kind: role });
  }
  take(): RawSpan[] {
    const spans = this.#spans;
    this.#spans = [];
    return spans;
  }
  swatch() {}
  line() {}
  polylineBegin() {}
  vertex() {}
  polylineEnd() {}
  circle() {}
  rect() {}
  text() {}
  end() {}
}

// The swatches of the theme being drawn. A theme names a handful of roles, so
// more than `MAX_SWATCHES` traps the program instead of growing without bound.
export const MAX_SWATCHES = 1000;

export class SwatchScene implements Scene {
  #swatches: RawSwatch[] = [];
  begin() {
    this.#swatches = [];
  }
  swatch(role: string, light: string, dark: string) {
    if (this.#swatches.length >= MAX_SWATCHES) throw new Error(`the theme drew more than ${MAX_SWATCHES} swatches`);
    this.#swatches.push({ role, light, dark });
  }
  take(): RawSwatch[] {
    const swatches = this.#swatches;
    this.#swatches = [];
    return swatches;
  }
  span() {}
  edit() {}
  line() {}
  polylineBegin() {}
  vertex() {}
  polylineEnd() {}
  circle() {}
  rect() {}
  text() {}
  end() {}
}

export type DrawingContext = Pick<
  CanvasRenderingContext2D | OffscreenCanvasRenderingContext2D,
  | "canvas"
  | "strokeStyle"
  | "fillStyle"
  | "font"
  | "textBaseline"
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
  | "arc"
  | "fill"
  | "fillRect"
  | "fillText"
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
    ctx.font = TEXT_FONT;
    ctx.textBaseline = "top";
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

  // A negative radius draws nothing: `arc` would throw on it.
  circle(x: number, y: number, r: number, color: string) {
    if (r < 0) return;
    const ctx = this.#ctx;
    ctx.fillStyle = color;
    ctx.beginPath();
    ctx.arc(x, y, r, 0, 2 * Math.PI);
    ctx.fill();
  }

  rect(x: number, y: number, w: number, h: number, color: string) {
    this.#ctx.fillStyle = color;
    this.#ctx.fillRect(x, y, w, h);
  }

  // (x, y) is the top left of the text, as a Rect's is.
  text(x: number, y: number, text: string, color: string) {
    this.#ctx.fillStyle = color;
    this.#ctx.fillText(text, x, y);
  }

  // The picture has no text to style and no theme to read.
  span() {}
  edit() {}
  swatch() {}

  end() {
    this.#ctx.restore();
  }
}

export type HostEvent =
  | { kind: "Tick"; dt: number }
  | { kind: "KeyDown" | "KeyUp"; key: string }
  | { kind: "PointerMove" | "PointerDown" | "PointerUp"; x: number; y: number }
  | { kind: "Edited"; text: string; cursor: number }
  | { kind: "HostTags"; names: string };

export type EventKind = HostEvent["kind"];

const EVENT_PREFIX = "goat_event_";

// Each host event under the turtle's name, then the canvas host's. A module is
// built against one vocabulary, so at most one of the two exports exists.
const EVENT_NAMES: Record<EventKind, readonly [string, string]> = {
  Tick: ["Tick", "Frame"],
  KeyDown: ["KeyDown", "KeyPress"],
  KeyUp: ["KeyUp", "KeyRelease"],
  PointerMove: ["PointerMove", "MouseMove"],
  PointerDown: ["PointerDown", "MousePress"],
  PointerUp: ["PointerUp", "MouseRelease"],
  Edited: ["Edited", "Edited"],
  HostTags: ["HostTags", "HostTags"],
};

function constructorFor(exports: WebAssembly.Exports, kind: EventKind): Function | undefined {
  const found = EVENT_NAMES[kind].map((name) => exports[EVENT_PREFIX + name]).find((x) => typeof x === "function");
  return found as Function | undefined;
}

// The events the module handles: one per `goat_event_*` export.
export function subscriptions(exports: WebAssembly.Exports): EventKind[] {
  return (Object.keys(EVENT_NAMES) as EventKind[]).filter((kind) => constructorFor(exports, kind));
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
  const make = constructorFor(exports, event.kind);
  if (!make) return null;
  switch (event.kind) {
    case "Tick":
      return make(event.dt);
    case "KeyDown":
    case "KeyUp":
      return make(newString(exports, event.key));
    case "Edited":
      return make(newString(exports, event.text), BigInt(event.cursor));
    case "HostTags":
      return make(newString(exports, event.names));
    default:
      return make(event.x, event.y);
  }
}
