// Browser host for compiled goat modules. No runtime dependencies.
//
// Contract with the compiler (docs/mir.md; mirrored by cli/src/lib.rs and
// cli/src/turtle.rs, which are the reference semantics):
//   imports  goat.{print_number,print_bool,print_string,write_number,write_string,write_end,trap}
//            turtle.{forward,back,left,right,pen_up,pen_down,color}
//   exports  memory, goat_entry() -> (), goat_live_allocs() -> u32 (optional),
//            goat_site (global: 1 + the index of the user call in flight, 0 for none)
//   section  goat.sites: u32 LE (start, end) source byte ranges, one per site
//   string   at object pointer p: byte length is a u32 LE at p+8, UTF-8 bytes at p+12
// Turtle calls only record commands, so the program runs to completion without
// blocking; `animate` replays the log onto a canvas afterwards.

const STR_LEN = 8;
const STR_BYTES = 12;
const MAX_COMMANDS = 1_000_000;
export const COLOR_PATTERN = /^[A-Za-z0-9#]{1,32}$/;

export type Command =
  | { kind: "forward" | "back" | "left" | "right"; value: number }
  | { kind: "color"; value: string }
  | { kind: "pen_up" | "pen_down" };

export type Point = [x: number, y: number];
export interface Stroke {
  color: string;
  points: Point[];
}

export interface GoatExports {
  memory: WebAssembly.Memory;
  goat_entry(): void;
  goat_live_allocs?(): number;
  goat_site?: WebAssembly.Global;
}

export class Trap extends Error {}

export interface HostImports {
  goat: {
    print_number(x: number): void;
    print_bool(b: number): void;
    print_string(ptr: number): void;
    write_number(x: number): void;
    write_string(ptr: number): void;
    write_end(): void;
    trap(ptr: number): void;
  };
  turtle: {
    forward(x: number): void;
    back(x: number): void;
    left(x: number): void;
    right(x: number): void;
    pen_up(): void;
    pen_down(): void;
    color(ptr: number): void;
  };
}

export interface Host {
  imports: HostImports;
  output: string[];
  commands: Command[];
}

export interface RunResult {
  output: string[];
  commands: Command[];
  liveAllocs: number | null;
}

export interface AnimateOptions {
  perFrame?: number;
  raf?: (callback: () => void) => void;
}

export function formatNumber(x: number): string {
  if (x > -1e18 && x < 1e18 && Number.isInteger(x)) return BigInt(x).toString();
  return formatG15(x);
}

function formatG15(x: number): string {
  if (Number.isNaN(x)) return "nan";
  if (!Number.isFinite(x)) return x < 0 ? "-inf" : "inf";
  const [mantissa, exp] = x.toExponential(14).split("e") as [string, string];
  const e = Number(exp);
  if (e >= -4 && e < 15) return stripZeros(x.toFixed(14 - e));
  return `${stripZeros(mantissa)}e${e < 0 ? "-" : "+"}${String(Math.abs(e)).padStart(2, "0")}`;
}

function stripZeros(s: string): string {
  return s.includes(".") ? s.replace(/0+$/, "").replace(/\.$/, "") : s;
}

export function readString(memory: WebAssembly.Memory, ptr: number): string {
  const data = memory.buffer;
  const start = ptr >>> 0;
  if (start + STR_BYTES > data.byteLength) throw new Error("string out of bounds");
  const len = new DataView(data).getUint32(start + STR_LEN, true);
  if (start + STR_BYTES + len > data.byteLength) throw new Error("string out of bounds");
  return new TextDecoder().decode(new Uint8Array(data, start + STR_BYTES, len));
}

function leb128(bytes: Uint8Array, at: number): [value: number, next: number] | undefined {
  let value = 0;
  for (let shift = 0; at < bytes.length && shift < 35; shift += 7) {
    const byte = bytes[at++]!;
    value += (byte & 0x7f) * 2 ** shift;
    if ((byte & 0x80) === 0) return [value, at];
  }
  return undefined;
}

// The (start, end) byte ranges of a module's `goat.sites` custom section, in
// site-number order; empty when the section is missing or malformed.
export function siteTable(wasm: Uint8Array): Array<[start: number, end: number]> {
  let at = 8;
  while (at < wasm.length) {
    const id = wasm[at++]!;
    const size = leb128(wasm, at);
    if (!size) break;
    const [length, body] = size;
    if (body + length > wasm.length) break;
    at = body + length;
    if (id !== 0) continue;
    const name = leb128(wasm, body);
    if (!name) continue;
    const [nameLength, nameAt] = name;
    const table = nameAt + nameLength;
    if (table > at || new TextDecoder().decode(wasm.subarray(nameAt, table)) !== "goat.sites") continue;
    const view = new DataView(wasm.buffer, wasm.byteOffset + table, Math.floor((at - table) / 8) * 8);
    const sites: Array<[number, number]> = [];
    for (let i = 0; i < view.byteLength; i += 8) sites.push([view.getUint32(i, true), view.getUint32(i + 4, true)]);
    return sites;
  }
  return [];
}

// `line:col: message`, the offending line, and a caret underline, the shape of
// the CLI's `GoatError::render`. The span is in UTF-8 bytes; the column counts
// characters.
export function renderTrap(source: string, [start, end]: [number, number], message: string): string {
  const bytes = new TextEncoder().encode(source);
  const decode = (from: number, to: number) => new TextDecoder().decode(bytes.subarray(from, to));
  const offset = Math.min(start, bytes.length);
  let lineStart = 0;
  let line = 1;
  for (let i = 0; i < offset; i++) {
    if (bytes[i] === 0x0a) {
      line++;
      lineStart = i + 1;
    }
  }
  let lineEnd = bytes.indexOf(0x0a, lineStart);
  if (lineEnd < 0) lineEnd = bytes.length;
  const col = [...decode(lineStart, offset)].length + 1;
  const caret = "^".repeat(Math.max(end - start, 1));
  return `${line}:${col}: ${message}\n  ${decode(lineStart, lineEnd)}\n  ${" ".repeat(col - 1)}${caret}`;
}

function finite(name: string, x: number): number {
  if (!Number.isFinite(x)) {
    throw new Error(`${name} needs a real number, not ${formatNumber(x)}`);
  }
  return x;
}

// Builds the import object and the logs it fills. `memory()` supplies the
// module's memory once it exists.
export function createHost(memory: () => WebAssembly.Memory): Host {
  const output: string[] = [];
  const commands: Command[] = [];
  let line = "";
  const finish = () => {
    output.push(line);
    line = "";
  };
  const say = (text: string) => {
    line += text;
    finish();
  };
  const record = (command: Command) => {
    if (commands.length >= MAX_COMMANDS) {
      throw new Error(`the turtle drew more than ${MAX_COMMANDS} commands`);
    }
    commands.push(command);
  };
  const move = (kind: "forward" | "back" | "left" | "right") => (x: number) => record({ kind, value: finite(kind, x) });
  const imports: HostImports = {
    goat: {
      print_number: (x: number) => say(formatNumber(x)),
      print_bool: (b: number) => say(b !== 0 ? "true" : "false"),
      print_string: (ptr: number) => say(readString(memory(), ptr)),
      write_number: (x: number) => {
        line += formatNumber(x);
      },
      write_string: (ptr: number) => {
        line += readString(memory(), ptr);
      },
      write_end: finish,
      trap: (ptr: number) => {
        throw new Trap(readString(memory(), ptr));
      },
    },
    turtle: {
      forward: move("forward"),
      back: move("back"),
      left: move("left"),
      right: move("right"),
      pen_up: () => record({ kind: "pen_up" }),
      pen_down: () => record({ kind: "pen_down" }),
      color: (ptr: number) => {
        const value = readString(memory(), ptr);
        if (!COLOR_PATTERN.test(value)) {
          throw new Error(`color wants a name like "red" or a code like "#ff8800", not ${JSON.stringify(value)}`);
        }
        record({ kind: "color", value });
      },
    },
  };
  return { imports, output, commands };
}

// The pen's trail: a run of pen-down moves in one color is one stroke.
export function strokes(commands: Command[]): Stroke[] {
  let x = 0;
  let y = 0;
  let heading = 0;
  let penDown = true;
  let color = "black";
  let open = false;
  const result: Stroke[] = [];
  const mod360 = (d: number) => ((d % 360) + 360) % 360;
  for (const command of commands) {
    if (command.kind === "forward" || command.kind === "back") {
      const distance = command.kind === "back" ? -command.value : command.value;
      const angle = (heading * Math.PI) / 180;
      const toX = x + distance * Math.sin(angle);
      const toY = y - distance * Math.cos(angle);
      if (penDown) {
        if (!open) {
          result.push({ color, points: [[x, y]] });
          open = true;
        }
        result[result.length - 1]!.points.push([toX, toY]);
      }
      [x, y] = [toX, toY];
    } else if (command.kind === "left") heading = mod360(heading - command.value);
    else if (command.kind === "right") heading = mod360(heading + command.value);
    else if (command.kind === "pen_up") [penDown, open] = [false, false];
    else if (command.kind === "pen_down") penDown = true;
    else if (command.kind === "color") [color, open] = [command.value, false];
  }
  return result;
}

// A trap carrying the user's call that was in flight, when the module says which.
function locate(trap: Trap, exports: GoatExports, moduleBytes: BufferSource, source: string): Error {
  const bytes = ArrayBuffer.isView(moduleBytes)
    ? new Uint8Array(moduleBytes.buffer, moduleBytes.byteOffset, moduleBytes.byteLength)
    : new Uint8Array(moduleBytes);
  const site = siteTable(bytes)[Number(exports.goat_site?.value) - 1];
  return site ? new Trap(`trap: ${renderTrap(source, site, trap.message)}`) : trap;
}

export async function run(
  moduleBytes: BufferSource,
  { onOutput, source }: { onOutput?: (line: string) => void; source?: string } = {},
): Promise<RunResult> {
  let memory: WebAssembly.Memory | undefined;
  const host = createHost(() => memory!);
  const { instance } = await WebAssembly.instantiate(moduleBytes, { ...host.imports });
  const exports = instance.exports as unknown as GoatExports;
  memory = exports.memory;
  if (!memory) throw new Error("module exports no memory");
  try {
    exports.goat_entry();
  } catch (e) {
    throw source === undefined || !(e instanceof Trap) ? e : locate(e, exports, moduleBytes, source);
  }
  const liveAllocs = exports.goat_live_allocs?.() ?? null;
  if (onOutput) host.output.forEach((line) => onOutput(line));
  return { output: host.output, commands: host.commands, liveAllocs };
}

// Browser only: draws the strokes segment by segment, `perFrame` segments per
// animation frame, scaled to fit the canvas. Resolves when drawing finishes.
export function animate(
  canvas: HTMLCanvasElement,
  commands: Command[],
  { perFrame = 4, raf = requestAnimationFrame }: AnimateOptions = {},
): Promise<void> {
  const ctx = canvas.getContext("2d")!;
  const paths = strokes(commands);
  const points = paths.flatMap((s) => s.points);
  const xs = points.map((p) => p[0]);
  const ys = points.map((p) => p[1]);
  const [minX, maxX] = [Math.min(0, ...xs), Math.max(0, ...xs)];
  const [minY, maxY] = [Math.min(0, ...ys), Math.max(0, ...ys)];
  const margin = 10;
  const width = maxX - minX + 2 * margin;
  const height = maxY - minY + 2 * margin;
  const scale = Math.min(canvas.width / width, canvas.height / height);
  const at = ([px, py]: Point): Point => [
    (px - minX + margin) * scale + (canvas.width - width * scale) / 2,
    (py - minY + margin) * scale + (canvas.height - height * scale) / 2,
  ];
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.lineWidth = 1;
  ctx.lineCap = "round";
  ctx.lineJoin = "round";
  const segments = paths.flatMap(({ color, points: ps }) =>
    ps.slice(1).map((to, i) => ({ color, from: ps[i], to })),
  );
  return new Promise<void>((resolve) => {
    let next = 0;
    const frame = () => {
      for (const end = Math.min(next + perFrame, segments.length); next < end; next++) {
        const { color, from, to } = segments[next]!;
        ctx.strokeStyle = color;
        ctx.beginPath();
        ctx.moveTo(...at(from));
        ctx.lineTo(...at(to));
        ctx.stroke();
      }
      if (next < segments.length) raf(frame);
      else resolve();
    };
    frame();
  });
}
