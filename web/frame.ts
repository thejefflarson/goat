// The frame encoding a compiled `draw` hands `scene.frame` once per frame, the
// browser half of mir/src/frame.rs (ADR 0015, second addendum). A frame declares
// the scene calls it makes, then makes them:
//
//   frame  = version:u8 ncalls:u8 call{ncalls} record*
//   call   = name_len:u8 name:utf8 nparams:u8 wire:u8{nparams}
//   record = call_index:u8 value{nparams of that call}
//   value  = Int: i64 LE | Float: f64 LE | Bool: u8 | Str: len:u32 LE, utf8
//
// The bytes are the goat program's, so every read is bounds-checked and a
// malformed frame throws, which traps the program.

export const FRAME_VERSION = 1;

export type FrameValue = number | boolean | string;

export type FrameHandler = (args: FrameValue[]) => void;

interface Call {
  wires: Uint8Array;
  handler: FrameHandler;
}

const INT = "i".charCodeAt(0);
const FLOAT = "f".charCodeAt(0);
const BOOL = "b".charCodeAt(0);
const STR = "s".charCodeAt(0);

const NAMES = new TextDecoder("utf-8", { fatal: true });
const TEXT = new TextDecoder();

// Colors and roles are short ASCII words, which a loop builds faster than a
// TextDecoder call; anything else takes the decoder, which replaces bad bytes.
const SHORT_TEXT = 24;

function text(bytes: Uint8Array, start: number, len: number): string {
  if (len <= SHORT_TEXT) {
    let out = "";
    for (let i = 0; i < len; i++) {
      const byte = bytes[start + i]!;
      if (byte >= 0x80) return TEXT.decode(bytes.subarray(start, start + len));
      out += String.fromCharCode(byte);
    }
    return out;
  }
  return TEXT.decode(bytes.subarray(start, start + len));
}

class Reader {
  at = 0;
  readonly bytes: Uint8Array;
  readonly view: DataView;
  constructor(bytes: Uint8Array) {
    this.bytes = bytes;
    this.view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  }

  need(n: number): number {
    const start = this.at;
    if (n > this.bytes.length - start) throw new Error("the frame ends in the middle of a value");
    this.at = start + n;
    return start;
  }
}

// Decodes frames and replays each as calls to the handler `resolve` names. The
// calls a frame declares are read again only when the header changes.
export class FrameDecoder {
  #resolve: (name: string) => FrameHandler | undefined;
  #header = new Uint8Array(0);
  #calls: Call[] = [];

  constructor(resolve: (name: string) => FrameHandler | undefined) {
    this.#resolve = resolve;
  }

  replay(bytes: Uint8Array): void {
    const r = new Reader(bytes);
    if (r.bytes[r.need(1)] !== FRAME_VERSION) {
      throw new Error(`the frame is version ${r.bytes[0]}, not ${FRAME_VERSION}`);
    }
    if (!this.#cached(bytes)) this.#readHeader(r);
    else r.at = this.#header.length;
    const args: FrameValue[] = [];
    while (r.at < bytes.length) {
      const call = this.#calls[r.bytes[r.at++]!];
      if (!call) throw new Error("the frame calls a scene call it did not declare");
      args.length = 0;
      for (const wire of call.wires) {
        switch (wire) {
          case INT:
            args.push(Number(r.view.getBigInt64(r.need(8), true)));
            break;
          case FLOAT:
            args.push(r.view.getFloat64(r.need(8), true));
            break;
          case BOOL:
            args.push(r.bytes[r.need(1)] !== 0);
            break;
          default: {
            const len = r.view.getUint32(r.need(4), true);
            args.push(text(r.bytes, r.need(len), len));
          }
        }
      }
      call.handler(args);
    }
  }

  #cached(bytes: Uint8Array): boolean {
    const header = this.#header;
    if (header.length === 0 || bytes.length < header.length) return false;
    for (let i = 0; i < header.length; i++) if (bytes[i] !== header[i]) return false;
    return true;
  }

  #readHeader(r: Reader): void {
    const calls: Call[] = [];
    const count = r.bytes[r.need(1)]!;
    for (let i = 0; i < count; i++) {
      const nameLength = r.bytes[r.need(1)]!;
      const nameAt = r.need(nameLength);
      let name: string;
      try {
        name = NAMES.decode(r.bytes.subarray(nameAt, nameAt + nameLength));
      } catch {
        throw new Error("a scene call name in the frame is not text");
      }
      const wireCount = r.bytes[r.need(1)]!;
      const wireAt = r.need(wireCount);
      const wires = r.bytes.slice(wireAt, wireAt + wireCount);
      if (wires.some((w) => w !== INT && w !== FLOAT && w !== BOOL && w !== STR)) {
        throw new Error("the frame has an unknown value type");
      }
      const handler = this.#resolve(name);
      if (!handler) throw new Error(`the host has no scene call ${name}`);
      calls.push({ wires, handler });
    }
    this.#calls = calls;
    this.#header = r.bytes.slice(0, r.at);
  }
}
