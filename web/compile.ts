// Drives goat_web.wasm; the record layout is documented in src/lib.rs.
import { utf16Offsets } from "./offsets.ts";

const OK = 0;
const DIAGNOSTIC_HEADER = 12;
const TOKEN_SIZE = 9;

type Entry = "gw_compile" | "gw_check" | "gw_tokenize";

interface CompilerExports {
  memory: WebAssembly.Memory;
  gw_alloc(len: number): number;
  gw_free(ptr: number, len: number): void;
  gw_free_result(rec: number): void;
  gw_compile(ptr: number, len: number): number;
  gw_check(ptr: number, len: number): number;
  gw_tokenize(ptr: number, len: number): number;
  gw_vocabulary(): number;
  gw_complete(ptr: number, len: number, cursor: number): number;
}

export type CompileResult =
  | { ok: true; module: Uint8Array<ArrayBuffer> }
  | { ok: false; diagnostics: string };

// A problem the checker found, positioned in UTF-16 code units of the source.
export interface Diagnostic {
  from: number;
  to: number;
  message: string;
}

export type TokenKind = "comment" | "keyword" | "literal" | "number" | "string" | "tag" | "operator";

const TOKEN_KINDS: readonly TokenKind[] = ["comment", "keyword", "literal", "number", "string", "tag", "operator"];

export interface Token {
  kind: TokenKind;
  from: number;
  to: number;
}

export async function loadCompiler(url: string | URL): Promise<WebAssembly.Module> {
  const response = await fetch(url);
  if (!response.ok) throw new Error(`could not load compiler: HTTP ${response.status}`);
  return WebAssembly.compile(await response.arrayBuffer());
}

function invoke(instance: WebAssembly.Instance, entry: Entry, source: string): { ok: boolean; payload: Uint8Array } {
  const exports = instance.exports as unknown as CompilerExports;
  const { memory, gw_alloc, gw_free } = exports;
  const text = new TextEncoder().encode(source);
  const src = gw_alloc(text.length);
  new Uint8Array(memory.buffer, src, text.length).set(text);
  const rec = exports[entry](src, text.length);
  gw_free(src, text.length);
  return takeRecord(exports, rec);
}

function takeRecord(exports: CompilerExports, rec: number): { ok: boolean; payload: Uint8Array } {
  const { memory, gw_free_result } = exports;
  const view = new DataView(memory.buffer);
  const tag = view.getUint8(rec);
  const payload = new Uint8Array(memory.buffer, rec + 5, view.getUint32(rec + 1, true)).slice();
  gw_free_result(rec);
  return { ok: tag === OK, payload };
}

export async function compile(compiler: WebAssembly.Module, source: string): Promise<CompileResult> {
  const { ok, payload } = invoke(await WebAssembly.instantiate(compiler, {}), "gw_compile", source);
  return ok
    ? { ok, module: payload as Uint8Array<ArrayBuffer> }
    : { ok, diagnostics: new TextDecoder().decode(payload) };
}

// The problems `compile` would fail with, as the checker's own spans and messages.
export async function check(compiler: WebAssembly.Module, source: string): Promise<Diagnostic[]> {
  const { ok, payload } = invoke(await WebAssembly.instantiate(compiler, {}), "gw_check", source);
  return ok ? [] : decodeDiagnostics(payload, source);
}

export function decodeDiagnostics(payload: Uint8Array, source: string): Diagnostic[] {
  const view = new DataView(payload.buffer, payload.byteOffset, payload.byteLength);
  const index = utf16Offsets(source);
  const found: Diagnostic[] = [];
  for (let at = 0; at + DIAGNOSTIC_HEADER <= payload.length; ) {
    const length = view.getUint32(at + 8, true);
    const message = new TextDecoder().decode(payload.subarray(at + DIAGNOSTIC_HEADER, at + DIAGNOSTIC_HEADER + length));
    found.push({ from: index(view.getUint32(at, true)), to: index(view.getUint32(at + 4, true)), message });
    at += DIAGNOSTIC_HEADER + length;
  }
  return found;
}

// A tokenizer that keeps one compiler instance alive: it runs on every
// keystroke, so it must not pay for instantiation. It never traps on any input;
// if one ever did, the next call starts from a fresh instance.
export function createTokenizer(compiler: WebAssembly.Module): (source: string) => Token[] {
  let instance: WebAssembly.Instance | undefined;
  return (source) => {
    try {
      instance ??= new WebAssembly.Instance(compiler, {});
      const { ok, payload } = invoke(instance, "gw_tokenize", source);
      return ok ? decodeTokens(payload, source) : [];
    } catch {
      instance = undefined;
      return [];
    }
  };
}

export function decodeTokens(payload: Uint8Array, source: string): Token[] {
  const view = new DataView(payload.buffer, payload.byteOffset, payload.byteLength);
  const index = utf16Offsets(source);
  const tokens: Token[] = [];
  for (let at = 0; at + TOKEN_SIZE <= payload.length; at += TOKEN_SIZE) {
    const kind = TOKEN_KINDS[payload[at]];
    if (kind) tokens.push({ kind, from: index(view.getUint32(at + 1, true)), to: index(view.getUint32(at + 5, true)) });
  }
  return tokens;
}

export type WordKind = "keyword" | "function" | "tag";

const WORD_KINDS: readonly WordKind[] = ["keyword", "function", "tag"];

// A word the editor can complete. `detail` is a signature for a function and
// empty otherwise.
export interface Word {
  kind: WordKind;
  name: string;
  detail: string;
}

// The keywords of the grammar and the names the turtle host defines, straight
// from the compiler so they cannot drift from the language.
export function loadVocabulary(compiler: WebAssembly.Module): Word[] {
  const instance = new WebAssembly.Instance(compiler, {});
  const exports = instance.exports as unknown as CompilerExports;
  const { ok, payload } = takeRecord(exports, exports.gw_vocabulary());
  return ok ? decodeVocabulary(payload) : [];
}

export function decodeVocabulary(payload: Uint8Array): Word[] {
  const view = new DataView(payload.buffer, payload.byteOffset, payload.byteLength);
  const decoder = new TextDecoder();
  const words: Word[] = [];
  let at = 0;
  const text = () => {
    const length = view.getUint32(at, true);
    const value = decoder.decode(payload.subarray(at + 4, at + 4 + length));
    at += 4 + length;
    return value;
  };
  while (at < payload.length) {
    const kind = WORD_KINDS[payload[at++]];
    const name = text();
    const detail = text();
    if (kind) words.push({ kind, name, detail });
  }
  return words;
}

export type OptionKind = "variable" | "function" | "keyword" | "tag" | "field";

const OPTION_KINDS: readonly OptionKind[] = ["variable", "function", "keyword", "tag", "field"];

// One thing the editor can offer. `detail` is a signature or a type, or empty.
export interface CompletionOption {
  kind: OptionKind;
  label: string;
  detail: string;
}

// What can be typed at the cursor, best first; `from` is where the word being
// typed starts, in UTF-16 code units of the source.
export interface Completions {
  from: number;
  options: CompletionOption[];
}

export type Completer = (source: string, cursor: number) => Completions | null;

// A completer that keeps one compiler instance alive, as `createTokenizer`
// does. It asks the checker, so it works on source that does not parse; it
// returns null where nothing completes.
export function createCompleter(compiler: WebAssembly.Module): Completer {
  let instance: WebAssembly.Instance | undefined;
  return (source, cursor) => {
    try {
      instance ??= new WebAssembly.Instance(compiler, {});
      const exports = instance.exports as unknown as CompilerExports;
      const { memory, gw_alloc, gw_free } = exports;
      const encoder = new TextEncoder();
      const text = encoder.encode(source);
      const at = encoder.encode(source.slice(0, cursor)).length;
      const src = gw_alloc(text.length);
      new Uint8Array(memory.buffer, src, text.length).set(text);
      const record = exports.gw_complete(src, text.length, at);
      gw_free(src, text.length);
      const { ok, payload } = takeRecord(exports, record);
      return ok ? decodeCompletions(payload, source) : null;
    } catch {
      instance = undefined;
      return null;
    }
  };
}

export function decodeCompletions(payload: Uint8Array, source: string): Completions | null {
  if (payload.length === 0) return null;
  const view = new DataView(payload.buffer, payload.byteOffset, payload.byteLength);
  const decoder = new TextDecoder();
  let at = 4;
  const text = () => {
    const length = view.getUint32(at, true);
    const value = decoder.decode(payload.subarray(at + 4, at + 4 + length));
    at += 4 + length;
    return value;
  };
  const options: CompletionOption[] = [];
  while (at < payload.length) {
    const kind = OPTION_KINDS[payload[at++]];
    const label = text();
    const detail = text();
    if (kind) options.push({ kind, label, detail });
  }
  return { from: utf16Offsets(source)(view.getUint32(0, true)), options };
}
