// Drives goat_web.wasm; the record layout is documented in src/lib.rs.
import { utf16Offsets } from "./offsets.ts";

const OK = 0;
const DIAGNOSTIC_HEADER = 12;
const TOKEN_SIZE = 9;

type Entry =
  | "gw_compile"
  | "gw_compile_live"
  | "gw_check"
  | "gw_compile_canvas"
  | "gw_compile_canvas_live"
  | "gw_check_canvas"
  | "gw_check_theme"
  | "gw_compile_theme"
  | "gw_tokenize"
  | "gw_tokenize_canvas"
  | "gw_compile_editor";

// The vocabulary a program is written against: the turtle's, the canvas host's
// (`Frame`, `MousePress`, `Dot`, ...), or the theme's (`Swatch`), which
// `editor/theme.goat` is written in. The theme has its own compile and check;
// its text is lexed and completed as the turtle's.
export type Host = "turtle" | "canvas" | "theme";

const COMPILE: Record<Host, Entry> = { turtle: "gw_compile", canvas: "gw_compile_canvas", theme: "gw_compile_theme" };
const COMPILE_LIVE: Record<Host, Entry> = {
  turtle: "gw_compile_live",
  canvas: "gw_compile_canvas_live",
  theme: "gw_compile_theme",
};
const CHECK: Record<Host, Entry> = { turtle: "gw_check", canvas: "gw_check_canvas", theme: "gw_check_theme" };
const TOKENIZE: Record<Host, Entry> = { turtle: "gw_tokenize", canvas: "gw_tokenize_canvas", theme: "gw_tokenize" };
const COMPLETE: Record<Host, CompleteEntry> = {
  turtle: "gw_complete",
  canvas: "gw_complete_canvas",
  theme: "gw_complete",
};

type CompleteEntry = "gw_complete" | "gw_complete_canvas";

interface CompilerExports {
  memory: WebAssembly.Memory;
  gw_alloc(len: number): number;
  gw_free(ptr: number, len: number): void;
  gw_free_result(rec: number): void;
  gw_compile(ptr: number, len: number): number;
  gw_compile_live(ptr: number, len: number): number;
  gw_check(ptr: number, len: number): number;
  gw_compile_canvas(ptr: number, len: number): number;
  gw_compile_canvas_live(ptr: number, len: number): number;
  gw_check_canvas(ptr: number, len: number): number;
  gw_check_theme(ptr: number, len: number): number;
  gw_compile_theme(ptr: number, len: number): number;
  gw_tokenize(ptr: number, len: number): number;
  gw_tokenize_canvas(ptr: number, len: number): number;
  gw_compile_editor(ptr: number, len: number): number;
  gw_host_tags(): number;
  gw_host_tags_canvas(): number;
  gw_complete(ptr: number, len: number, cursor: number): number;
  gw_complete_canvas(ptr: number, len: number, cursor: number): number;
}

export type CompileResult =
  | { ok: true; module: Uint8Array<ArrayBuffer> }
  | { ok: false; diagnostics: string };

// A problem the checker found, positioned in UTF-16 code units of the source.
export interface Diagnostic {
  from: number;
  to: number;
  message: string;
  // Other places that explain the problem, each saying what it shows there.
  labels?: DiagnosticLabel[];
}

export interface DiagnosticLabel {
  from: number;
  to: number;
  message: string;
}

export type TokenKind = "comment" | "keyword" | "literal" | "number" | "string" | "tag" | "operator";

export const TOKEN_KINDS: readonly TokenKind[] = ["comment", "keyword", "literal", "number", "string", "tag", "operator"];

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

export async function compile(
  compiler: WebAssembly.Module,
  source: string,
  host: Host = "turtle",
  live = false,
): Promise<CompileResult> {
  const entry = (live ? COMPILE_LIVE : COMPILE)[host];
  const { ok, payload } = invoke(await WebAssembly.instantiate(compiler, {}), entry, source);
  return ok
    ? { ok, module: payload as Uint8Array<ArrayBuffer> }
    : { ok, diagnostics: new TextDecoder().decode(payload) };
}

// Like `compile`, but an interactive program comes out as a module that imports
// its heap, so `Loop.reload` can swap it in over a running one.
export const compileLive = (compiler: WebAssembly.Module, source: string, host: Host = "turtle"): Promise<CompileResult> =>
  compile(compiler, source, host, true);

// The problems `compile` would fail with, as the checker's own spans and messages.
export async function check(compiler: WebAssembly.Module, source: string, host: Host = "turtle"): Promise<Diagnostic[]> {
  const { ok, payload } = invoke(await WebAssembly.instantiate(compiler, {}), CHECK[host], source);
  return ok ? [] : decodeDiagnostics(payload, source);
}

// A program over the editor vocabulary (`Edited`, `HostTags`, `Span`), like
// `editor/highlight.goat`, as a module that draws style spans.
export async function compileEditor(compiler: WebAssembly.Module, source: string): Promise<CompileResult> {
  const { ok, payload } = invoke(await WebAssembly.instantiate(compiler, {}), "gw_compile_editor", source);
  return ok
    ? { ok, module: payload as Uint8Array<ArrayBuffer> }
    : { ok, diagnostics: new TextDecoder().decode(payload) };
}

// A program over the theme vocabulary (`Swatch`), like `editor/theme.goat`, as
// a module that draws one swatch per style role.
export async function compileTheme(compiler: WebAssembly.Module, source: string): Promise<CompileResult> {
  const { ok, payload } = invoke(await WebAssembly.instantiate(compiler, {}), "gw_compile_theme", source);
  return ok
    ? { ok, module: payload as Uint8Array<ArrayBuffer> }
    : { ok, diagnostics: new TextDecoder().decode(payload) };
}

const HOST_TAGS = { turtle: "gw_host_tags", canvas: "gw_host_tags_canvas" } as const;

// The names `host` declares as tags, space separated: what a highlighter must
// be told, since the text of a program does not declare them.
export function hostTags(compiler: WebAssembly.Module, host: Host): string {
  if (host === "theme") return "";
  const instance = new WebAssembly.Instance(compiler, {});
  const exports = instance.exports as unknown as CompilerExports;
  const { ok, payload } = takeRecord(exports, exports[HOST_TAGS[host]]());
  if (!ok) throw new Error("could not read the host's tags");
  return new TextDecoder().decode(payload);
}

export function decodeDiagnostics(payload: Uint8Array, source: string): Diagnostic[] {
  const view = new DataView(payload.buffer, payload.byteOffset, payload.byteLength);
  const index = utf16Offsets(source);
  const found: Diagnostic[] = [];
  let at = 0;
  const located = (): DiagnosticLabel => {
    const length = view.getUint32(at + 8, true);
    const start = at + DIAGNOSTIC_HEADER;
    const message = new TextDecoder().decode(payload.subarray(start, start + length));
    const place = { from: index(view.getUint32(at, true)), to: index(view.getUint32(at + 4, true)), message };
    at = start + length;
    return place;
  };
  const fits = (bytes: number) => at + bytes <= payload.length;
  while (fits(DIAGNOSTIC_HEADER)) {
    const diagnostic: Diagnostic = located();
    // A count or a label past the end of the payload is dropped, not read, so
    // a malformed payload cannot throw or allocate by the count it claims.
    const count = fits(4) ? view.getUint32(at, true) : 0;
    at += 4;
    const labels: DiagnosticLabel[] = [];
    while (labels.length < count && fits(DIAGNOSTIC_HEADER)) labels.push(located());
    found.push(labels.length > 0 ? { ...diagnostic, labels } : diagnostic);
  }
  return found;
}

// A tokenizer that keeps one compiler instance alive: it runs on every
// keystroke, so it must not pay for instantiation. It colors against the
// vocabulary `host` names at each call. It never traps on any input; if one
// ever did, the next call starts from a fresh instance.
export function createTokenizer(compiler: WebAssembly.Module, host: () => Host = () => "turtle"): (source: string) => Token[] {
  let instance: WebAssembly.Instance | undefined;
  return (source) => {
    try {
      instance ??= new WebAssembly.Instance(compiler, {});
      const { ok, payload } = invoke(instance, TOKENIZE[host()], source);
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
export function createCompleter(compiler: WebAssembly.Module, host: () => Host = () => "turtle"): Completer {
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
      const record = exports[COMPLETE[host()]](src, text.length, at);
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
