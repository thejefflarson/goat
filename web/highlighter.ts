// The editor's syntax highlighter written in goat (editor/highlight.goat, ADR
// 0020 addendum), run in a worker of its own under the supervisor (ADR 0021): a
// highlighter that spins or traps is terminated, and the editor falls back to
// the built-in tokenizer (`gw_tokenize`), which colors the same text the same
// way. CodeMirror keeps input, undo and IME; this only supplies the spans.

import { type Host, type Token, TOKEN_KINDS, compileEditor, createTokenizer, hostTags } from "./compile.ts";
import { utf16Offsets } from "./offsets.ts";
import type { RawSpan } from "./scene.ts";
import type { Runner } from "./supervisor.ts";
import type { HostEvent } from "./scene.ts";

// A call into the highlighter that takes longer than this is stuck: a scan of a
// page of source takes a few milliseconds.
export const HIGHLIGHT_BUDGET_MS = 500;

export interface TokenSource {
  // Asks for the tokens of `text`. Returns them at once when they are known now,
  // or null when they will arrive later through `onTokens`.
  request(text: string): Token[] | null;
  onTokens(listener: (tokens: Token[]) => void): () => void;
}

const KINDS: ReadonlySet<string> = new Set(TOKEN_KINDS);

// The highlighter program's spans as tokens over `source`, in UTF-16 offsets.
// The program is goat code and its words are not trusted: a `kind` outside the
// seven known roles never becomes a class name, and a span that is malformed,
// out of range or out of order is dropped.
export function acceptSpans(spans: unknown, source: string): Token[] {
  if (!Array.isArray(spans)) return [];
  const length = new TextEncoder().encode(source).length;
  const index = utf16Offsets(source);
  const tokens: Token[] = [];
  let end = 0;
  for (const span of spans as Array<Partial<RawSpan> | null>) {
    if (typeof span !== "object" || span === null) continue;
    const { from, to, kind } = span;
    if (typeof kind !== "string" || !KINDS.has(kind)) continue;
    if (typeof from !== "number" || typeof to !== "number" || !Number.isInteger(from) || !Number.isInteger(to)) continue;
    if (from < end || to <= from || to > length) continue;
    end = to;
    const start = index(from);
    const stop = index(to);
    if (start < stop) tokens.push({ kind: kind as Token["kind"], from: start, to: stop });
  }
  return tokens;
}

// What the highlighter needs of a `Supervisor`.
export interface HighlightRunner extends Runner {
  input(event: HostEvent, ticket?: number): void;
}

export interface GoatHighlighterOptions {
  compiler: WebAssembly.Module;
  // The text of editor/highlight.goat.
  source: string;
  runner: HighlightRunner;
  // The vocabulary whose tags the highlighter marks, asked at each request.
  host?: () => Host;
}

export class GoatHighlighter implements TokenSource {
  #options: GoatHighlighterOptions;
  #fallback: (text: string) => Token[];
  #listeners = new Set<(tokens: Token[]) => void>();
  #ticket = 0;
  #text = "";
  #ready = false;
  #sentHost: Host | undefined;

  constructor(options: GoatHighlighterOptions) {
    this.#options = options;
    this.#fallback = createTokenizer(options.compiler, this.#host);
  }

  #host = (): Host => this.#options.host?.() ?? "turtle";

  // Whether the goat highlighter is the one coloring the text right now.
  get active(): boolean {
    return this.#ready;
  }

  // Compiles the highlighter and starts its worker. Until it is ready, and for
  // good if it cannot start, requests are answered by the built-in tokenizer.
  async start(): Promise<void> {
    try {
      const compiled = await compileEditor(this.#options.compiler, this.#options.source);
      if (!compiled.ok) return;
      this.#options.runner.start(
        { mode: "highlight", module: compiled.module },
        {
          onReady: () => this.#workerReady(),
          onOutput: () => {},
          onSpans: (ticket, spans) => this.#spans(ticket, spans),
          onFailed: () => this.#failed(),
        },
      );
    } catch {
      this.#ready = false;
    }
  }

  stop(): void {
    this.#ready = false;
    this.#options.runner.stop();
  }

  onTokens(listener: (tokens: Token[]) => void): () => void {
    this.#listeners.add(listener);
    return () => void this.#listeners.delete(listener);
  }

  request(text: string): Token[] | null {
    this.#text = text;
    this.#ticket++;
    if (this.#ready && this.#send()) return null;
    return this.#fallback(text);
  }

  // Sends the current text, and the host's tags first when the worker has not
  // heard them. False if the worker could not be told.
  #send(): boolean {
    try {
      const host = this.#host();
      const { runner, compiler } = this.#options;
      if (host !== this.#sentHost) {
        runner.input({ kind: "HostTags", names: hostTags(compiler, host) });
        this.#sentHost = host;
      }
      runner.input({ kind: "Edited", text: this.#text, cursor: 0 }, this.#ticket);
      return true;
    } catch {
      this.stop();
      return false;
    }
  }

  // A fresh worker knows no tags and no text.
  #workerReady(): void {
    this.#ready = true;
    this.#sentHost = undefined;
    if (this.#ticket > 0 && !this.#send()) this.#emit(this.#fallback(this.#text));
  }

  #spans(ticket: number, spans: RawSpan[]): void {
    if (ticket === this.#ticket) this.#emit(acceptSpans(spans, this.#text));
  }

  // A trap ends the worker; a stuck call has been terminated and the supervisor
  // may start a fresh one, which says so through `onReady`.
  #failed(): void {
    this.stop();
    if (this.#ticket > 0) this.#emit(this.#fallback(this.#text));
  }

  #emit(tokens: Token[]): void {
    this.#listeners.forEach((listener) => listener(tokens));
  }
}
