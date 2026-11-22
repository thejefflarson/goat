// The editor's formatter, written in goat (editor/format.goat, ADR 0041), run
// in a worker of its own under the supervisor (ADR 0021) like the highlighter.
// It cannot build text, so it answers with whitespace edits; this validates
// them and turns them into CodeMirror changes in UTF-16 offsets.

import { compileEditor } from "./compile.ts";
import type { HighlightRunner } from "./highlighter.ts";
import { utf16Offsets } from "./offsets.ts";
import type { RawEdit } from "./scene.ts";

// More line breaks or spaces than this in one gap is not a layout, whatever
// the program says.
const MAX_NEWLINES = 8;
const MAX_INDENT = 256;

export interface TextEdit {
  from: number;
  to: number;
  insert: string;
}

export interface Formatter {
  // The edits that lay `text` out in the house style, or a rejection if the
  // formatter cannot answer.
  format(text: string): Promise<TextEdit[]>;
}

// The formatter program's edits as changes over `source`, in UTF-16 offsets.
// The program is goat code and its words are not trusted: an edit that is
// malformed, out of range or out of order, that does not start and end on
// character boundaries, or that would replace anything but whitespace, is
// dropped, so no output can change what a program says.
export function acceptEdits(edits: unknown, source: string): TextEdit[] {
  if (!Array.isArray(edits)) return [];
  const bytes = new TextEncoder().encode(source).length;
  const index = utf16Offsets(source);
  const found: TextEdit[] = [];
  let end = 0;
  for (const edit of edits as Array<Partial<RawEdit> | null>) {
    if (typeof edit !== "object" || edit === null) continue;
    const { from, to, newlines, indent } = edit;
    if (![from, to, newlines, indent].every((n) => typeof n === "number" && Number.isInteger(n))) continue;
    if (from! < end || to! < from! || to! > bytes) continue;
    if (newlines! < 0 || newlines! > MAX_NEWLINES || indent! < 0 || indent! > MAX_INDENT) continue;
    const start = index(from!);
    const stop = index(to!);
    const replaced = source.slice(start, stop);
    if (new TextEncoder().encode(replaced).length !== to! - from! || !/^\s*$/.test(replaced)) continue;
    end = to!;
    found.push({ from: start, to: stop, insert: "\n".repeat(newlines!) + " ".repeat(indent!) });
  }
  return found;
}

export interface GoatFormatterOptions {
  compiler: WebAssembly.Module;
  // The text of editor/format.goat.
  source: string;
  runner: HighlightRunner;
}

interface Waiting {
  text: string;
  resolve(edits: TextEdit[]): void;
  reject(error: Error): void;
}

export class GoatFormatter implements Formatter {
  #options: GoatFormatterOptions;
  #ticket = 0;
  #waiting = new Map<number, Waiting>();
  #ready = false;

  constructor(options: GoatFormatterOptions) {
    this.#options = options;
  }

  // Compiles the formatter and starts its worker. True once it is running;
  // false if it cannot start, and then `format` rejects.
  async start(): Promise<boolean> {
    try {
      const compiled = await compileEditor(this.#options.compiler, this.#options.source);
      if (!compiled.ok) return false;
      return await new Promise<boolean>((resolve) => {
        this.#options.runner.start(
          { mode: "highlight", module: compiled.module },
          {
            onReady: () => {
              this.#ready = true;
              resolve(true);
            },
            onOutput: () => {},
            onSpans: (ticket, _spans, edits) => this.#answer(ticket, edits),
            onFailed: () => {
              this.#fail();
              resolve(false);
            },
          },
        );
      });
    } catch {
      this.#fail();
      return false;
    }
  }

  stop(): void {
    this.#fail();
    this.#options.runner.stop();
  }

  format(text: string): Promise<TextEdit[]> {
    if (!this.#ready) return Promise.reject(new Error("the formatter is not running"));
    const ticket = ++this.#ticket;
    return new Promise((resolve, reject) => {
      this.#waiting.set(ticket, { text, resolve, reject });
      try {
        this.#options.runner.input({ kind: "Edited", text, cursor: 0 }, ticket);
      } catch (e) {
        this.#waiting.delete(ticket);
        this.#fail();
        reject(e instanceof Error ? e : new Error(String(e)));
      }
    });
  }

  #answer(ticket: number, edits: RawEdit[]): void {
    const waiting = this.#waiting.get(ticket);
    if (!waiting) return;
    this.#waiting.delete(ticket);
    waiting.resolve(acceptEdits(edits, waiting.text));
  }

  // A trap ends the worker, and a stuck call has been terminated.
  #fail(): void {
    this.#ready = false;
    for (const waiting of this.#waiting.values()) waiting.reject(new Error("the formatter stopped"));
    this.#waiting.clear();
  }
}
