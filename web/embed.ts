// The compile-and-draw engine for hosts that own the editor (hosts/apple): the
// host sends source in and reads `EngineMessage`s back. There is no editor UI
// here, only a canvas and the runtime.

import { type BeatMessage, createBeat } from "./beat.ts";
import { compile } from "./compile.ts";
import { isInteractiveModule, runInteractive, type Loop } from "./loop.ts";
import { animate, run } from "./runtime.ts";
import type { Runner } from "./supervisor.ts";

// `line` and `column` are 1-based, `column` and `length` count characters, and
// line 0 means the message has no place in the user's source.
export interface Diagnostic {
  line: number;
  column: number;
  length: number;
  message: string;
}

export type EngineMessage =
  | { type: "ready" }
  | { type: "diagnostics"; diagnostics: Diagnostic[] }
  | { type: "output"; lines: string[] }
  | { type: "state"; state: "running" | "finished" | "failed"; message?: string }
  | BeatMessage;

export interface Engine {
  run(source: string): Promise<void>;
  stop(): void;
}

export interface EngineEnv {
  canvas: HTMLCanvasElement;
  compiler: WebAssembly.Module;
  post(message: EngineMessage): void;
  // When present, goat runs in a terminable worker that owns the drawing
  // surface (ADR 0021); otherwise it runs on this thread against `canvas`.
  runner?: Runner;
  focus?(): void;
  // Posts a `beat` around every call into goat, for a host that watches the page
  // from outside and tears it down when goat stops answering. Without a runner,
  // this is the only thing that can stop a runaway program, so the engine
  // declines to run without it.
  heartbeat?: boolean;
}

export const UNPROTECTED_MESSAGE =
  "goat will not run here: nothing could stop a program that never finishes. Serve the page cross-origin isolated, or open it from a host app that watches it.";

const LOCATED = /^(in the prelude, )?(\d+):(\d+): /;
const NOTE = /^\d+:\d+: note: /;

// Reads the checker's rendered form, `line:col: message`, the source line, then
// a caret underline (checker/src/error.rs), one block per error. The notes an
// error carries follow its own caret line; this host shows only the error
// itself, so they are dropped until it learns to draw a second location.
export function parseDiagnostics(rendered: string): Diagnostic[] {
  return rendered.split("\n\n").map((block) => {
    const located = LOCATED.exec(block);
    const all = block.split("\n");
    const note = all.findIndex((line, i) => i > 0 && NOTE.test(line));
    const lines = note < 0 ? all : all.slice(0, note);
    if (!located || located[1] || lines.length < 3) {
      return { line: 0, column: 0, length: 0, message: block };
    }
    const length = /\^+\s*$/.exec(lines[lines.length - 1]!)?.[0].trim().length ?? 1;
    return {
      line: Number(located[2]),
      column: Number(located[3]),
      length,
      message: [lines[0]!.slice(located[0].length), ...lines.slice(1, -2)].join("\n"),
    };
  });
}

export function createEngine({ canvas, compiler, post, runner, heartbeat = false, focus = () => canvas.focus() }: EngineEnv): Engine {
  const beat = heartbeat ? createBeat(post) : undefined;
  let loop: Loop | undefined;
  let generation = 0;

  const stop = () => {
    generation++;
    loop?.stop();
    loop = undefined;
    runner?.stop();
  };

  // A run that was superseded or stopped while awaiting must not post or draw.
  const runSource = async (source: string) => {
    stop();
    const mine = generation;
    const current = () => mine === generation;
    const fail = (message: string) => {
      if (current()) post({ type: "state", state: "failed", message });
    };
    if (!runner && !heartbeat) return fail(UNPROTECTED_MESSAGE);
    if (!runner) canvas.getContext("2d")!.clearRect(0, 0, canvas.width, canvas.height);
    try {
      const compiled = await compile(compiler, source);
      if (!current()) return;
      if (!compiled.ok) {
        post({ type: "diagnostics", diagnostics: parseDiagnostics(compiled.diagnostics) });
        return fail("your program has problems");
      }
      post({ type: "state", state: "running" });
      const interactive = isInteractiveModule(await WebAssembly.compile(compiled.module));
      if (!current()) return;
      if (runner) {
        let failed = false;
        runner.start(
          { mode: interactive ? "interactive" : "once", module: compiled.module },
          {
            onReady: () => {
              if (!current()) return;
              if (failed) post({ type: "state", state: "running" });
              failed = false;
              focus();
            },
            onOutput: (lines) => current() && post({ type: "output", lines }),
            onFinished: () => current() && post({ type: "state", state: "finished" }),
            onFailed: (message) => {
              failed = true;
              fail(message);
            },
          },
        );
        return;
      }
      if (interactive) {
        const started = await runInteractive(
          compiled.module,
          canvas,
          fail,
          beat && ((call) => beat.around("frame", call)),
        );
        if (!current()) return started.stop();
        loop = started;
        focus();
        return;
      }
      const lines: string[] = [];
      const { commands } = await run(compiled.module, {
        onOutput: (line) => lines.push(line),
        around: beat && ((call) => beat.around("once", call)),
      });
      if (!current()) return;
      post({ type: "output", lines });
      await animate(canvas, commands, {
        raf: (frame) => (current() ? requestAnimationFrame(frame) : 0),
      });
      if (current()) post({ type: "state", state: "finished" });
    } catch (e) {
      fail(e instanceof Error ? e.message : String(e));
    }
  };

  return { run: runSource, stop };
}
