// The compile-and-draw engine for hosts that own the editor (hosts/apple): the
// host sends source in and reads `EngineMessage`s back. There is no editor UI
// here, only a canvas and the runtime.

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
  | { type: "state"; state: "running" | "finished" | "failed"; message?: string };

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
}

const LOCATED = /^(in the prelude, )?(\d+):(\d+): /;

// Reads the checker's rendered form, `line:col: message`, the source line, then
// a caret underline (checker/src/error.rs), one block per error.
export function parseDiagnostics(rendered: string): Diagnostic[] {
  return rendered.split("\n\n").map((block) => {
    const located = LOCATED.exec(block);
    const lines = block.split("\n");
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

export function createEngine({ canvas, compiler, post, runner, focus = () => canvas.focus() }: EngineEnv): Engine {
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
        const started = await runInteractive(compiled.module, canvas, fail);
        if (!current()) return started.stop();
        loop = started;
        focus();
        return;
      }
      const lines: string[] = [];
      const { commands } = await run(compiled.module, { onOutput: (line) => lines.push(line) });
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
