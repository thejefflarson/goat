// The compile-and-draw engine for hosts that own the editor (hosts/apple): the
// host sends source in and reads `EngineMessage`s back. There is no editor UI
// here, only a canvas and the runtime.

import { compile } from "./compile.ts";
import { isInteractiveModule, runInteractive, type Loop } from "./loop.ts";
import { animate, run } from "./runtime.ts";

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

export function createEngine({ canvas, compiler, post }: EngineEnv): Engine {
  let loop: Loop | undefined;
  let generation = 0;

  const stop = () => {
    generation++;
    loop?.stop();
    loop = undefined;
  };

  // A run that was superseded or stopped while awaiting must not post or draw.
  const runSource = async (source: string) => {
    stop();
    const mine = generation;
    const current = () => mine === generation;
    const fail = (message: string) => {
      if (current()) post({ type: "state", state: "failed", message });
    };
    canvas.getContext("2d")!.clearRect(0, 0, canvas.width, canvas.height);
    try {
      const compiled = await compile(compiler, source);
      if (!current()) return;
      if (!compiled.ok) {
        post({ type: "diagnostics", diagnostics: parseDiagnostics(compiled.diagnostics) });
        return fail("your program has problems");
      }
      post({ type: "state", state: "running" });
      if (isInteractiveModule(await WebAssembly.compile(compiled.module))) {
        const started = await runInteractive(compiled.module, canvas, fail);
        if (!current()) return started.stop();
        loop = started;
        canvas.focus();
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
