import type { Diagnostic } from "./compile.ts";

// The shape @codemirror/lint draws, which `Diagnostic` already positions.
export interface LintDiagnostic extends Diagnostic {
  severity: "error";
}

// Fits the checker's diagnostics to a document of `length` code units. A span
// with no width (an error at the very end of the program, say) is widened by
// one character so something is underlined.
export function lintDiagnostics(found: Diagnostic[], length: number): LintDiagnostic[] {
  return found.map(({ from, to, message }) => {
    to = Math.min(to, length);
    from = Math.min(from, to);
    if (from === to) {
      if (to < length) to += 1;
      else from = Math.max(0, from - 1);
    }
    return { from, to, severity: "error", message };
  });
}
