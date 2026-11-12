import type { Diagnostic } from "./compile.ts";

// The shape @codemirror/lint draws, which `Diagnostic` already positions.
export interface LintDiagnostic {
  from: number;
  to: number;
  message: string;
  severity: "error" | "info";
}

// Fits the checker's diagnostics to a document of `length` code units. A span
// with no width (an error at the very end of the program, say) is widened by
// one character so something is underlined.
// A secondary label becomes its own note at the place it names, so the problems
// panel lists both locations; messages stay plain text.
export function lintDiagnostics(found: Diagnostic[], length: number): LintDiagnostic[] {
  const fit = ({ from, to }: { from: number; to: number }) => {
    to = Math.min(to, length);
    from = Math.min(from, to);
    if (from === to) {
      if (to < length) to += 1;
      else from = Math.max(0, from - 1);
    }
    return { from, to };
  };
  return found.flatMap(({ message, labels = [], ...place }) => [
    { ...fit(place), severity: "error" as const, message },
    ...labels.map((label) => ({ ...fit(label), severity: "info" as const, message: `note: ${label.message}` })),
  ]);
}
