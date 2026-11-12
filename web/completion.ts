// Completion for the playground editor, answered by the compiler: its checker
// reads the half-typed buffer, so a name's type decides what a `.` offers and
// a `match` offers its scrutinee's tags. This file only adapts the answer to
// CodeMirror; the wasm module does the thinking.

import type { Completion, CompletionContext, CompletionResult, CompletionSource } from "@codemirror/autocomplete";
import type { Completer, OptionKind } from "./compile.ts";

const TYPES: Record<OptionKind, string> = {
  variable: "variable",
  function: "function",
  keyword: "keyword",
  tag: "class",
  field: "property",
};

// Typing opens the list once a letter is typed, or a `.` or `::`; Ctrl-Space opens it
// anywhere. The compiler's order is the ranking, so CodeMirror does not refilter.
export function goatCompletions(complete: Completer): CompletionSource {
  return (context: CompletionContext): CompletionResult | null => {
    const source = context.state.doc.toString();
    const found = complete(source, context.pos);
    if (!found) return null;
    const afterDot = source[found.from - 1] === "." && source[found.from - 2] !== ".";
    const afterTake = source.slice(found.from - 2, found.from) === "::";
    if (!context.explicit && found.from === context.pos && !afterDot && !afterTake) return null;
    const options: Completion[] = found.options.map(({ kind, label, detail }) => ({
      label,
      detail: detail || undefined,
      type: TYPES[kind],
    }));
    return { from: found.from, options, filter: false };
  };
}
