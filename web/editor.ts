// The playground's code editor: CodeMirror 6 with goat's own lexer driving the
// colors and goat's own checker driving the underlines. Bundled for the
// browser by build-editor.ts; the pieces worth testing live in lint.ts and
// compile.ts, and the decorations in `tokenDecorations`.

import { defaultKeymap, history, historyKeymap } from "@codemirror/commands";
import { Compartment, RangeSetBuilder, type Extension } from "@codemirror/state";
import {
  Decoration,
  type DecorationSet,
  EditorView,
  ViewPlugin,
  type ViewUpdate,
  drawSelection,
  keymap,
  lineNumbers,
} from "@codemirror/view";
import { linter, lintGutter } from "@codemirror/lint";
import { autocompletion } from "@codemirror/autocomplete";
import { check, createCompleter, createTokenizer, type Token } from "./compile.ts";
import { goatCompletions } from "./completion.ts";
import { lintDiagnostics } from "./lint.ts";

const CHECK_DELAY_MS = 200;

export function tokenDecorations(tokens: Token[]): DecorationSet {
  const builder = new RangeSetBuilder<Decoration>();
  for (const { kind, from, to } of tokens) builder.add(from, to, Decoration.mark({ class: `tok-${kind}` }));
  return builder.finish();
}

function highlighting(tokenize: (source: string) => Token[]): Extension {
  return ViewPlugin.fromClass(
    class {
      decorations: DecorationSet;
      constructor(view: EditorView) {
        this.decorations = tokenDecorations(tokenize(view.state.doc.toString()));
      }
      update(update: ViewUpdate) {
        if (update.docChanged) this.decorations = tokenDecorations(tokenize(update.state.doc.toString()));
      }
    },
    { decorations: (plugin) => plugin.decorations },
  );
}

function liveChecking(compiler: WebAssembly.Module): Extension {
  const source = async (view: EditorView) => {
    const text = view.state.doc.toString();
    try {
      return lintDiagnostics(await check(compiler, text), text.length);
    } catch {
      return [];
    }
  };
  return [linter(source, { delay: CHECK_DELAY_MS }), lintGutter()];
}

function completing(compiler: WebAssembly.Module): Extension {
  return autocompletion({ override: [goatCompletions(createCompleter(compiler))] });
}

function withCompiler(compiler: WebAssembly.Module): Extension[] {
  const tokenize = createTokenizer(compiler);
  return [highlighting(tokenize), liveChecking(compiler), completing(compiler)];
}

// Colors come from the page's custom properties, so light and dark follow the
// page; the token colors fall back to values readable on a white panel.
const theme = EditorView.theme({
  "&": {
    height: "100%",
    color: "var(--fg)",
    backgroundColor: "var(--panel)",
    border: "1px solid var(--line)",
    borderRadius: "6px",
    fontSize: "14px",
  },
  "&.cm-focused": { outline: "2px solid var(--accent)" },
  ".cm-scroller": { fontFamily: "ui-monospace, Menlo, Consolas, monospace", lineHeight: "1.4" },
  ".cm-content": { caretColor: "var(--fg)" },
  ".cm-cursor": { borderLeftColor: "var(--fg)" },
  ".cm-gutters": { backgroundColor: "var(--panel)", color: "var(--tok-comment, #6a6a73)", border: "none" },
  "&.cm-focused .cm-selectionBackground, .cm-selectionBackground": { backgroundColor: "var(--selection, #c9c9ce)" },
  ".tok-keyword": { color: "var(--tok-keyword, #5b3fd1)" },
  ".tok-literal": { color: "var(--tok-literal, #0b6e99)" },
  ".tok-number": { color: "var(--tok-number, #0b6e99)" },
  ".tok-string": { color: "var(--tok-string, #1a7f37)" },
  ".tok-comment": { color: "var(--tok-comment, #6a6a73)", fontStyle: "italic" },
  ".tok-tag": { color: "var(--tok-tag, #b35900)" },
});

export interface GoatEditor {
  text(): string;
  setText(text: string): void;
}

// Without a `compiler` the editor still edits; it just neither colors, checks nor completes.
export function mountEditor(parent: HTMLElement, doc: string, compiler?: WebAssembly.Module): GoatEditor {
  const scheme = matchMedia("(prefers-color-scheme: dark)");
  const darkness = new Compartment();
  const view = new EditorView({
    parent,
    doc,
    extensions: [
      lineNumbers(),
      history(),
      drawSelection(),
      keymap.of([...defaultKeymap, ...historyKeymap]),
      theme,
      darkness.of(EditorView.darkTheme.of(scheme.matches)),
      // goat strings use straight quotes; stop mobile keyboards from curling them.
      EditorView.contentAttributes.of({
        "aria-label": "goat code",
        spellcheck: "false",
        autocorrect: "off",
        autocapitalize: "off",
      }),
      ...(compiler ? withCompiler(compiler) : []),
    ],
  });
  scheme.addEventListener("change", () =>
    view.dispatch({ effects: darkness.reconfigure(EditorView.darkTheme.of(scheme.matches)) }),
  );
  return {
    text: () => view.state.doc.toString(),
    setText: (text) => view.dispatch({ changes: { from: 0, to: view.state.doc.length, insert: text } }),
  };
}
