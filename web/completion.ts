// Completion for the playground editor, from the lexer alone: it tokenizes
// half-typed code, so no parse or error recovery is needed. Offers the grammar's
// keywords, the host's functions and tags, and the names the program has bound
// before the cursor. `completionsAt` is plain data in, data out; only
// `goatCompletions` knows about CodeMirror.

import type { Completion, CompletionContext, CompletionResult, CompletionSource } from "@codemirror/autocomplete";
import type { Token, Word } from "./compile.ts";

const NAME = String.raw`\p{XID_Start}\p{XID_Continue}*`;
const NOT_AFTER_NAME = String.raw`(?<![\p{XID_Continue}.])`;

// Every way a name gets bound, by its text: `x = …`, a `program(a, b)`
// parameter, a `for` variable, and a name in the pattern of a `match` arm. A
// tag declaration's `tag Shape = …` is not a binding.
const BINDING = new RegExp(String.raw`${NOT_AFTER_NAME}(?<!\btag\s+)(${NAME})\s*=(?!=)`, "gu");
const PARAMETERS = new RegExp(String.raw`\b(?:program|function)\s*\(([^)]*)\)`, "gu");
const FOR_VARIABLE = new RegExp(String.raw`\bfor\s+(${NAME})\s+(?:from|in)\b`, "gu");
const ARM_PATTERN = new RegExp(String.raw`(?<!\p{XID_Continue})(?:${NAME})\s*\(([^()]*)\)\s*then\b|\[([^\]]*)\]\s*then\b`, "gu");
const NAMES_IN = new RegExp(String.raw`(?<!\p{XID_Continue})${NAME}`, "gu");
const PREFIX = /\p{XID_Continue}*$/u;
const STARTS_A_NAME = /^\p{XID_Start}/u;

// Comments and strings blanked out (length-preserving), so the patterns above
// cannot match inside them.
function blankOut(text: string, tokens: Token[]): string {
  let out = "";
  let at = 0;
  for (const { kind, from, to } of tokens) {
    if ((kind !== "comment" && kind !== "string") || from >= text.length) continue;
    out += text.slice(at, from) + " ".repeat(Math.min(to, text.length) - from);
    at = Math.min(to, text.length);
  }
  return out + text.slice(at);
}

function namesIn(text: string | undefined): string[] {
  return text === undefined ? [] : [...text.matchAll(NAMES_IN)].map((m) => m[0]);
}

// The names `before` (the source up to the cursor) binds, latest first. There
// is no scoping: a parameter of a function already closed still counts.
export function boundNames(before: string, tokens: Token[], keywords: ReadonlySet<string>): string[] {
  const text = blankOut(before, tokens);
  const found: { at: number; name: string }[] = [];
  const add = (match: RegExpMatchArray, names: string[]) =>
    found.push(...names.filter((name) => !keywords.has(name)).map((name) => ({ at: match.index!, name })));
  for (const m of text.matchAll(BINDING)) add(m, [m[1]]);
  for (const m of text.matchAll(PARAMETERS)) add(m, namesIn(m[1]));
  for (const m of text.matchAll(FOR_VARIABLE)) add(m, [m[1]]);
  for (const m of text.matchAll(ARM_PATTERN)) add(m, namesIn(m[1] ?? m[2]));
  found.sort((a, b) => b.at - a.at);
  return [...new Set(found.map((f) => f.name))];
}

export interface Completions {
  from: number;
  options: Completion[];
}

const byName = (a: Completion, b: Completion) => a.label.localeCompare(b.label);

function insideStringOrComment(tokens: Token[], cursor: number): boolean {
  return tokens.some(
    ({ kind, from, to }) =>
      (kind === "string" && from < cursor && cursor < to) || (kind === "comment" && from < cursor && cursor <= to),
  );
}

// What can be typed at `cursor` in `source`: the names bound so far, then the
// host's functions, the keywords and the tags, each starting with the word
// being typed. `tokens` are the lexer's tokens of `source`. Null where nothing
// should be offered: in a comment or string, after a `.` (a field name), or
// inside a number.
export function completionsAt(source: string, cursor: number, words: Word[], tokens: Token[]): Completions | null {
  const before = source.slice(0, cursor);
  const prefix = PREFIX.exec(before)![0];
  const from = cursor - prefix.length;
  if (insideStringOrComment(tokens, cursor)) return null;
  if (prefix && !STARTS_A_NAME.test(prefix)) return null;
  if (before[from - 1] === "." && before[from - 2] !== ".") return null;

  const keywords = new Set(words.filter((w) => w.kind === "keyword").map((w) => w.name));
  const typed = prefix.toLowerCase();
  const tagsDeclared = tokens
    .filter((t) => t.kind === "tag" && t.to <= from)
    .map((t) => source.slice(t.from, t.to));

  const groups: Completion[][] = [
    boundNames(before.slice(0, from), tokens, keywords).map((label) => ({ label, type: "variable" })),
    [...new Set(tagsDeclared)].map((label) => ({ label, type: "class" })).sort(byName),
    ...(["function", "keyword", "tag"] as const).map((kind) =>
      words
        .filter((w) => w.kind === kind)
        .map(({ name, detail }) => ({ label: name, detail: detail || undefined, type: kind === "tag" ? "class" : kind }))
        .sort(byName),
    ),
  ];
  const seen = new Set<string>();
  const options = groups
    .flat()
    .filter(({ label }) => {
      if (label === prefix || !label.toLowerCase().startsWith(typed) || seen.has(label)) return false;
      seen.add(label);
      return true;
    });
  return { from, options };
}

// Typing opens the list once a letter is typed; Ctrl-Space opens it anywhere.
export function goatCompletions(words: Word[], tokenize: (source: string) => Token[]): CompletionSource {
  return (context: CompletionContext): CompletionResult | null => {
    const source = context.state.doc.toString();
    const found = completionsAt(source, context.pos, words, tokenize(source));
    if (!found || (!context.explicit && found.from === context.pos)) return null;
    return { ...found, filter: false };
  };
}
