// The editor's colours come from a goat program (editor/theme.goat). It runs in
// a worker under the supervisor, like the highlighter (ADR 0021), once per
// change of the theme, and draws one `Swatch` per style role: the role and its
// light and dark colours. What it says is untrusted: the host accepts only
// known roles and colours it can check and read, and writes them to the page as
// `--tok-*` custom properties. goat never touches the page.

import { AA, SURFACES, contrast, normalizeHex } from "./contrast.ts";
import { compileTheme } from "./compile.ts";
import type { Runner } from "./supervisor.ts";
import type { RawSwatch } from "./scene.ts";
import { checkColor } from "./runtime.ts";

// The roles the editor styles, as editor/theme.goat names them.
export const THEME_ROLES = ["keyword", "literal", "number", "string", "comment", "tag"] as const;
export type ThemeRole = (typeof THEME_ROLES)[number];

export const SCHEMES = ["light", "dark"] as const;
export type Scheme = (typeof SCHEMES)[number];

export type Palette = Record<ThemeRole, string>;
export type Theme = Record<Scheme, Palette>;

// What index.html paints before any theme runs, and what a role falls back to
// when the theme leaves it out or gives it a colour the host drops.
export const DEFAULT_THEME: Theme = {
  light: {
    keyword: "#4a2fb8",
    literal: "#095a80",
    number: "#095a80",
    string: "#14602b",
    comment: "#505058",
    tag: "#80400a",
  },
  dark: {
    keyword: "#b4a3ff",
    literal: "#7dd3fc",
    number: "#7dd3fc",
    string: "#7ee787",
    comment: "#b8b8c4",
    tag: "#ffb870",
  },
};

// The basic CSS colour names. Contrast can only be measured on a colour whose
// value is known, so a name outside this list has to be written as a code.
const NAMED = new Map<string, string>(Object.entries({
  black: "#000000",
  silver: "#c0c0c0",
  gray: "#808080",
  grey: "#808080",
  white: "#ffffff",
  maroon: "#800000",
  red: "#ff0000",
  purple: "#800080",
  fuchsia: "#ff00ff",
  green: "#008000",
  lime: "#00ff00",
  olive: "#808000",
  yellow: "#ffff00",
  navy: "#000080",
  blue: "#0000ff",
  teal: "#008080",
  aqua: "#00ffff",
  orange: "#ffa500",
}));

function resolveColor(text: string): string | null {
  try {
    checkColor(text);
  } catch {
    return null;
  }
  return normalizeHex(text) ?? NAMED.get(text.toLowerCase()) ?? null;
}

export type ThemeOutcome = { ok: true; theme: Theme; notes: string[] } | { ok: false; message: string };

// The theme the program's swatches describe. A swatch for a role that does not
// exist is dropped, and so is one colour that is not an allowed colour the host
// can read; that role then keeps its default in that palette. A colour that is
// hard to read on the editor's background rejects the whole theme.
export function acceptSwatches(swatches: unknown): ThemeOutcome {
  const theme: Theme = { light: { ...DEFAULT_THEME.light }, dark: { ...DEFAULT_THEME.dark } };
  const written = new Map<string, string>();
  const notes: string[] = [];
  for (const swatch of Array.isArray(swatches) ? (swatches as Array<Partial<RawSwatch> | null>) : []) {
    if (typeof swatch !== "object" || swatch === null) continue;
    const role = THEME_ROLES.find((known) => known === swatch.role);
    if (role === undefined) continue;
    for (const scheme of SCHEMES) {
      const color = swatch[scheme];
      const hex = typeof color === "string" ? resolveColor(color) : null;
      if (typeof color !== "string" || hex === null) {
        notes.push(
          `Ignored the ${scheme} ${role} colour ${JSON.stringify(String(color).slice(0, 32))}: use a name like "purple" or a code like "#4a2fb8".`,
        );
        continue;
      }
      theme[scheme][role] = hex;
      written.set(`${scheme} ${role}`, color);
    }
  }
  const problems: string[] = [];
  for (const scheme of SCHEMES) {
    for (const role of THEME_ROLES) {
      for (const [surface, background] of Object.entries(SURFACES[scheme])) {
        const ratio = contrast(theme[scheme][role], background);
        if (ratio >= AA) continue;
        const wording = written.get(`${scheme} ${role}`) ?? theme[scheme][role];
        problems.push(
          `The ${scheme} ${role} colour ${JSON.stringify(wording)} is hard to read on the ${surface} (${ratio.toFixed(1)} to 1; it needs ${AA} to 1). Try a ${scheme === "light" ? "darker" : "lighter"} one.`,
        );
        break;
      }
    }
  }
  if (problems.length > 0) return { ok: false, message: [...problems, "Your last theme is still in use."].join("\n") };
  return { ok: true, theme, notes };
}

// The custom properties that paint `palette`.
export function themeVariables(palette: Palette): Record<string, string> {
  return Object.fromEntries(THEME_ROLES.map((role) => [`--tok-${role}`, palette[role]]));
}

export interface StyleTarget {
  style: { setProperty(name: string, value: string): void };
}

export interface SchemeQuery {
  matches: boolean;
  addEventListener(type: "change", listener: () => void): void;
}

// Paints themes onto `root`: the palette for the page's colour scheme now, and
// again whenever the scheme flips.
export function themeApplier(root: StyleTarget, dark: SchemeQuery): (theme: Theme) => void {
  let current: Theme | undefined;
  const paint = () => {
    if (!current) return;
    const variables = themeVariables(current[dark.matches ? "dark" : "light"]);
    for (const [name, value] of Object.entries(variables)) root.style.setProperty(name, value);
  };
  dark.addEventListener("change", paint);
  return (theme) => {
    current = theme;
    paint();
  };
}

// A theme program that has not answered by then is dropped; a program stuck
// inside a call is stopped sooner by the supervisor.
export const THEME_BUDGET_MS = 2000;

export interface ThemeEngineOptions {
  compiler: WebAssembly.Module;
  runner: Runner;
  apply(theme: Theme): void;
  budgetMs?: number;
}

// Runs theme programs. Each distinct source runs once, however often it is
// asked for or painted afterwards; a theme that does not compile, traps, hangs
// or is hard to read leaves the theme in use as it was.
export class ThemeEngine {
  #options: ThemeEngineOptions;
  #queue: Promise<unknown> = Promise.resolve();
  #last: { source: string; outcome: ThemeOutcome } | undefined;

  constructor(options: ThemeEngineOptions) {
    this.#options = options;
  }

  change(source: string): Promise<ThemeOutcome> {
    const next = this.#queue.then(() => this.#evaluate(source));
    this.#queue = next.catch(() => {});
    return next;
  }

  // Back to the default theme.
  reset(): void {
    this.#last = undefined;
    this.#options.apply(DEFAULT_THEME);
  }

  async #evaluate(source: string): Promise<ThemeOutcome> {
    if (this.#last?.source === source) return this.#last.outcome;
    let outcome: ThemeOutcome;
    try {
      outcome = await this.#run(source);
    } catch (e) {
      outcome = { ok: false, message: `The theme could not run: ${e instanceof Error ? e.message : String(e)}` };
    }
    if (outcome.ok) {
      this.#last = { source, outcome };
      this.#options.apply(outcome.theme);
    }
    return outcome;
  }

  async #run(source: string): Promise<ThemeOutcome> {
    const compiled = await compileTheme(this.#options.compiler, source);
    if (!compiled.ok) return { ok: false, message: `${compiled.diagnostics}\nYour last theme is still in use.` };
    const { runner, budgetMs = THEME_BUDGET_MS } = this.#options;
    let timer: ReturnType<typeof setTimeout> | undefined;
    try {
      const swatches = await new Promise<RawSwatch[] | string>((resolve) => {
        timer = setTimeout(() => resolve("The theme never answered: its draw must list the swatches."), budgetMs);
        runner.start(
          { mode: "theme", module: compiled.module },
          { onOutput: () => {}, onSwatches: resolve, onFailed: resolve },
        );
      });
      if (typeof swatches === "string") return { ok: false, message: `${swatches}\nYour last theme is still in use.` };
      return acceptSwatches(swatches);
    } finally {
      clearTimeout(timer);
      runner.stop();
    }
  }
}

const STORAGE_KEY = "goat.theme";

// A kid's edited theme in the browser's storage. Storage can be missing, full
// or blocked, and the editor works without it.
export const themeStore = {
  load(storage: Pick<Storage, "getItem"> | undefined): string | null {
    try {
      return storage?.getItem(STORAGE_KEY) ?? null;
    } catch {
      return null;
    }
  },
  save(storage: Pick<Storage, "setItem" | "removeItem"> | undefined, source: string | null): void {
    try {
      if (source === null) storage?.removeItem(STORAGE_KEY);
      else storage?.setItem(STORAGE_KEY, source);
    } catch {}
  },
};
