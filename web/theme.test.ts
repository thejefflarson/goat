// The theme end to end in one process: the real worker core stands in for the
// Web Worker behind the real supervisor, so editor/theme.goat runs for real and
// its swatches travel the whole way to the page's custom properties.

import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import type { FromWorker, ToWorker } from "./protocol.ts";
import { Supervisor, type WorkerLike } from "./supervisor.ts";
import {
  DEFAULT_THEME,
  SCHEMES,
  THEME_ROLES,
  type Theme,
  ThemeEngine,
  acceptSwatches,
  themeApplier,
  themeStore,
  themeVariables,
} from "./theme.ts";
import { createWorkerCore } from "./worker-core.ts";

const compiler = await WebAssembly.compile(
  readFileSync(new URL("../target/wasm32-unknown-unknown/release/goat_web.wasm", import.meta.url)),
);
const source = readFileSync(new URL("../editor/theme.goat", import.meta.url), "utf8");
const page = readFileSync(new URL("./index.html", import.meta.url), "utf8");

const capable = { crossOriginIsolated: true, SharedArrayBuffer, Worker: class {}, OffscreenCanvas: class {} };

function inProcessWorker(): WorkerLike {
  let closed = false;
  const worker: WorkerLike = {
    onmessage: null,
    onerror: null,
    postMessage: (message: ToWorker) => void core.handle(message),
    terminate: () => {
      closed = true;
    },
  };
  const core = createWorkerCore({
    post: (message: FromWorker) => {
      if (!closed) worker.onmessage?.({ data: message });
    },
    raf: () => 0,
    cancelRaf: () => {},
    now: () => performance.now(),
  });
  return worker;
}

// An engine over real workers, counting how many theme programs it started and
// recording each theme it painted.
function engine(budgetMs?: number) {
  let started = 0;
  const painted: Theme[] = [];
  const supervisor = new Supervisor(
    {
      spawn: () => {
        started++;
        return inProcessWorker();
      },
      surface: () => ({ width: 1, height: 1 }) as OffscreenCanvas,
      now: () => performance.now(),
      every: () => () => {},
    },
    capable,
  );
  const themes = new ThemeEngine({ compiler, runner: supervisor, apply: (theme) => void painted.push(theme), budgetMs });
  return { themes, painted, started: () => started };
}

// The `--tok-*` values of the two :root blocks in index.html.
function cssPalettes(): Theme {
  const [light, dark] = [...page.matchAll(/:root \{([^}]*)\}/g)].map((m) => m[1]!);
  const read = (block: string) =>
    Object.fromEntries(
      THEME_ROLES.map((role) => [role, new RegExp(`--tok-${role}:\\s*(#[0-9a-f]{6})`).exec(block)![1]]),
    ) as Theme["light"];
  return { light: read(light!), dark: read(dark!) };
}

const recolored = (role: string, color: string, palette = "light") =>
  source.replace(new RegExp(`(role: "${role}", light: "[^"]*", dark: "[^"]*")`), (line) =>
    line.replace(new RegExp(`${palette}: "[^"]*"`), `${palette}: "${color}"`),
  );

test("the default theme is today's palette, exactly", async () => {
  const { themes, painted } = engine();
  const outcome = await themes.change(source);
  assert.ok(outcome.ok);
  assert.deepEqual(outcome.theme, cssPalettes());
  assert.deepEqual(outcome.theme, DEFAULT_THEME);
  assert.deepEqual(outcome.notes, []);
  assert.deepEqual(painted, [DEFAULT_THEME]);
});

test("editing one colour re-colours that role and nothing else, with no reload", async () => {
  const { themes, painted } = engine();
  const outcome = await themes.change(recolored("keyword", "#000000"));
  assert.ok(outcome.ok);
  assert.equal(outcome.theme.light.keyword, "#000000");
  assert.deepEqual(outcome.theme.dark, DEFAULT_THEME.dark);
  assert.deepEqual({ ...outcome.theme.light, keyword: "" }, { ...DEFAULT_THEME.light, keyword: "" });
  assert.equal(painted.at(-1)?.light.keyword, "#000000");
});

test("a named colour is read as the colour it names", async () => {
  const { themes } = engine();
  const outcome = await themes.change(recolored("string", "Navy"));
  assert.ok(outcome.ok);
  assert.equal(outcome.theme.light.string, "#000080");
});

test("a theme that does not compile keeps the previous theme and shows the checker's diagnostic", async () => {
  const { themes, painted } = engine();
  await themes.change(recolored("keyword", "#000000"));
  const outcome = await themes.change(source.replace("Swatch({role: \"keyword\"", "Swatch({rol: \"keyword\""));
  assert.ok(!outcome.ok);
  assert.match(outcome.message, /rol/);
  assert.match(outcome.message, /\^/);
  assert.match(outcome.message, /last theme is still in use/);
  assert.equal(painted.length, 1);
  assert.equal(painted[0]!.light.keyword, "#000000");
});

test("a colour that is hard to read rejects the theme, naming the role and the palette", async () => {
  const { themes, painted } = engine();
  const outcome = await themes.change(recolored("comment", "#eeeeee"));
  assert.ok(!outcome.ok);
  assert.match(outcome.message, /light comment colour "#eeeeee" is hard to read/);
  assert.match(outcome.message, /darker/);
  assert.deepEqual(painted, []);
});

test("a colour outside the allowlist or the names the host knows is dropped and the role keeps its default", async () => {
  const { themes } = engine();
  const outcome = await themes.change(recolored("number", "papayawhip").replace('"#14602b"', '"red;}body{x:y"'));
  assert.ok(outcome.ok);
  assert.deepEqual(outcome.theme, DEFAULT_THEME);
  assert.equal(outcome.notes.length, 2);
  assert.match(outcome.notes[0]!, /light number colour "papayawhip"/);
});

test("a name only an object inherits, like constructor, is an unknown colour, not a crash", async () => {
  const { themes } = engine();
  const outcome = await themes.change(recolored("number", "constructor"));
  assert.ok(outcome.ok);
  assert.deepEqual(outcome.theme, DEFAULT_THEME);
  assert.match(outcome.notes[0]!, /light number colour "constructor"/);
});

test("a program that never answers is dropped after its budget instead of hanging the queue", async () => {
  const painted: Theme[] = [];
  let stopped = 0;
  const silent = { start: () => {}, stop: () => void stopped++ };
  const themes = new ThemeEngine({ compiler, runner: silent, apply: (theme) => void painted.push(theme), budgetMs: 20 });
  const outcome = await themes.change(source);
  assert.ok(!outcome.ok);
  assert.match(outcome.message, /never answered/);
  assert.match(outcome.message, /last theme is still in use/);
  assert.equal(stopped, 1);
  assert.deepEqual(painted, []);
});

test("a theme that traps keeps the previous theme and says why", async () => {
  const { themes, painted } = engine();
  await themes.change(source);
  const outcome = await themes.change(source.replace("draw = program(model) do", 'draw = program(model) do\n  trap("no colours today");'));
  assert.ok(!outcome.ok);
  assert.match(outcome.message, /no colours today/);
  assert.equal(painted.length, 1);
});

test("a theme is evaluated once per change, however often it is asked for or painted", async () => {
  const { themes, started } = engine();
  await themes.change(source);
  await themes.change(source);
  assert.equal(started(), 1);
  await themes.change(recolored("keyword", "#000000"));
  assert.equal(started(), 2);
  await Promise.all([themes.change(source), themes.change(source)]);
  assert.equal(started(), 3);
});

test("resetting paints the default theme again", async () => {
  const { themes, painted } = engine();
  await themes.change(recolored("keyword", "#000000"));
  themes.reset();
  assert.deepEqual(painted.at(-1), DEFAULT_THEME);
  await themes.change(recolored("keyword", "#000000"));
  assert.equal(painted.at(-1)?.light.keyword, "#000000");
});

test("swatches for unknown roles and malformed shapes are dropped", () => {
  const swatch = (role: unknown, light: unknown, dark: unknown) => ({ role, light, dark });
  const outcome = acceptSwatches([
    swatch("plain", "#000000", "#ffffff"),
    swatch("__proto__", "#000000", "#ffffff"),
    swatch(3, "#000000", "#ffffff"),
    null,
    "keyword",
    swatch("string", "#000000", "#ffffff"),
  ]);
  assert.ok(outcome.ok);
  assert.deepEqual(outcome.theme.light, { ...DEFAULT_THEME.light, string: "#000000" });
  assert.deepEqual(outcome.theme.dark, { ...DEFAULT_THEME.dark, string: "#ffffff" });
  assert.deepEqual(acceptSwatches("not a list"), { ok: true, theme: DEFAULT_THEME, notes: [] });
});

test("a bad colour in one palette leaves the other palette's colour in place", () => {
  const outcome = acceptSwatches([{ role: "keyword", light: 5, dark: "#ffffff" }]);
  assert.ok(outcome.ok);
  assert.equal(outcome.theme.light.keyword, DEFAULT_THEME.light.keyword);
  assert.equal(outcome.theme.dark.keyword, "#ffffff");
  assert.equal(outcome.notes.length, 1);
});

test("a colour is checked against every surface of its palette", () => {
  const dark = acceptSwatches([{ role: "keyword", light: "#000000", dark: "#3d3d5c" }]);
  assert.ok(!dark.ok);
  assert.match(dark.message, /dark keyword colour "#3d3d5c" is hard to read on the panel/);
  assert.match(dark.message, /lighter/);
  // #707070 reads on the white panel but not on the light selection.
  const light = acceptSwatches([{ role: "keyword", light: "#707070", dark: "#ffffff" }]);
  assert.ok(!light.ok);
  assert.match(light.message, /light keyword colour "#707070" is hard to read on the selection/);
});

test("only validated hex codes reach the page's custom properties", () => {
  for (const scheme of SCHEMES) {
    for (const [name, value] of Object.entries(themeVariables(DEFAULT_THEME[scheme]))) {
      assert.match(name, /^--tok-(keyword|literal|number|string|comment|tag)$/);
      assert.match(value, /^#[0-9a-f]{6}$/);
    }
  }
});

test("the applier paints the palette for the page's scheme, and again when the scheme flips", () => {
  const painted = new Map<string, string>();
  let flip = () => {};
  const query = { matches: false, addEventListener: (_: "change", listener: () => void) => void (flip = listener) };
  const apply = themeApplier({ style: { setProperty: (name, value) => void painted.set(name, value) } }, query);
  apply(DEFAULT_THEME);
  assert.equal(painted.get("--tok-keyword"), DEFAULT_THEME.light.keyword);
  query.matches = true;
  flip();
  assert.equal(painted.get("--tok-keyword"), DEFAULT_THEME.dark.keyword);
  assert.equal(painted.size, THEME_ROLES.length);
});

test("storage failures are survivable", () => {
  const broken = {
    getItem: () => {
      throw new Error("blocked");
    },
    setItem: () => {
      throw new Error("full");
    },
    removeItem: () => {
      throw new Error("blocked");
    },
  };
  assert.equal(themeStore.load(broken), null);
  assert.doesNotThrow(() => themeStore.save(broken, "x"));
  assert.doesNotThrow(() => themeStore.save(broken, null));
  assert.equal(themeStore.load(undefined), null);
  const kept = new Map<string, string>();
  const storage = {
    getItem: (key: string) => kept.get(key) ?? null,
    setItem: (key: string, value: string) => void kept.set(key, value),
    removeItem: (key: string) => void kept.delete(key),
  };
  themeStore.save(storage, "theme");
  assert.equal(themeStore.load(storage), "theme");
  themeStore.save(storage, null);
  assert.equal(themeStore.load(storage), null);
});
