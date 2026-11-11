import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import { AA, SURFACES, contrast } from "./contrast.ts";

const roles = ["keyword", "literal", "number", "string", "comment", "tag"];

const html = readFileSync(new URL("./index.html", import.meta.url), "utf8");
const [lightBlock, darkBlock] = [...html.matchAll(/:root \{([^}]*)\}/g)].map((m) => m[1]);

function vars(block: string): Map<string, string> {
  return new Map(
    [...block.matchAll(/--([\w-]+):\s*#([0-9a-fA-F]{3}|[0-9a-fA-F]{6})\b/g)].map(([, name, hex]) => [
      name,
      "#" + (hex.length === 3 ? [...hex].map((c) => c + c).join("") : hex),
    ]),
  );
}

const light = vars(lightBlock);
const modes = { light, dark: new Map([...light, ...vars(darkBlock)]) };

for (const [mode, colors] of Object.entries(modes)) {
  for (const surface of ["panel", "selection"]) {
    for (const role of roles) {
      test(`${mode}: tok-${role} on ${surface} meets WCAG AA`, () => {
        const fg = colors.get(`tok-${role}`);
        const bg = colors.get(surface);
        assert.ok(fg && bg, `missing --tok-${role} or --${surface}`);
        const ratio = contrast(fg, bg);
        assert.ok(ratio >= AA, `${fg} on ${bg} is ${ratio.toFixed(2)}:1, need ${AA}:1`);
      });
    }
  }
}

test("the contrast function matches the WCAG reference values", () => {
  assert.equal(contrast("#000000", "#ffffff").toFixed(2), "21.00");
  assert.equal(contrast("#777777", "#ffffff").toFixed(2), "4.48");
});

test("editor fallbacks match the light-mode tokens", () => {
  const editor = readFileSync(new URL("./editor.ts", import.meta.url), "utf8");
  for (const role of roles) {
    const fallback = editor.match(new RegExp(`var\\(--tok-${role}, (#[0-9a-fA-F]{6})\\)`))?.[1];
    assert.equal(fallback, light.get(`tok-${role}`), `tok-${role} fallback`);
  }
});

test("the theme check's surfaces are the ones the page paints", () => {
  assert.equal(SURFACES.light.panel, light.get("panel"));
  assert.equal(SURFACES.light.selection, light.get("selection"));
  assert.equal(SURFACES.dark.panel, modes.dark.get("panel"));
  assert.equal(SURFACES.dark.selection, modes.dark.get("selection"));
});

test("problems is a polite status region, not an alert", () => {
  assert.match(html, /<pre id="problems" role="status"/);
});
