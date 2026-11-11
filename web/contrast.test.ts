import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";

const AA = 4.5;
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

function luminance(hex: string): number {
  const [r, g, b] = [1, 3, 5].map((i) => parseInt(hex.slice(i, i + 2), 16) / 255).map((c) =>
    c <= 0.03928 ? c / 12.92 : ((c + 0.055) / 1.055) ** 2.4
  );
  return 0.2126 * r + 0.7152 * g + 0.0722 * b;
}

function contrast(a: string, b: string): number {
  const [hi, lo] = [luminance(a), luminance(b)].sort((x, y) => y - x);
  return (hi + 0.05) / (lo + 0.05);
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

test("problems is a polite status region, not an alert", () => {
  assert.match(html, /<pre id="problems" role="status"/);
});
