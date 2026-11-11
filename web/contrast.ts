// WCAG 2.x contrast, shared by the contrast test and the theme check: a colour
// the editor shows text in has to be readable on every surface the text sits on.

export const AA = 4.5;

export type Surfaces = Record<"panel" | "selection", string>;

// The surfaces index.html paints behind code, per colour scheme.
export const SURFACES: Record<"light" | "dark", Surfaces> = {
  light: { panel: "#ffffff", selection: "#c9c9ce" },
  dark: { panel: "#222226", selection: "#3d3d5c" },
};

// "#rgb" or "#rrggbb" as "#rrggbb", or null for anything else.
export function normalizeHex(value: string): string | null {
  const match = /^#([0-9a-fA-F]{3}|[0-9a-fA-F]{6})$/.exec(value);
  if (!match) return null;
  const digits = match[1]!.toLowerCase();
  return "#" + (digits.length === 3 ? [...digits].map((c) => c + c).join("") : digits);
}

export function luminance(hex: string): number {
  const [r, g, b] = [1, 3, 5]
    .map((i) => parseInt(hex.slice(i, i + 2), 16) / 255)
    .map((c) => (c <= 0.03928 ? c / 12.92 : ((c + 0.055) / 1.055) ** 2.4)) as [number, number, number];
  return 0.2126 * r + 0.7152 * g + 0.0722 * b;
}

export function contrast(a: string, b: string): number {
  const [hi, lo] = [luminance(a), luminance(b)].sort((x, y) => y - x) as [number, number];
  return (hi + 0.05) / (lo + 0.05);
}
