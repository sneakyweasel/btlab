/** Ember / sea for O and E. Flare / plunge for a steep climb or drop. */

export const EMBER = "#c45c26";
export const SEA = "#1f6f6a";
export const FLARE = "#e8932a";
export const PLUNGE = "#14525c";

const STEEP_LOG10 = 2.2;

function parseHex(color: string): [number, number, number] {
  const hex = color.replace("#", "");
  return [
    Number.parseInt(hex.slice(0, 2), 16),
    Number.parseInt(hex.slice(2, 4), 16),
    Number.parseInt(hex.slice(4, 6), 16),
  ];
}

export function mixHex(from: string, to: string, amount: number): string {
  const t = Math.max(0, Math.min(1, amount));
  const a = parseHex(from);
  const b = parseHex(to);
  const channel = (index: number) => Math.round(a[index] + (b[index] - a[index]) * t);
  return `#${[0, 1, 2].map((index) => channel(index).toString(16).padStart(2, "0")).join("")}`;
}

/** Path color for one Juggler step. Large |Δ log10| runs hotter or deeper. */
export function stepPathColor(dLog10: number): string {
  if (dLog10 >= 0) return mixHex(EMBER, FLARE, dLog10 / STEEP_LOG10);
  return mixHex(SEA, PLUNGE, -dLog10 / STEEP_LOG10);
}
