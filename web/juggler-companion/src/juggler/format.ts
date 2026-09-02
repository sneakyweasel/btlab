import { bitLength } from "./map";

export function formatInt(value: bigint | number): string {
  if (typeof value === "bigint" && bitLength(value) > 80) {
    const exp = Math.round((bitLength(value) - 1) * Math.LOG10E * Math.LN2);
    return `~10^${exp}`;
  }
  const text = value.toString();
  if (text.length <= 18) return text;
  return `${text.slice(0, 6)}…${text.slice(-4)} (${text.length} digits)`;
}

export function formatGrouped(value: number): string {
  return value.toLocaleString("en-US");
}

export function parsePositiveInt(text: string): bigint | null {
  const trimmed = text.trim();
  if (!/^[1-9]\d*$/.test(trimmed)) return null;
  try {
    return BigInt(trimmed);
  } catch {
    return null;
  }
}
