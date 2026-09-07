/**
 * Run-suffix law. Display fork of
 * src/research/juggler_sequence/run_suffix_law.py
 * (Paper A Theorems 3.26–3.31, Corollaries 3.27 and 3.30).
 */

import { icbrt, lnBig } from "./map";

export const RUN_A_MIN = 1;
export const RUN_A_MAX = 16;
export const SUFFIX_MAX = 8;
export const RUN_N_MIN = 2;
export const RUN_N_MAX = 10_000_000;
export const THRESHOLD_HI = 1_000_000_000_000;

export type EnvelopeMode = "crude" | "sharp";

export type Recovery = {
  suffix: string;
  printedA: number;
  lawA: number;
  nCrude: number;
  nSharp: number;
  source: string;
};

/** Corollary 3.27 / 3.30. Shipped so the printed n_u cannot drift. */
export const RECOVERIES: readonly Recovery[] = [
  { suffix: "E", printedA: 3, lawA: 2, nCrude: 1032, nSharp: 7, source: "Lemma 3.4(v)" },
  { suffix: "EE", printedA: 4, lawA: 4, nCrude: 205, nSharp: 6, source: "Theorems 3.12, 3.21" },
  { suffix: "EOE", printedA: 3, lawA: 3, nCrude: 109, nSharp: 6, source: "Theorems 3.12, 3.21" },
  { suffix: "EEE", printedA: 6, lawA: 6, nCrude: 73, nSharp: 5, source: "Theorem 3.14" },
  { suffix: "EOEE", printedA: 5, lawA: 5, nCrude: 60, nSharp: 5, source: "Theorem 3.15" },
  { suffix: "EOOEE", printedA: 4, lawA: 4, nCrude: 45, nSharp: 5, source: "Theorem 3.16" },
  { suffix: "EOOOEE", printedA: 3, lawA: 3, nCrude: 30, nSharp: 5, source: "Theorem 3.17" },
  { suffix: "EEOE", printedA: 5, lawA: 5, nCrude: 60, nSharp: 5, source: "Theorem 3.18" },
  { suffix: "EOEOE", printedA: 4, lawA: 4, nCrude: 45, nSharp: 5, source: "Theorem 3.19" },
  { suffix: "EOOEOE", printedA: 3, lawA: 3, nCrude: 30, nSharp: 5, source: "Theorem 3.20" },
];

/** Remark 3.32 / Theorem 3.31. Shipped — the site does not enumerate the forms. */
export const EVEN_COUNT_LADDER = [
  { e: 3, bounds: [5, 3, 1], forms: 16, closedAt: 16 },
  { e: 4, bounds: [6, 5, 3, 1], forms: 186, closedAt: 16 },
  { e: 5, bounds: [8, 6, 5, 3, 1], forms: 2037, closedAt: 16 },
  { e: 6, bounds: [10, 8, 6, 5, 3, 1], forms: 25353, closedAt: 16 },
  { e: 7, bounds: [11, 10, 8, 6, 5, 3, 1], forms: 325452, closedAt: 64 },
] as const;

const LN4 = 2 * Math.LN2;

export function parseSuffix(text: string): string | null {
  const word = text.trim().toUpperCase();
  if (!word) return "";
  if (word.length > SUFFIX_MAX) return null;
  if (!/^[OE]+$/.test(word)) return null;
  if (word[0] !== "E") return null;
  return word;
}

export function suffixOddCount(suffix: string): number {
  return [...suffix].filter((letter) => letter === "O").length;
}

/** T(u) = 2^|u| / 3^{#O(u)}. Empty suffix is 1. */
export function suffixExponentValue(suffix: string): number {
  return 2 ** suffix.length / 3 ** suffixOddCount(suffix);
}

export function formatT(suffix: string): string {
  if (!suffix) return "1";
  const odds = suffixOddCount(suffix);
  const numer = 2 ** suffix.length;
  if (odds === 0) return String(numer);
  return `${numer}/${3 ** odds}`;
}

export function forwardExponent(a: number): number {
  return (3 / 2) ** a;
}

/** ln of Lemma 3.24: 4 (n/4)^{(3/2)^a}. */
export function forwardBoundLn(n: number, a: number): number {
  return LN4 + forwardExponent(a) * (Math.log(n) - LN4);
}

export function sharpExponents(a: number): [number, number] {
  return [3 * (3 ** a - 2 ** a), 2 * 3 ** a - 3 * 2 ** a];
}

/**
 * Integer B(u) of Lemma 3.25. The state entering the suffix is strictly less.
 * Recurrence matches run_suffix_law.exact_backward_envelope.
 */
export function exactBackwardEnvelope(suffix: string, n: number): bigint {
  if (!Number.isInteger(n) || n < 1) {
    throw new Error("exactBackwardEnvelope needs a positive integer n");
  }
  let bound = BigInt(n) + 1n;
  for (let index = suffix.length - 1; index >= 0; index -= 1) {
    const letter = suffix[index];
    if (letter === "E") {
      bound *= bound;
    } else if (letter === "O") {
      bound = icbrt(bound * bound - 1n) + 1n;
    } else {
      throw new Error("suffix letters must be O or E");
    }
  }
  return bound;
}

export function backwardLn(suffix: string, n: number): number {
  return lnBig(exactBackwardEnvelope(suffix, n));
}

export function leastRun(suffix: string, aMax = RUN_A_MAX): number | null {
  const tee = suffixExponentValue(suffix);
  for (let a = 1; a <= aMax; a += 1) {
    if (forwardExponent(a) > tee) return a;
  }
  return null;
}

/** θ = 1 − T/P. How much room the leading exponents leave. */
export function margin(a: number, suffix: string): number {
  return 1 - suffixExponentValue(suffix) / forwardExponent(a);
}

export function floorConstant(n: number): number {
  return LN4 / Math.log(n);
}

export function tailExpanding(a: number, suffix: string): boolean {
  const odds = a + suffixOddCount(suffix);
  const length = a + suffix.length;
  return 3 ** odds > 2 ** length;
}

export function excludedCrude(a: number, suffix: string, n: number): boolean {
  if (!suffix) return false;
  if (forwardExponent(a) <= suffixExponentValue(suffix)) return false;
  return forwardBoundLn(n, a) >= backwardLn(suffix, n);
}

export function excludedSharp(a: number, suffix: string, n: number): boolean {
  if (!suffix) return false;
  if (forwardExponent(a) <= suffixExponentValue(suffix)) return false;
  const [ex, wye] = sharpExponents(a);
  const right = 2 ** a * backwardLn(suffix, n) + wye * Math.log(n + 1);
  return right <= ex * Math.log(n);
}

function searchThreshold(pred: (n: number) => boolean, hi = THRESHOLD_HI): number | null {
  if (!pred(hi)) return null;
  let lo = 2;
  let high = hi;
  while (lo < high) {
    const mid = Math.floor((lo + high) / 2);
    if (pred(mid)) high = mid;
    else lo = mid + 1;
  }
  return lo;
}

export function thresholdCrude(a: number, suffix: string): number | null {
  if (!suffix || forwardExponent(a) <= suffixExponentValue(suffix)) return null;
  return searchThreshold((n) => excludedCrude(a, suffix, n));
}

export function thresholdSharp(a: number, suffix: string): number | null {
  if (!suffix || forwardExponent(a) <= suffixExponentValue(suffix)) return null;
  return searchThreshold((n) => excludedSharp(a, suffix, n));
}

export function recoveryOf(suffix: string): Recovery | null {
  return RECOVERIES.find((row) => row.suffix === suffix) ?? null;
}

/** Printed n_u when the pair is a Corollary 3.27 row at its law a; else a live search. */
export function resolveThreshold(
  a: number,
  suffix: string,
  mode: EnvelopeMode,
): number | null {
  const row = recoveryOf(suffix);
  if (row && row.lawA === a) return mode === "crude" ? row.nCrude : row.nSharp;
  return mode === "crude" ? thresholdCrude(a, suffix) : thresholdSharp(a, suffix);
}

export type RunSuffixView = {
  suffix: string;
  a: number;
  n: number;
  mode: EnvelopeMode;
  T: number;
  TLabel: string;
  P: number;
  tailExpanding: boolean;
  leastA: number | null;
  margin: number;
  floorCost: number;
  nCrude: number | null;
  nSharp: number | null;
  nThreshold: number | null;
  fires: boolean;
  wholeWord: boolean;
  recovery: Recovery | null;
};

export function runSuffixView(
  suffix: string,
  a: number,
  n: number,
  mode: EnvelopeMode,
): RunSuffixView {
  const wholeWord = suffix.length === 0;
  const recovery = recoveryOf(suffix);
  const nCrude = wholeWord ? null : resolveThreshold(a, suffix, "crude");
  const nSharp = wholeWord ? null : resolveThreshold(a, suffix, "sharp");
  const nThreshold = mode === "crude" ? nCrude : nSharp;
  const fires = wholeWord
    ? false
    : mode === "crude"
      ? excludedCrude(a, suffix, n)
      : excludedSharp(a, suffix, n);
  return {
    suffix,
    a,
    n,
    mode,
    T: suffixExponentValue(suffix),
    TLabel: formatT(suffix),
    P: forwardExponent(a),
    tailExpanding: tailExpanding(a, suffix),
    leastA: leastRun(suffix),
    margin: margin(a, suffix),
    floorCost: floorConstant(n),
    nCrude,
    nSharp,
    nThreshold,
    fires,
    wholeWord,
    recovery,
  };
}
