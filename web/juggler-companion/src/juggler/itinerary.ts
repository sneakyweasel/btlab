/**
 * Itinerary algebra. Display fork of
 * src/research/juggler_sequence/power_itineraries.py and cycle_itinerary.py.
 */

import { CYCLE_WORD_MAX, SLACK_BITS, WORD_MAX } from "./constants";
import { bitLength, floorPower, letterOf, powInt } from "./map";

export type Regime = "contracting" | "expanding" | "critical" | "empty";

export function parseItinerary(text: string, max = WORD_MAX): string | null {
  const word = text.trim().toUpperCase();
  if (!word) return "";
  if (word.length > max) return null;
  if (!/^[OE]+$/.test(word)) return null;
  return word;
}

export function oddCount(word: string): number {
  return [...word].filter((letter) => letter === "O").length;
}

export function evenCount(word: string): number {
  return [...word].filter((letter) => letter === "E").length;
}

export function regimeOf(length: number, odds: number): Regime {
  if (length <= 0) return "empty";
  const left = 3n ** BigInt(Math.max(odds, 0));
  const right = 2n ** BigInt(length);
  if (left < right) return "contracting";
  if (left > right) return "expanding";
  return "critical";
}

export function idealExponentApprox(odds: number, length: number): number {
  if (length <= 0) return 1;
  return Math.exp(odds * Math.log(3) - length * Math.log(2));
}

export function expanding(word: string): boolean {
  return 2 ** word.length < 3 ** oddCount(word);
}

export function surplus(word: string): number {
  return 3 ** oddCount(word) - 2 ** word.length;
}

export function followsItinerary(n: bigint, word: string): boolean {
  let current = n;
  for (const letter of word) {
    if (letter !== letterOf(current)) return false;
    current = floorPower(current);
  }
  return true;
}

export function imageAfter(n: bigint, word: string): bigint {
  let current = n;
  for (const _letter of word) {
    current = floorPower(current);
  }
  return current;
}

export function firstFail(
  n: bigint,
  word: string,
): { index: number; state: bigint } | null {
  let current = n;
  for (let index = 0; index < word.length; index += 1) {
    if (word[index] !== letterOf(current)) {
      return { index, state: current };
    }
    current = floorPower(current);
  }
  return null;
}

export function rotateItinerary(word: string, shift: number): string {
  if (!word) return "";
  const n = word.length;
  const k = ((shift % n) + n) % n;
  return word.slice(k) + word.slice(0, k);
}

export function parseCycleItinerary(text: string): string | null {
  return parseItinerary(text, CYCLE_WORD_MAX);
}

export function localDefect(n: bigint): bigint {
  const y = floorPower(n);
  if (n % 2n === 0n) return n - y * y;
  return n * n * n - y * y;
}

function lnBig(n: bigint): number {
  if (n <= 0n) return Number.NEGATIVE_INFINITY;
  const bits = bitLength(n);
  if (bits <= 53) return Math.log(Number(n));
  const hex = n.toString(16);
  const take = Math.min(hex.length, 13);
  const lead = Number.parseInt(hex.slice(0, take), 16);
  return Math.log(lead) + (hex.length - take) * 4 * Math.LN2;
}

/** Finite stand-in for SVG / Number display. Exact below 53 bits. */
export function plotMagnitude(n: bigint): number {
  const bits = bitLength(n);
  if (bits <= 53) return Number(n);
  return 2 ** Math.min(lnBig(n) / Math.LN2, 1023);
}

function plotFromLn(ln: number): number {
  if (!Number.isFinite(ln)) return Number.NaN;
  return Math.exp(Math.min(Math.max(ln, -700), 700));
}

/** Value-space ceiling n^{3^o / 2^L}. Length 0 is n itself. */
export function envelopeCeilingApprox(n: bigint, odds: number, length: number): number {
  if (n <= 0n) return 0;
  if (length <= 0) return plotMagnitude(n);
  return plotFromLn(idealExponentApprox(odds, length) * lnBig(n));
}

/** Log-slack 3^o ln n − 2^k ln image. */
export function envelopeLogSlack(
  n: bigint,
  image: bigint,
  k: number,
  o: number,
): number {
  if (k < 0 || o < 0) {
    throw new Error("envelopeLogSlack requires nonnegative exponents");
  }
  if (n <= 0n || image <= 0n) return Number.NaN;
  return 3 ** o * lnBig(n) - 2 ** k * lnBig(image);
}

/** 1 − image^{2^k} / n^{3^o}, or NaN if the logs blow up. */
export function envelopeRelativeRoom(
  n: bigint,
  image: bigint,
  k: number,
  o: number,
): number {
  const slack = envelopeLogSlack(n, image, k, o);
  if (!Number.isFinite(slack)) return Number.NaN;
  if (slack <= 0) return 0;
  return -Math.expm1(-slack);
}

export type EnvelopeSeries = {
  walk: number[];
  ceiling: number[];
};

/** Per-step walk and ceiling n^{3^{o_k}/2^k} for the SVG. */
export function envelopeSeries(n: bigint, states: readonly bigint[]): EnvelopeSeries {
  const walk: number[] = [];
  const ceiling: number[] = [];
  let odds = 0;
  for (let step = 0; step < states.length; step += 1) {
    const state = states[step];
    walk.push(plotMagnitude(state));
    ceiling.push(envelopeCeilingApprox(n, odds, step));
    if (state % 2n === 1n) odds += 1;
  }
  return { walk, ceiling };
}

/** Envelope slack Δ = n^{3^o} − image^{2^k}, or null if bits blow up. */
export function envelopeSlack(
  n: bigint,
  image: bigint,
  k: number,
  o: number,
  bitLimit = SLACK_BITS,
): bigint | null {
  if (k < 0 || o < 0) {
    throw new Error("envelopeSlack requires nonnegative exponents");
  }
  const leftBits = Math.max(1, 3 ** o) * Math.max(1, bitLength(n));
  const rightBits = Math.max(1, 1 << k) * Math.max(1, bitLength(image));
  if (leftBits > bitLimit || rightBits > bitLimit) return null;
  return powInt(n, 3 ** o) - powInt(image, 1 << k);
}

export function compareImage(image: bigint, n: bigint): "<" | ">" | "=" {
  if (image < n) return "<";
  if (image > n) return ">";
  return "=";
}

export function oMinForLength(length: number): number | null {
  if (length < 1) return null;
  return Math.floor((length * Math.LN2) / Math.log(3)) + 1;
}

export type CycleSeamKind = "OE|OO" | "EE|OO" | "other";

export type CycleMinShape = {
  startsOO: boolean;
  endsE: boolean;
  evenCount: number;
  oddCount: number;
  evenCountGe4: boolean;
  oddCountGe7: boolean;
  lengthGe11: boolean;
  expanding: boolean;
  lastOddRun: number | null;
  lastOddRunAtMost1: boolean;
  startsOddEvenBlock: boolean;
  unplacedOdds: number;
  extraEvens: number;
  seam: CycleSeamKind;
  cycleMinShaped: boolean;
};

/** Candidate four-slot word. Same fields as Lean `NecklaceFill`. */
export type NecklaceFill = {
  a1Extras: number;
  middleOdds: number;
  extraEvens: number;
  lastOdds: number;
};

export type AssembleFillCounts = {
  oddCount: number;
  evenCount: number;
  length: number;
  unplacedOdds: number;
  extraEvens: number;
};

/** Odds immediately before the final E. Null if the spelling does not end E. */
export function lastOddRun(word: string): number | null {
  if (!word.endsWith("E")) return null;
  let index = word.length - 2;
  let run = 0;
  while (index >= 0 && word[index] === "O") {
    run += 1;
    index -= 1;
  }
  return run;
}

export function cycleSeam(word: string): CycleSeamKind {
  if (word.length < 2 || !word.startsWith("OO") || !word.endsWith("E")) {
    return "other";
  }
  const closing = lastOddRun(word);
  const window = `${word.slice(-2)}|${word.slice(0, 2)}`;
  if (window === "OE|OO" && closing === 1) return "OE|OO";
  if (window === "EE|OO" && closing === 0) return "EE|OO";
  return "other";
}

/** Forced CycleMin spelling tests. Necessary, not a cycle. */
export function cycleMinShape(word: string): CycleMinShape {
  const odds = oddCount(word);
  const evens = evenCount(word);
  const startsOO = word.startsWith("OO");
  const endsE = word.endsWith("E");
  const closing = lastOddRun(word);
  const lastOddRunAtMost1 = closing !== null && closing <= 1;
  const isExpanding = expanding(word);
  const evenCountGe4 = evens >= 4;
  const oddCountGe7 = odds >= 7;
  const lengthGe11 = word.length >= 11;
  return {
    startsOO,
    endsE,
    evenCount: evens,
    oddCount: odds,
    evenCountGe4,
    oddCountGe7,
    lengthGe11,
    expanding: isExpanding,
    lastOddRun: closing,
    lastOddRunAtMost1,
    startsOddEvenBlock: /^OO+E/.test(word),
    unplacedOdds: Math.max(0, odds - 2),
    extraEvens: Math.max(0, evens - 4),
    seam: cycleSeam(word),
    cycleMinShaped:
      startsOO &&
      endsE &&
      evenCountGe4 &&
      oddCountGe7 &&
      lengthGe11 &&
      isExpanding &&
      lastOddRunAtMost1,
  };
}

/**
 * Indices where rotating the word to start there is CycleMin-shaped.
 * Odd/even *counts* cannot locate the cut (they are rotation-invariant).
 * The cut is a position: start OO, end E, last odd-run ≤ 1, enough letters.
 */
export function cycleMinCuts(word: string): number[] {
  if (!word) return [];
  const cuts: number[] = [];
  for (let index = 0; index < word.length; index += 1) {
    if (cycleMinShape(rotateItinerary(word, index)).cycleMinShaped) {
      cuts.push(index);
    }
  }
  return cuts;
}

/** First CycleMin cut in stored order, or undefined if no rotation is shaped. */
export function firstCycleMinCut(word: string): number | undefined {
  return cycleMinCuts(word)[0];
}

/** Lean `assembleOddEvenRuns`: odd-runs separated by one even each. */
export function assembleOddEvenRuns(runs: readonly number[]): string {
  return runs.map((run) => "O".repeat(run) + "E").join("");
}

/** Lean `oddEvenRuns`. Null unless the word ends E. */
export function oddEvenRuns(word: string): number[] | null {
  if (!word.endsWith("E") || !/^[OE]+$/.test(word)) return null;
  const runs: number[] = [];
  let odds = 0;
  for (const letter of word) {
    if (letter === "O") odds += 1;
    else {
      runs.push(odds);
      odds = 0;
    }
  }
  return runs;
}

export function formatOddEvenRuns(runs: readonly number[]): string {
  return `[${runs.join(", ")}]`;
}

/** Four-slot names as painted on the ring. */
export function formatBalloonSlots(fill: NecklaceFill): string {
  return `a₁ = ${2 + fill.a1Extras}, a∗ = ${fill.middleOdds}, e₊ = ${fill.extraEvens}, aₑ = ${fill.lastOdds}`;
}

/** Display form `O^3 E O^2 E E` of a Lean run list. */
export function formatRunWord(runs: readonly number[]): string {
  return runs.map((odds) => (odds === 0 ? "E" : `O^${odds} E`)).join(" ");
}

/** KaTeX form of a Lean run list: `O^{3}E\,O^{2}E\,E`. */
export function formatRunWordTex(runs: readonly number[]): string {
  return runs.map((odds) => (odds === 0 ? "E" : `O^{${odds}}E`)).join("\\,");
}

export function runsEqual(left: readonly number[], right: readonly number[]): boolean {
  return left.length === right.length && left.every((value, index) => value === right[index]);
}

/** Lean `NecklaceFill.toRuns`: bunched middle odds and empty extra evens. */
export function necklaceFillToRuns(fill: NecklaceFill): number[] {
  return [
    2 + fill.a1Extras,
    fill.middleOdds,
    ...Array.from({ length: fill.extraEvens + 1 }, () => 0),
    fill.lastOdds,
  ];
}

/** Lean `assembleFill`: bunched extra evens, empty third odd-run. */
export function assembleFill(fill: NecklaceFill): string {
  return (
    "O".repeat(2 + fill.a1Extras) +
    "E" +
    "O".repeat(fill.middleOdds) +
    "E" +
    "E".repeat(fill.extraEvens) +
    "E" +
    "O".repeat(fill.lastOdds) +
    "E"
  );
}

export function necklaceFillAdmits(fill: NecklaceFill): boolean {
  return (
    fill.a1Extras >= 0 &&
    fill.middleOdds >= 0 &&
    fill.extraEvens >= 0 &&
    fill.lastOdds >= 0 &&
    fill.lastOdds <= 1
  );
}

/** Exact Lean identities `assembleFill_oddCount` / `evenCount` / `length`. */
export function assembleFillCounts(fill: NecklaceFill): AssembleFillCounts {
  return {
    oddCount: 2 + fill.a1Extras + fill.middleOdds + fill.lastOdds,
    evenCount: 4 + fill.extraEvens,
    length: 6 + fill.a1Extras + fill.middleOdds + fill.extraEvens + fill.lastOdds,
    unplacedOdds: fill.a1Extras + fill.middleOdds + fill.lastOdds,
    extraEvens: fill.extraEvens,
  };
}

/**
 * Parse the candidate four-slot word. Null if the spelling is not an
 * `assembleFill` — a CycleMin-shaped leftover such as O³EO²EO²EE is not.
 */
export function tryAssembleFill(word: string): NecklaceFill | null {
  if (!word.endsWith("E")) return null;
  let index = 0;
  while (index < word.length && word[index] === "O") index += 1;
  if (index < 2 || word[index] !== "E") return null;
  const a1Extras = index - 2;
  index += 1;
  const midStart = index;
  while (index < word.length && word[index] === "O") index += 1;
  const middleOdds = index - midStart;
  if (index >= word.length || word[index] !== "E") return null;
  index += 1;
  const rest = word.slice(index);
  const matched = /^(E+)(O*)E$/.exec(rest);
  if (!matched) return null;
  return {
    a1Extras,
    middleOdds,
    extraEvens: matched[1].length - 1,
    lastOdds: matched[2].length,
  };
}

export function formatNecklaceFill(fill: NecklaceFill): string {
  return `⟨${fill.a1Extras}, ${fill.middleOdds}, ${fill.extraEvens}, ${fill.lastOdds}⟩`;
}
