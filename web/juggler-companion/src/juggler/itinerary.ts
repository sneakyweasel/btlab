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
  const left = 3 ** odds;
  const right = 2 ** length;
  if (left < right) return "contracting";
  if (left > right) return "expanding";
  return "critical";
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
