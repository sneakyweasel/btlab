/**
 * Walk-charge transport and shipped hug words. Display fork of
 * cycle_walk_charge.deficit_D and cycle_walk_greedy.hug_word
 * (Paper A Theorems 5.3–5.4). Not a hug-charge calculator.
 */

import {
  LAB_FLOOR,
  LAB_WALK_PERIOD,
  MAIN_FLOOR,
  MAIN_PERIOD,
  PRINTED_FLOOR,
  PRINTED_PERIOD,
  WALK_WINDOW_HI,
  WALK_WINDOW_LO,
} from "./constants";
import { GAP_LENGTH_CHIPS, resolveOddCount } from "./gapTransfer";

export const TRANSPORT_EVEN = 1.05;
export const TRANSPORT_ODD = 0.7;
export const HUG_MU = Math.log2(1.5);

export const WALK_N_MIN = 400;
export const WALK_N_MAX = 10_000_000_000;
export const WALK_L_MIN = 1;
export const WALK_L_MAX = 2_000_000;
export const WALK_LENGTH_CHIPS = GAP_LENGTH_CHIPS;

export type ShippedHugWord = {
  L: number;
  o: number;
  word: string;
};

/** hug_word(11, 7) and hug_word(19, 12). No other pairs are shipped. */
export const SHIPPED_HUG_WORDS: readonly ShippedHugWord[] = [
  { L: 11, o: 7, word: "OOEOOEOOEOE" },
  { L: 19, o: 12, word: "OOEOOEOOEOEOOEOOEOE" },
];

export type WalkFloorComparison = {
  name: string;
  n0: number;
  printedL: number;
  theorem: string;
};

export const WALK_FLOOR_COMPARISONS: readonly WalkFloorComparison[] = [
  {
    name: "Theorem 5.9",
    n0: LAB_FLOOR,
    printedL: LAB_WALK_PERIOD,
    theorem: "walk charge at 2.6·10⁷",
  },
  {
    name: "Corollary 5.10",
    n0: PRINTED_FLOOR,
    printedL: PRINTED_PERIOD,
    theorem: "walk charge at 1.6·10⁸",
  },
  {
    name: "Corollary 5.11",
    n0: MAIN_FLOOR,
    printedL: MAIN_PERIOD,
    theorem: "walk charge at 3.5·10⁸",
  },
];

export const WALK_WINDOW_MARKS = [
  { L: WALK_WINDOW_LO, label: "50,508", role: "window" },
  { L: LAB_WALK_PERIOD, label: "176,251", role: "bound" },
  { L: PRINTED_PERIOD, label: "478,245", role: "bound" },
  { L: MAIN_PERIOD, label: "780,239", role: "bound" },
  { L: WALK_WINDOW_HI, label: "16,785,921", role: "window" },
] as const;

/** D = 1.05 e / n + 0.7 o / n^{3/2}. */
export function deficitD(n: number, length: number, odds: number): number {
  if (n <= 0) return Number.POSITIVE_INFINITY;
  const evens = length - odds;
  return TRANSPORT_EVEN * evens / n + TRANSPORT_ODD * odds / n ** 1.5;
}

/** n' = n e^{-D}. */
export function reducedBase(n: number, deficit: number): number {
  return n * Math.exp(-deficit);
}

export function shippedHugWord(length: number, odds: number): ShippedHugWord | null {
  return SHIPPED_HUG_WORDS.find((row) => row.L === length && row.o === odds) ?? null;
}

/** Height u after each prefix, including u_0 = 0. u = (1+μ)a − k. */
export function hugHeights(word: string): number[] {
  const heights = [0];
  let odds = 0;
  for (let index = 0; index < word.length; index += 1) {
    if (word[index] === "O") odds += 1;
    heights.push((1 + HUG_MU) * odds - (index + 1));
  }
  return heights;
}

export type WalkChargeView = {
  n: number;
  L: number;
  o: number;
  e: number;
  oIsDefault: boolean;
  D: number;
  nPrime: number;
  lnNPrime: number;
  hug: ShippedHugWord | null;
  prefixMinimal: boolean;
};

export function walkChargeView(
  n: number,
  length: number,
  odds: number | null,
): WalkChargeView {
  const o = resolveOddCount(length, odds);
  const D = deficitD(n, length, o);
  const nPrime = reducedBase(n, D);
  const hug = shippedHugWord(length, o);
  return {
    n,
    L: length,
    o,
    e: length - o,
    oIsDefault: odds === null,
    D,
    nPrime,
    lnNPrime: Math.log(nPrime),
    hug,
    prefixMinimal: hug !== null,
  };
}
