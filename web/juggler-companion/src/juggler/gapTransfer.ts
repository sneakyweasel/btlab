/**
 * Gap transfer and Rhin short-cycle reduction. Display fork of
 * paper_a_audit.rhin_checks / survivor_exponent and the SdW packaging
 * in cycle_gap_baker.py (Paper A Theorem 4.10, Corollary 4.11).
 */

import {
  LAB_FLOOR,
  LAB_PARITY_PERIOD,
  LIVE_FINANCE_L_MAX,
  MAIN_FLOOR,
  MAIN_PERIOD,
  PAPER_FLOOR,
  PAPER_PERIOD,
  PRINTED_FLOOR,
  PRINTED_PERIOD,
} from "./constants";
import { resolveLedger, shippedNMax } from "./finance";
import { oMinForLength } from "./itinerary";
import { oMinExact } from "./necklace";

export const RHIN_A = 13.3;
export const RHIN_SHIFT = 0.46057;
export const RHIN_C = 6.1256;
export const RHIN_POWER = 14.3;
export const RHIN_COEFF = 915;

export const GAP_N_MIN = 2;
export const GAP_N_MAX = 10_000_000_000;
export const GAP_L_MIN = 1;
export const GAP_L_MAX = 2_000_000;

export const GAP_LENGTH_CHIPS = [
  11, 19, 84, 569, 1054, 25781, 50508, 176251, 478245, 780239,
] as const;

/** Paper remark: log L / log n_max at the named survivors. */
export const SURVIVOR_EXPONENTS = [
  { L: 25781, nMax: 26_254_995, exponent: 0.595 },
  { L: 50508, nMax: 162_848_325, exponent: 0.573 },
  { L: 176251, nMax: 1_044_093_213, exponent: 0.582 },
  { L: 780239, nMax: 4_479_642_886, exponent: 0.611 },
] as const;

export type GapCase = "nonpositive" | "large" | "thin";

export type FloorComparison = {
  name: string;
  n0: number;
  rhinL: number;
  printedL: number;
  theorem: string;
};

export function lambdaOf(length: number, odds: number): number {
  return odds * Math.log(3) - length * Math.LN2;
}

/** θ = 1 − 2^L / 3^o, via -expm1 so large L stay finite. */
export function thetaOf(length: number, odds: number): number {
  return -Math.expm1(length * Math.LN2 - odds * Math.log(3));
}

export function resolveOddCount(length: number, odds: number | null): number {
  if (odds !== null) return odds;
  if (length <= LIVE_FINANCE_L_MAX) return oMinExact(length);
  const ledger = resolveLedger(length);
  if (ledger) return ledger.o;
  return oMinForLength(length) ?? 1;
}

export type GapCaseKind = GapCase;

/** The three branches of the cycleMin_gap_transfer proof. */
export function gapCase(length: number, odds: number): GapCase {
  const lam = lambdaOf(length, odds);
  if (lam <= 0) return "nonpositive";
  if (odds * Math.log(3) >= (length + 1) * Math.LN2) return "large";
  return "thin";
}

export function gapHolds(n: number, length: number, odds: number): boolean {
  if (n < 2 || length < 1) return false;
  const lam = lambdaOf(length, odds);
  return n * Math.log(n) * Math.min(lam, 1) <= 2 * length;
}

/** Λ > e^{-6.1256} L^{-13.3} (SdW Lemma 12, height L). */
export function rhinLambdaLower(length: number): number {
  if (length < 1) return Math.POSITIVE_INFINITY;
  const exponent = -RHIN_C * (RHIN_SHIFT + Math.log(length));
  if (exponent < -700) return 0;
  return Math.exp(exponent);
}

/** L = (n log n / 915)^{1/14.3}. */
export function rhinMinLength(n: number): number {
  if (n < 2) return Number.POSITIVE_INFINITY;
  return (n * Math.log(n) / RHIN_COEFF) ** (1 / RHIN_POWER);
}

/** Least integer L with L > rhinMinLength(n). */
export function rhinForcedLength(n: number): number {
  const min = rhinMinLength(n);
  if (!Number.isFinite(min) || min < 1) return 1;
  return Math.floor(min) + 1;
}

/** Corollary 4.11: L^{14.3} ≤ n log n / 915. */
export function shortExcluded(n: number, length: number): boolean {
  if (n < 2 || length < 1) return false;
  return length ** RHIN_POWER <= (n * Math.log(n)) / RHIN_COEFF;
}

export const FLOOR_COMPARISONS: readonly FloorComparison[] = [
  {
    name: "Theorem 4.6",
    n0: PAPER_FLOOR,
    rhinL: rhinForcedLength(PAPER_FLOOR),
    printedL: PAPER_PERIOD,
    theorem: "finance at 10⁶",
  },
  {
    name: "Theorem 5.2",
    n0: LAB_FLOOR,
    rhinL: rhinForcedLength(LAB_FLOOR),
    printedL: LAB_PARITY_PERIOD,
    theorem: "parity table at 2.6·10⁷",
  },
  {
    name: "Corollary 5.10",
    n0: PRINTED_FLOOR,
    rhinL: rhinForcedLength(PRINTED_FLOOR),
    printedL: PRINTED_PERIOD,
    theorem: "walk charge at 1.6·10⁸",
  },
  {
    name: "Corollary 5.11",
    n0: MAIN_FLOOR,
    rhinL: rhinForcedLength(MAIN_FLOOR),
    printedL: MAIN_PERIOD,
    theorem: "walk charge at 3.5·10⁸",
  },
];

export type PlanePoint = {
  L: number;
  nMax: number;
  label: string;
};

export function namedSurvivorPoints(): PlanePoint[] {
  return SURVIVOR_EXPONENTS.map((row) => ({
    L: row.L,
    nMax: row.nMax,
    label: `L = ${row.L.toLocaleString("en-US")}`,
  }));
}

export function nMaxForLength(length: number): number | null {
  const shipped = shippedNMax(length);
  if (shipped !== null) return shipped;
  const named = SURVIVOR_EXPONENTS.find((row) => row.L === length);
  return named?.nMax ?? null;
}

export type GapTransferView = {
  n: number;
  L: number;
  o: number;
  oIsDefault: boolean;
  theta: number;
  lambda: number;
  minLambda: number;
  expanding: boolean;
  caseKind: GapCase;
  left: number;
  right: number;
  holds: boolean;
  rhinL: number;
  short: boolean;
};

export function gapTransferView(
  n: number,
  length: number,
  odds: number | null,
): GapTransferView {
  const o = resolveOddCount(length, odds);
  const lam = lambdaOf(length, o);
  const theta = thetaOf(length, o);
  return {
    n,
    L: length,
    o,
    oIsDefault: odds === null,
    theta,
    lambda: lam,
    minLambda: Math.min(lam, 1),
    expanding: lam > 0,
    caseKind: gapCase(length, o),
    left: n * Math.log(n) * Math.min(lam, 1),
    right: 2 * length,
    holds: gapHolds(n, length, o),
    rhinL: rhinForcedLength(n),
    short: shortExcluded(n, length),
  };
}
