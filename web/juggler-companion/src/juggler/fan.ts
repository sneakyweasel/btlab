/**
 * Semiconvergent fan of Proposition 5.12. Display fork of fan.json.
 * n_max is shipped; never recomputed.
 */

import fanData from "../data/fan.json";
import {
  LAB_FLOOR,
  MAIN_FLOOR,
  PAPER_FLOOR,
  PRINTED_FLOOR,
} from "./constants";

export type FanRow = {
  k: number;
  L: number;
  o: number;
  lam: number;
  nmax: number;
};

export const FAN_ROWS: readonly FanRow[] = fanData as FanRow[];

export const FAN_Q12 = 176_251;
export const FAN_Q13 = 301_994;
export const FAN_P12 = 111_202;
export const FAN_P13 = 190_537;
export const FAN_K_MIN = 0;
export const FAN_K_MAX = 55;
export const FAN_MEMBER_COUNT = FAN_K_MAX - FAN_K_MIN + 1;

/** Named k in the paper’s §5.8 table. */
export const FAN_CHIPS = [0, 1, 2, 3, 6, 31, 52, 54, 55] as const;

export const FAN_CERTIFIED_FLOORS = [
  { n0: PAPER_FLOOR, label: "10⁶" },
  { n0: LAB_FLOOR, label: "2.6·10⁷" },
  { n0: PRINTED_FLOOR, label: "1.6·10⁸" },
  { n0: MAIN_FLOOR, label: "3.5·10⁸" },
] as const;

/** Finance n_max(L_54) ≈ 2.2·10¹²; n_max(L_55) ≈ 4.9·10¹². */
export const FAN_EXHAUST_NMAX = FAN_ROWS[54]?.nmax ?? 2_199_215_565_043;
export const FAN_Q14_NMAX = FAN_ROWS[55]?.nmax ?? 4_865_750_064_600;

export type FanWalkStatus = "excluded" | "current" | "open";

export function fanLength(k: number): number {
  return FAN_Q12 + k * FAN_Q13;
}

export function fanOdd(k: number): number {
  return FAN_P12 + k * FAN_P13;
}

export function fanRow(k: number): FanRow | null {
  if (!Number.isInteger(k) || k < FAN_K_MIN || k > FAN_K_MAX) return null;
  return FAN_ROWS[k] ?? null;
}

/**
 * Printed walk-charge frontier index at a certified floor.
 * Finance-only reachedAt is a different comparison and is not this.
 */
export function printedWalkK(n0: number): number | null {
  if (n0 >= MAIN_FLOOR) return 2;
  if (n0 >= PRINTED_FLOOR) return 1;
  if (n0 >= LAB_FLOOR) return 0;
  return null;
}

export function walkStatus(k: number, frontierK: number): FanWalkStatus {
  if (k < frontierK) return "excluded";
  if (k === frontierK) return "current";
  return "open";
}

export type FanView = {
  k: number;
  L: number;
  o: number;
  lam: number;
  nmax: number;
  frontierK: number;
  status: FanWalkStatus;
  financePassed: boolean;
};

export function fanView(k: number, n0: number = MAIN_FLOOR): FanView | null {
  const row = fanRow(k);
  if (row === null) return null;
  const selectedFloorK = k === 0 || k === 1 || k === 2 ? k : null;
  const frontierK = selectedFloorK ?? printedWalkK(n0) ?? 2;
  return {
    k: row.k,
    L: row.L,
    o: row.o,
    lam: row.lam,
    nmax: row.nmax,
    frontierK,
    status: walkStatus(row.k, frontierK),
    financePassed: row.nmax <= n0,
  };
}

/** Walk-charge factor at the present frontier: n_max(L_1) / N₀. */
export function walkChargeFactor(n0: number = MAIN_FLOOR): number {
  const row = fanRow(1);
  if (row === null || n0 <= 0) return Number.POSITIVE_INFINITY;
  return row.nmax / n0;
}
