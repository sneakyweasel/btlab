/**
 * Lookup-only finance status at the Theorem 4.6 floor 10^6.
 * n_max is never recomputed in the browser.
 */

import snapshot from "../data/finance.json";
import {
  PAPER_EXCEPTION_COUNT,
  PAPER_FLOOR,
  PAPER_L_CAP,
  PAPER_PERIOD,
} from "./constants";
import { oMinForLength } from "./itinerary";

export type FinanceStatus = "excluded" | "admissible" | "beyond table" | "invalid";

export type FinanceView = {
  length: number;
  oMin: number | null;
  nMax: number | null;
  record: boolean;
  inExceptionSet: boolean;
  status: FinanceStatus;
};

const records = new Map(
  snapshot.records.map((row) => [row.L, row] as const),
);
const exceptionSet = new Set(snapshot.exceptionLengths);

if (snapshot.floor !== PAPER_FLOOR) {
  throw new Error("finance snapshot floor is not 10^6");
}
if (snapshot.firstSurvivor !== PAPER_PERIOD) {
  throw new Error("finance snapshot first survivor is not 25781");
}
if (snapshot.exceptionCount !== PAPER_EXCEPTION_COUNT) {
  throw new Error("finance snapshot exception count is not 141");
}
if (snapshot.survivors.length !== PAPER_EXCEPTION_COUNT) {
  throw new Error("finance snapshot survivor rows are not 141");
}

export const financeSnapshot = snapshot;

/** One finance survivor at the floor 10^6 with its Proposition 4.9 coordinates. */
export type FinanceSurvivor = {
  L: number;
  o: number;
  nMax: number;
  /** (L, o) = a·v* + b·v_1054 with v* = (25781, 16266), v_1054 = (1054, 665). */
  a: number;
  b: number;
  /** Theorem 4.8: killed by the run-type packing at the same floor. */
  packingDeath: boolean;
};

export const financeSurvivors: readonly FinanceSurvivor[] = snapshot.survivors;
export const financeLattice = snapshot.lattice;

const survivorByLength = new Map(financeSurvivors.map((row) => [row.L, row] as const));

export function survivorOf(length: number): FinanceSurvivor | undefined {
  return survivorByLength.get(length);
}

/** Shipped parity n_max for a length: a record row or a survivor row, else null. */
export function shippedNMax(length: number): number | null {
  return records.get(length)?.nMax ?? survivorByLength.get(length)?.nMax ?? null;
}

export function financeView(length: number): FinanceView {
  if (!Number.isInteger(length) || length < 1) {
    return {
      length,
      oMin: null,
      nMax: null,
      record: false,
      inExceptionSet: false,
      status: "invalid",
    };
  }
  const record = records.get(length);
  const survivor = survivorByLength.get(length);
  const inExceptionSet = exceptionSet.has(length);
  if (length > PAPER_L_CAP) {
    return {
      length,
      oMin: record?.o ?? oMinForLength(length),
      nMax: record?.nMax ?? null,
      record: record !== undefined,
      inExceptionSet,
      status: "beyond table",
    };
  }
  return {
    length,
    oMin: record?.o ?? survivor?.o ?? oMinForLength(length),
    nMax: record?.nMax ?? survivor?.nMax ?? null,
    record: record !== undefined,
    inExceptionSet,
    status: inExceptionSet ? "admissible" : "excluded",
  };
}
