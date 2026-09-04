/**
 * Finance status at the Theorem 4.6 floor 10^6.
 * Lengths through LIVE_FINANCE_L_MAX compute θ live. Larger surplus
 * values and every n_max are looked up from finance.json.
 */

import snapshot from "../data/finance.json";
import {
  LIVE_FINANCE_L_MAX,
  PAPER_EXCEPTION_COUNT,
  PAPER_FLOOR,
  PAPER_L_CAP,
  PAPER_PERIOD,
} from "./constants";
import { oMinForLength } from "./itinerary";
import { constantOneCrossing, thetaExact } from "./necklace";

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

/** Shipped Theorem 4.4 surplus and crossing. Written by export_finance_ledgers.py. */
export type FinanceLedger = {
  L: number;
  o: number;
  theta: number;
  thetaDecimal: string;
  crossing: number;
};

export const financeLedgers: readonly FinanceLedger[] = snapshot.ledgers;

if (financeLedgers.length === 0) {
  throw new Error("finance snapshot has no ledgers");
}

const ledgerByLength = new Map(financeLedgers.map((row) => [row.L, row] as const));

for (const row of snapshot.records) {
  if (!ledgerByLength.has(row.L)) {
    throw new Error(`finance snapshot is missing a ledger for record L=${row.L}`);
  }
}
for (const row of financeSurvivors) {
  if (!ledgerByLength.has(row.L)) {
    throw new Error(`finance snapshot is missing a ledger for survivor L=${row.L}`);
  }
}

export function shippedLedger(length: number): FinanceLedger | null {
  return ledgerByLength.get(length) ?? null;
}

export type LedgerSource = "live" | "shipped";

export type ResolvedLedger = FinanceLedger & { source: LedgerSource };

/**
 * Small L: exact θ in the browser. Large L: shipped row, or null.
 * n_max is never computed here.
 */
export function resolveLedger(length: number): ResolvedLedger | null {
  if (!Number.isInteger(length) || length < 1) return null;
  if (length <= LIVE_FINANCE_L_MAX) {
    const theta = thetaExact(length);
    return {
      L: length,
      o: theta.o,
      theta: theta.approx,
      thetaDecimal: theta.decimal,
      crossing: constantOneCrossing(length, theta.approx),
      source: "live",
    };
  }
  const row = shippedLedger(length);
  return row === null ? null : { ...row, source: "shipped" };
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
