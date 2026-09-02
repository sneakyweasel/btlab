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

export const financeSnapshot = snapshot;

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
    oMin: record?.o ?? oMinForLength(length),
    nMax: record?.nMax ?? null,
    record: record !== undefined,
    inExceptionSet,
    status: inExceptionSet ? "admissible" : "excluded",
  };
}
