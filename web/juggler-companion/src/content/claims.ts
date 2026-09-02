import {
  LAB_FLOOR,
  LAB_PARITY_PERIOD,
  LAB_WALK_PERIOD,
  PAPER_FLOOR,
  PAPER_PERIOD,
  PRINTED_FLOOR,
  PRINTED_PERIOD,
} from "../juggler/constants";

export const CLAIM_ROWS = [
  {
    plain: "After a word, the result cannot outrun a known power bound.",
    theorem: "Theorem 2.2 / Corollary 2.3 power envelope",
    tag: "EXACT — LEAN VERIFIED",
  },
  {
    plain: "Going backwards, an odd image has at most one odd parent.",
    theorem: "Lemma 3.1 odd cells unique",
    tag: "EXACT — LEAN VERIFIED",
  },
  {
    plain: "A real loop must mix O and E, and grow more than it shrinks.",
    theorem: "Theorem 3.2 cycle restrictions",
    tag: "EXACT — LEAN VERIFIED",
  },
  {
    plain: "Every real loop has at least four even letters, so the period is at least 11.",
    theorem: "Theorem 3.22 / Corollary 3.23",
    tag: "EXACT — LEAN VERIFIED",
  },
  {
    plain: "At a cycle minimum, n log n times the surplus cannot exceed L · 3^o.",
    theorem: "Theorem 4.4 finance inequality",
    tag: "EXACT — LEAN VERIFIED",
  },
  {
    plain: `With the verified descent floor ${PAPER_FLOOR.toLocaleString("en-US")}, there is no period ≤ ${PAPER_PERIOD - 1}.`,
    theorem: "Theorem 4.6",
    tag: "COMPUTATIONALLY VERIFIED",
  },
  {
    plain: `At the laboratory floor ${LAB_FLOOR.toLocaleString("en-US")} the same table gives period ≥ ${LAB_PARITY_PERIOD.toLocaleString("en-US")}.`,
    theorem: "Theorem 5.2",
    tag: "COMPUTATIONALLY VERIFIED",
  },
  {
    plain: `Walk charge at that floor kills the parity leftovers below ${LAB_WALK_PERIOD.toLocaleString("en-US")}.`,
    theorem: "Theorem 5.9",
    tag: "COMPUTATIONALLY VERIFIED",
  },
  {
    plain: `At the second certified floor ${PRINTED_FLOOR.toLocaleString("en-US")}, period ≥ ${PRINTED_PERIOD.toLocaleString("en-US")}.`,
    theorem: "Corollary 5.10",
    tag: "COMPUTATIONALLY VERIFIED",
  },
] as const;

export const NOT_CLAIMED = [
  "This is not a termination proof and not progress toward the Juggler conjecture.",
  "Hitting 1 on a playground walk is one orbit, not a theorem that every start reaches 1.",
  "A finance-survivor length is a length the inequality did not kill. It is not a candidate cycle.",
  "The census-free window of Theorem 5.8 stops at 301,994. Corollary 5.10 is not an extension of that window.",
  "Paper B (parity discrepancy and descent densities) is a different manuscript.",
] as const;
