import {
  LAB_FLOOR,
  LAB_PARITY_PERIOD,
  LAB_WALK_PERIOD,
  PACKING_DEATH_CONDITIONAL,
  PACKING_DEATH_COUNT,
  PACKING_DEATH_FIRST,
  PACKING_DEATH_STEP,
  PACKING_DEATH_UNCONDITIONAL,
  PAPER_FLOOR,
  PAPER_PERIOD,
  MAIN_FLOOR,
  MAIN_PERIOD,
  PRINTED_FLOOR,
  PRINTED_PERIOD,
  RUN_EXCEPTION_COUNT,
  RUN_EXCEPTION_COUNT_NO_HYPOTHESIS,
} from "../juggler/constants";

export const CLAIM_ROWS = [
  {
    plain: "After an itinerary, the result cannot outrun a known power bound.",
    theorem: "Theorem 2.2 / Corollary 2.3 power envelope",
    tag: "EXACT — LEAN VERIFIED",
  },
  {
    plain: "Going backwards, an odd image has at most one odd parent.",
    theorem: "Lemma 3.1 odd one-step preimages unique",
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
    plain:
      "Section 3's eleven exclusions are one inequality: an odd run of length a followed by a suffix with s letters and l odd ones is dead once (3/2)^a exceeds 2^s/3^l. The eleven printed thresholds are ten evaluations of it.",
    theorem: "Theorem 3.26 / Corollary 3.27 run-suffix law",
    tag: "EXACT — HUMAN PROOF",
  },
  {
    plain:
      "Using the cycle minimum at every step of an odd run, not only at its start, removes the constant entirely. That lifts the floor-free bound to eight even letters and period 22 once the cycle minimum is at least 300.",
    theorem: "Lemma 3.28 / Theorem 3.31",
    tag: "COMPUTATIONALLY VERIFIED",
  },
  {
    plain: "At a cycle minimum, n log n times the surplus cannot exceed L · 3^o.",
    theorem: "Theorem 4.4 finance inequality",
    tag: "EXACT — LEAN VERIFIED",
  },
  {
    plain:
      "The charge behind the per-length table prices valleys at n, internal odd states at t = ⌊n^(3/2)⌋, and evens at n². Called the “parity” charge for historical reasons, it is a three-class bound, and the t-scale middle term is what makes it sharper than a parity split.",
    theorem: "Corollary 4.5 three-class charge (cycleMin_defect_threeTerm)",
    tag: "EXACT — LEAN VERIFIED",
  },
  {
    plain: `With the verified descent floor ${PAPER_FLOOR.toLocaleString("en-US")}, there is no period ≤ ${PAPER_PERIOD - 1}. The inequality behind the table is Lean; the per-length arithmetic and the descent floor stay computation.`,
    theorem: "Theorem 4.6",
    tag: "COMPUTATIONALLY VERIFIED",
  },
  {
    plain:
      "Packing the valleys by run type sharpens the charge by a factor 1.4048. It needs two hypotheses: the itinerary is primitive, and it contains no EE. Without the second, the counting gives only #cheap ≤ o − #blocks.",
    theorem: "Theorem 4.7 run-type packing",
    tag: "EXACT — HUMAN PROOF",
  },
  {
    plain: `Packing kills ${PACKING_DEATH_COUNT} more lengths, ${PACKING_DEATH_FIRST.toLocaleString("en-US")} + ${PACKING_DEATH_STEP.toLocaleString("en-US")}k. Only ${PACKING_DEATH_UNCONDITIONAL} hold whatever the itinerary: the other ${PACKING_DEATH_CONDITIONAL} need the no-EE hypothesis, and admissible words with odd runs of length ≤ 2 defeat each. Dropping it leaves ${RUN_EXCEPTION_COUNT_NO_HYPOTHESIS} lengths, not ${RUN_EXCEPTION_COUNT}. The period ${PAPER_PERIOD.toLocaleString("en-US")} is unchanged either way.`,
    theorem: "Theorem 4.8 run-type table",
    tag: "COMPUTATIONALLY VERIFIED",
  },
  {
    plain:
      "Without a descent floor, the surplus is a linear form in (L, o). Rhin’s measure then excludes only short cycles; the open problem is the long regime.",
    theorem: "Theorem 4.10 / Corollary 4.11 gap transfer",
    tag: "EXACT — HUMAN PROOF",
  },
  {
    plain: `At the laboratory floor ${LAB_FLOOR.toLocaleString("en-US")} the same table gives period ≥ ${LAB_PARITY_PERIOD.toLocaleString("en-US")}.`,
    theorem: "Theorem 5.2",
    tag: "COMPUTATIONALLY VERIFIED",
  },
  {
    plain:
      "On the window [50,508, 16,785,921) the walk-charge envelope is census-free. That bounds the charge, not the kill.",
    theorem: "Theorem 5.8 census-free window",
    tag: "EXACT — HUMAN PROOF",
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
  {
    plain: `At the third certified floor ${MAIN_FLOOR.toLocaleString("en-US")}, period ≥ ${MAIN_PERIOD.toLocaleString("en-US")}.`,
    theorem: "Corollary 5.11",
    tag: "COMPUTATIONALLY VERIFIED",
  },
  {
    plain:
      "The surviving lengths are one arithmetic progression of 56 terms, 176251 + 301994k, ending on the next convergent.",
    theorem: "Proposition 5.12 fan law",
    tag: "EXACT — LEAN VERIFIED",
  },
  {
    plain:
      "The fan ends at k = 55 for the same reason the certified numeration range does: Λ₅₅ > 0 and Λ₅₆ < 0 are the two sandwich inequalities.",
    theorem: "fanLambda_55_pos / fanLambda_56_neg (FanLaw.lean)",
    tag: "EXACT — LEAN VERIFIED",
  },
  {
    plain:
      "The lattice program maximises over words that need not be realizable, but that costs under a part in 10⁸ at the kill-table lengths.",
    theorem: "Propositions 5.8b, 5.8c",
    tag: "COMPUTATIONALLY VERIFIED",
  },
  {
    plain:
      "The walk charge is worth about 0.44 ln n′ over the parity charge, so doubling its efficiency means squaring the descent floor.",
    theorem: "Remark 5.8a margin scaling",
    tag: "OBSERVATION",
  },
  {
    plain:
      "If every n ≤ 554,000,000 reaches 1, then the period is at least 1,082,233. The kill table is done; the floor is not.",
    theorem: "Corollary 5.14",
    tag: "COMPUTATIONALLY VERIFIED",
  },
] as const;

export const DEFINITIONS = [
  {
    term: "Map J",
    meaning: "The one-step rule. The sequence is the trajectory of iterates.",
  },
  {
    term: "Floor",
    meaning: "⌊x⌋ throws away the decimals, after every step.",
  },
  {
    term: "Trajectory",
    meaning: "The list of values n, J(n), J²(n), … .",
  },
  {
    term: "Itinerary",
    meaning: "A finite string of O/E parities of a prefix. Not the trajectory.",
  },
  {
    term: "CycleMin",
    meaning:
      "The rotation of a cycle itinerary that starts at the smallest value. That spelling starts OO, ends E, and needs four evens in Lean (Theorem 3.22); eight evens once the minimum is at least 300 (Theorem 3.31).",
  },
  {
    term: "String",
    meaning:
      "The realized itinerary before the first visit to a cycle. Empty if the start is already on the cycle. The walk of 3 is OOOEEE onto 1.",
  },
  {
    term: "Realized itinerary",
    meaning: "The trajectory of n actually follows those letters.",
  },
  {
    term: "Ideal exponent",
    meaning: "3^o / 2^k for an itinerary of length k with o odd letters, before floors.",
  },
  {
    term: "One-step preimage",
    meaning: "The set J⁻¹(m) = {k : J(k) = m}. J is not invertible.",
  },
  {
    term: "N₀",
    meaning: "A verified descent floor: a computational input, not the theorem.",
  },
] as const;

export const NOT_CLAIMED = [
  "This is not a termination proof and not progress toward the Juggler conjecture.",
  "Hitting 1 on a playground walk is one trajectory, not a theorem that every start reaches 1.",
  "A finance-survivor length is a length the inequality did not kill. It is not a candidate cycle.",
  "The census-free window of Theorem 5.8 bounds the charge, not the kill. The comparison against θ(L) is still per-length, so the kill tables are not census-free.",
  "Proposition 5.8b/5.8c bound the relaxation at the lengths where it can be measured. They do not prove the extremal walk is realizable at every length.",
  "Corollary 4.11 is a floor-free reduction. It is weaker than the finance table at every certified floor and does not kill the long survivors.",
  "Corollary 5.14 is conditional on a descent floor nobody has certified. It is a priced next step, not a theorem about periods.",
  "Theorem 3.31 needs a cycle minimum at least 300 and an enumeration of 325452 seven-even forms. Theorem 3.22 remains the statement proved in Lean for every n at least 2, and the interactive checker implements that one.",
  "No independence-from-Peano-arithmetic claim is made. Goodstein is a different theorem.",
  "Paper B (parity discrepancy and descent densities) is a different manuscript.",
] as const;
