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
    plain:
      "A real loop's word reads O^a₁ E … O^aₑ E: e blocks, one even letter each, the first odd run at least two long and the last at most one. This is what lays out the lollipop figure — the bead count and both ends of it.",
    theorem: "cycleMin_has_full_odd_even_run_form (CycleRunForm.lean)",
    tag: "EXACT — LEAN VERIFIED",
  },
  {
    plain:
      "If the maximum stays below the cube of the minimum, the sorted states rotate by the even count, the period and odd count are coprime, and the CycleMin word is the ceiling mechanical word.",
    theorem: "Theorem 3.33 cubic-band order",
    tag: "EXACT — HUMAN PROOF",
  },
  {
    plain:
      "For an actual cubic-band cycle with minimum at least 7, the maximum sits below m³ − m^{15/8}.",
    theorem: "Theorem 3.39 periodic return height restriction",
    tag: "EXACT — HUMAN PROOF",
  },
  {
    plain:
      "Successive genuine return transfers carve still deeper height strips at minima 2^{24} and 2^{128}. The terminal mixed OE/EO passage contracts and does not close no-cycle.",
    theorem: "Theorem 3.40 / Proposition 3.41",
    tag: "EXACT — HUMAN PROOF",
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
      "Packing the valleys by run type sharpens the charge by a factor 1.4048. It needs two hypotheses: the itinerary is primitive, and it contains no EE. Given both, the display follows from CycleMin (cycleMin_sixTerm), so they are sufficient as well as necessary; without the second the counting gives only #cheap ≤ o − #blocks.",
    theorem: "Theorem 4.7 run-type packing",
    tag: "EXACT — LEAN VERIFIED",
  },
  {
    plain: `Packing kills ${PACKING_DEATH_COUNT} more lengths, ${PACKING_DEATH_FIRST.toLocaleString("en-US")} + ${PACKING_DEATH_STEP.toLocaleString("en-US")}k. ${PACKING_DEATH_UNCONDITIONAL} of them need no hypothesis at all: at most half the odd letters can be cheap valleys, whatever the word does with EE (two_mul_cheap_le_odd), and that alone excludes them. The other ${PACKING_DEATH_CONDITIONAL} rest on the no-EE hypothesis, and admissible words with odd runs of length ≤ 2 defeat each. Dropping it leaves ${RUN_EXCEPTION_COUNT_NO_HYPOTHESIS} lengths, not ${RUN_EXCEPTION_COUNT}. The period ${PAPER_PERIOD.toLocaleString("en-US")} is unchanged either way.`,
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
      "The hug walk is a rotation. Its mean charge is C_*, Ostrowski digits of L have sum s(L), and Denjoy–Koksma on certified convergent blocks gives |C_L − C_*| ≤ 2s(L)/L. Lean certifies the sandwich arithmetic; the variation bound is written.",
    theorem: "Theorem 5.7 Ostrowski / Denjoy–Koksma envelope",
    tag: "EXACT — HUMAN PROOF",
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
  {
    plain:
      "On an odd-to-odd edge the unused upper cell is at least three: x³ + 3 ≤ (J(x)+1)².",
    theorem: "Lemma 6.3a (floorPower_odd_image_upper_gap)",
    tag: "EXACT — LEAN VERIFIED",
  },
  {
    plain:
      "Upper cells on the sorted log-log grid bound the surplus. The finite geometric form is Lean; the written charge supplies the cells.",
    theorem: "Proposition 6.3b upper-cell charge (Lean finite bounds; written cells)",
    tag: "EXACT — HUMAN PROOF",
  },
  {
    plain:
      "An actual cubic-band cycle at the leftover counts (780239, 492276, 287963) must have 350,000,000 < m < 520,000,000. Lean owns the cutoff shape; the numerical comparison is computation. This does not exclude period 780239.",
    theorem: "Corollary 6.3c leftover minimum window",
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
  {
    term: "Cubic band",
    meaning:
      "A primitive cycle with minimum m > 1 and maximum M < m³. Odds sit below m²; the CycleMin word is mechanical.",
  },
  {
    term: "Leftover counts",
    meaning:
      "The first surviving triple after Corollary 5.11: (L, o, e) = (780239, 492276, 287963).",
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
  "Cubic-band order and the height strips are not a halt theorem and do not raise the period 780239.",
  "Corollary 6.3c does not exclude period 780239. It only squeezes the minimum at those leftover counts.",
  "The uniform wrong-parity intersection on the threshold map remains open.",
  "A laboratory kill of the remaining near-convergents is closed. The next useful floor 5.54·10⁸ is parked; this site does not raise N₀.",
  "The signed first-triple test (UC6) is an exact reformulation, not a proved inequality.",
  "Theorem 3.31 needs a cycle minimum at least 300 and an enumeration of 325452 seven-even forms. Theorem 3.22 remains the statement proved in Lean for every n at least 2, and the interactive checker implements that one.",
  "No independence-from-Peano-arithmetic claim is made. Goodstein is a different theorem.",
  "Paper B (parity discrepancy and descent densities) is a different manuscript.",
] as const;

/** Separate from CLAIM_ROWS: Paper C Lean names are not this scoreboard. */
export const PAPER_C_CLAIM_ROWS = [
  {
    plain:
      "On a good fiber the scarcer half of the circle is at least H/3 − 2 once m ≥ 10⁶ and the step stays away from 0 and 1/2.",
    theorem: "Paper C Lemma 4.2 parity sweep",
    tag: "EXACT — HUMAN PROOF",
  },
  {
    plain:
      "Averaging the even-m fibers of E(m') gives a 1/4 share of even images after an error 250 m'^{11/9} log(m'+1).",
    theorem: "Paper C Proposition 4.4 even-block average",
    tag: "EXACT — HUMAN PROOF",
  },
  {
    plain:
      "Three pairwise disjoint families fill A ∩ (√x, x]. Items 1+2 give λ* = 0.3774; adding the rest drops 3t/8 from 1/3 to 1/9 and gives λ_pair = 0.4480.",
    theorem: "Paper C §5.1–5.2 three sources",
    tag: "EXACT — HUMAN PROOF",
  },
  {
    plain:
      "The official contagion exponent λ** = 0.4926 is the V6 truncation. The ideal share of a production word is available exactly when ρ_w ≤ 1/2.",
    theorem: "Paper C Theorem 5.3 / Proposition 5.13",
    tag: "EXACT — HUMAN PROOF",
  },
] as const;

export const PAPER_C_NOT_CLAIMED = [
  "Paper C excludes no fate and is not a halt theorem.",
  "Official λ** = 0.4926 is the V6 truncation, not the three-source recursion.",
  "The depth-two ideal 0.4927 is a method ceiling, not a proved word list.",
  "Playground fiber shares and block averages are observations, not the sweep or van der Corput proofs.",
] as const;
