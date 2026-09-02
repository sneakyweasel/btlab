export type DecisionKind = "theorem" | "optional" | "leftover" | "off-figure";

export type DecisionFocus =
  | "figure"
  | "string"
  | "string-oo"
  | "string-grey"
  | "string-e"
  | "join"
  | "balloon"
  | "balloon-oo"
  | "balloon-e"
  | "balloon-fade"
  | "balloon-seam"
  | "balloon-first-e"
  | "none";

export type IdealDecision = {
  id: string;
  part: "shared" | "string" | "cycle" | "escape";
  kind: DecisionKind;
  focus: DecisionFocus;
  title: string;
  why: string;
  lemma: string;
};

export const DECISION_PARTS = ["shared", "string", "cycle", "escape"] as const;

export const DECISION_PART_LABEL: Record<(typeof DECISION_PARTS)[number], string> = {
  shared: "Shared layer",
  string: "Stem",
  cycle: "Cycle",
  escape: "Not this figure",
};

export const DECISION_KIND_LABEL: Record<DecisionKind, string> = {
  theorem: "theorem",
  optional: "optional stem",
  leftover: "leftover",
  "off-figure": "off-figure",
};

/**
 * One row per figure decision, keyed to the itinerary-structure extract.
 * Optional stem marks stay visible; they are not CycleMin theorems.
 */
export const IDEAL_DECISIONS: readonly IdealDecision[] = [
  {
    id: "fates",
    part: "shared",
    kind: "theorem",
    focus: "figure",
    title: "This picture is fate 2 only",
    why: "Lemma 1.1 allows reach 1, a nontrivial cycle, or an unbounded walk. The lollipop is a first visit onto a cycle. It does not say which fate occurs.",
    lemma: "Paper A Lemma 1.1",
  },
  {
    id: "realized",
    part: "shared",
    kind: "theorem",
    focus: "figure",
    title: "Every letter is a realized itinerary",
    why: "A formal O/E word that no start follows is not an itinerary. The figure is a shape, not a walk.",
    lemma: "J-itinerary-semantics",
  },
  {
    id: "envelope",
    part: "shared",
    kind: "theorem",
    focus: "figure",
    title: "The envelope binds stem and cycle",
    why: "Every realized finite word obeys the power envelope. A contracting prefix of the stem is descent, not a cycle. A contracting cycle cannot close.",
    lemma: "J-power-envelope-contraction",
  },
  {
    id: "cells",
    part: "shared",
    kind: "theorem",
    focus: "join",
    title: "The join uses one-step cells",
    why: "Even parents of n fill a square interval. An odd image has at most one odd parent. First meeting is Collision Factorization: off-cycle parent t, on-cycle parent c, child J(t)=J(c).",
    lemma: "J-inverse-preimage-asymmetry",
  },
  {
    id: "empty-string",
    part: "string",
    kind: "theorem",
    focus: "string-grey",
    title: "The string may be empty",
    why: "If the start is already on the cycle there is no preperiod. Grey ??? have minimum length 0. Three greys are a picture of unknown color, not a lower bound.",
    lemma: "J-itinerary-semantics",
  },
  {
    id: "string-oo",
    part: "string",
    kind: "optional",
    focus: "string-oo",
    title: "Solid OO on the stem is optional",
    why: "Launch OO is forced on the cycle, not on a preperiod. The even tower EEE is a legal stem onto 1. The stem OO is a launching first visit, not Theorem 3.2(ii).",
    lemma: "J-cycle-finite-structure — cycle only",
  },
  {
    id: "string-grey",
    part: "string",
    kind: "theorem",
    focus: "string-grey",
    title: "Stem ??? stay grey",
    why: "A string is not run form O^{a}E⋯O^{a}E. The middle is not tiled by OOE and OE. Color and count are both unknown. Fading them orange or teal would pretend we know the parity.",
    lemma: "J-itinerary-semantics",
  },
  {
    id: "string-e",
    part: "string",
    kind: "optional",
    focus: "string-e",
    title: "Solid t = E is optional",
    why: "The generic parent of any first visit sits in the even cell of that image. At most one odd parent exists. The figure draws that even t at every allowed join, not a theorem that every stem ends E.",
    lemma: "J-inverse-preimage-asymmetry",
  },
  {
    id: "join-seam",
    part: "string",
    kind: "optional",
    focus: "join",
    title: "Join can sit at any sure letter",
    why: "The join is the first meeting, not the CycleMin cut. On this figure the forced letters are two launch O and four E. Left and right step those six. Interval slots may be empty, so they are not stops. A real join can also sit in a realized extra odd.",
    lemma: "Collision Factorization",
  },
  {
    id: "string-descent",
    part: "string",
    kind: "theorem",
    focus: "string",
    title: "A contracting prefix is descent",
    why: "E, OE, OOEE, OOOEE, and OOEOE are certified descents. They may appear on a stem. They are not extra cycle odd-run mass.",
    lemma: "J-finite-progress-boundary, J-four-step-descent-density, J-five-step-descent-density",
  },
  {
    id: "string-capture",
    part: "string",
    kind: "theorem",
    focus: "string",
    title: "If the cycle is 1, the stem is a capture",
    why: "Named even-towers and OEEE reach 1. That is the only known cycle. Hitting 1 is one trajectory, not a halt theorem.",
    lemma: "Capture / even_tower_to_one",
  },
  {
    id: "string-hug",
    part: "string",
    kind: "theorem",
    focus: "string",
    title: "Hug does not bind a falling string",
    why: "Prefix-odd domination is proved on CycleMin and on AboveAnchor. A stem that descends toward a smaller cycle is not AboveAnchor, so it need not be hug-admissible.",
    lemma: "aboveAnchor_prefix_odds_ge_hug",
  },
  {
    id: "balloon-cut",
    part: "cycle",
    kind: "theorem",
    focus: "balloon",
    title: "The circle is a CycleMin rotation",
    why: "Every cycle has a rotation that starts at the smallest value. That minimum is odd. The knot is n, not 1 unless the cycle is {1}.",
    lemma: "J-cycle-finite-structure / exists_cycleMin",
  },
  {
    id: "balloon-oo",
    part: "cycle",
    kind: "theorem",
    focus: "balloon-oo",
    title: "Solid OO is a₁ ≥ 2",
    why: "A minimum spelling cannot start E or OE. Launch is OO: T(n) is odd and the first high leaves n. Lean names this cycleMin_launch_is_OO.",
    lemma: "cycleMin_launch_is_OO, cycleMin_starts_two_odds",
  },
  {
    id: "balloon-expand",
    part: "cycle",
    kind: "theorem",
    focus: "balloon-fade",
    title: "The cycle is expanding",
    why: "A mixed cycle must beat 2^L by 3^o. Four evens then force at least seven odds (cycleMin_oddCount_ge_seven), so extras past the two launch O have minimum 5 and stay unplaced. They are not five grey letter beads, and they are not fill-slot equalities on a general CycleMin word.",
    lemma: "cycle_itinerary_formally_expanding, cycleMin_oddCount_ge_seven, cycleMin_unplaced_odds_ge_five",
  },
  {
    id: "balloon-evens",
    part: "cycle",
    kind: "theorem",
    focus: "balloon-e",
    title: "Four solid E, period at least 11",
    why: "Fewer than four evens is impossible at n ≥ 2. Hence L ≥ 11. Extra evens past those four may lengthen an even-run; they are empty at the length-11 bound, so they are not a fifth E.",
    lemma: "J-even-count-le-three",
  },
  {
    id: "balloon-overshoot",
    part: "cycle",
    kind: "theorem",
    focus: "balloon-first-e",
    title: "First E overshoots; last E lands",
    why: "The first even sits at or above (n+1)², so the maximum is at least that. The last even lands in [n²+1, (n+1)²). Those can be the same even-run.",
    lemma: "cycleMin_firstEven_is_overshoot, cycleMin_lastEven_is_closure_cell, J-first-even-overshoots, J-cyclemax-succ-sq",
  },
  {
    id: "balloon-run",
    part: "cycle",
    kind: "theorem",
    focus: "balloon",
    title: "Lean has the first block, not the full e-run",
    why: "Lean proves w = O^{a₁}E ++ v with a₁ ≥ 2, and the last odd-run aₑ ≤ 1. The full spelling O^{a₁}E ⋯ O^{aₑ}E is Lemma 3.21b, still EXACT — HUMAN PROOF. The figure’s four-slot fill is a candidate schema, not that reconstruction.",
    lemma: "cycleMin_run_form_first_block, exists_cycleMin_last_odd_run, Paper A Lemma 3.21b",
  },
  {
    id: "balloon-seam",
    part: "cycle",
    kind: "theorem",
    focus: "balloon-seam",
    title: "Last odd-run aₑ ≤ 1",
    why: "The word ends O^a E with a ≤ 1. The wrap EO is a sure table link (sureLink_iff). Legal 2+2 seams are OE|n|OO and EE|n|OO. Trailing EE is realized when aₑ = 0, but it is not a sure (always-present) link. Forced isolated OE is refuted.",
    lemma: "cycleMin_wrap_is_EO, sureLink_iff, J-cyclemin-last-odd-run",
  },
  {
    id: "balloon-hug",
    part: "cycle",
    kind: "theorem",
    focus: "balloon",
    title: "Every CycleMin prefix is hug-admissible",
    why: "On the cycle, each prefix has at least hugOdds(k) odds (PrefixOddBudget). Extra odd-run mass may occupy the interval slots. Those slots are bounds, not letter beads: unused runs may be empty and the extra letters are not placed.",
    lemma: "cycleMin_bead_prefix_dominates_hug, cycleMin_prefix_odds_ge_hug, J-cyclemin-walk-word-identity",
  },
  {
    id: "balloon-fade",
    part: "cycle",
    kind: "theorem",
    focus: "balloon-fade",
    title: "Interval slots are bounds, not letter beads",
    why: "The Lean candidate schema has a₁ extras 0+, middle odd-runs 0+, aₑ ∈ {0,1}, and extra E 0+. cycleMin_projects_balloonSchema is projection onto forced stations, not an assembleFill reconstruction. Those marks sit between the six sure letters. They are not grey ? beads and they are not forced stations.",
    lemma: "cycleMin_projects_balloonSchema, Lemma 3.21b",
  },
  {
    id: "balloon-links",
    part: "cycle",
    kind: "theorem",
    focus: "balloon-oo",
    title: "Exactly two table links are sure",
    why: "sureLink_iff: the bead table forces only launch OO and the wrap EO. Trailing EE can appear when lastOdds = 0, but that adjacency is not a sure link. No other consecutive pair is always present.",
    lemma: "sureLink_iff, cycleMin_launch_is_OO, cycleMin_wrap_is_EO",
  },
  {
    id: "balloon-fill",
    part: "cycle",
    kind: "theorem",
    focus: "balloon-fade",
    title: "Fill counts are exact on assembleFill, not on CycleMin",
    why: "On a NecklaceFill, #O = 2+a₁+mid+last, #E = 4+extra, length = 6 plus those slots. Extra evens are bunched in one slot. A CycleMin-shaped word such as O³EO²EO²EE is not an assembleFill. There is no Lean map CycleMin → NecklaceFill.",
    lemma: "assembleFill_oddCount, assembleFill_evenCount, assembleFill_length, necklaceFill_unplaced_odd_budget",
  },
  {
    id: "balloon-parity",
    part: "cycle",
    kind: "theorem",
    focus: "balloon",
    title: "Cycle letters are O or E",
    why: "Every letter of a CycleMin word has known parity. Unknown beads are stem-only. The cycle schema never uses intervalUnknown.",
    lemma: "cycleMin_letters_known_parity, stem_slots_not_cycle_schema",
  },
  {
    id: "leftovers",
    part: "cycle",
    kind: "leftover",
    title: "Shape is not CycleMin",
    focus: "balloon-fade",
    why: "O⁷EEEE inhabits CycleMinShape and is not a cycle itinerary for any n (CycleMinShape_not_of_CycleMin). O⁶EEEOE and the (1,3) EEE family do the same. Fudge leftovers and slack 3^o−2^{o+4} live on those spellings, not on the ideal circle. Shape is necessary, not a cycle.",
    lemma: "CycleMinShape_not_of_CycleMin, J-o7eeee-gap, J-o6eeeoe-gap, J-one-three-eee-gap, J-cyclemin-fudge, J-cyclemin-slack, J-cyclemin-last-cluster, J-cyclemin-prefix-*",
  },
  {
    id: "even-count-leftovers",
    part: "cycle",
    kind: "leftover",
    focus: "balloon-e",
    title: "Fewer than four evens is already dead",
    why: "All-odd cannot return. One even dies by next-square. Two-even leftover families die by Theorem 3.12. Three-even bunched tails and gapped O^aEO^bEE / EOE die by Theorems 3.14–3.21. Those words never fill the circle.",
    lemma: "J-even-count-le-three, J-two-even-leftover-*, J-three-even-*, J-gapped-cycle-itinerary-*",
  },
  {
    id: "escape",
    part: "escape",
    kind: "theorem",
    focus: "none",
    title: "An unbounded walk has no cycle and no stem",
    why: "A descent-free flight is hug-admissible and has unbounded walk. It either enters a cycle above the floor or diverges with quantized near-returns. No stem is drawn for that fate.",
    lemma: "J-flight-walk-divergence, J-flight-envelope-transport, J-flight-height-law",
  },
  {
    id: "divergent",
    part: "escape",
    kind: "theorem",
    focus: "none",
    title: "Divergent structure is not this figure",
    why: "Record jumps live on the log₂ 3 lattice; shortest near-return 19. Hug circuits on leftover periods are OE/OOE. That is escape geometry, not a tiling of the stem.",
    lemma: "J-flight-divergent-structure, J-flight-return-quantization",
  },
  {
    id: "equidistribution",
    part: "shared",
    kind: "off-figure",
    focus: "none",
    title: "Equidistribution is not a bead law",
    why: "All-depth equidistribution would give density-one descent certificates. The implication is proved; the hypothesis is open past length 4. It does not constrain the lollipop.",
    lemma: "J-equidistribution-implies-density-one",
  },
  {
    id: "automatic",
    part: "shared",
    kind: "off-figure",
    focus: "none",
    title: "Automatic descent is fate 1, not the stem OO",
    why: "Every even start realizes E and descends. Odd-then-even realizes OE and descends. Those are termination certificates, not CycleMin launch.",
    lemma: "J-automatic-descent-density",
  },
];

export const HARVESTED_LEMMA_NEEDLES = [
  "Lemma 1.1",
  "J-itinerary-semantics",
  "J-power-envelope-contraction",
  "J-inverse-preimage-asymmetry",
  "J-finite-progress-boundary",
  "J-four-step-descent-density",
  "J-five-step-descent-density",
  "J-automatic-descent-density",
  "J-equidistribution-implies-density-one",
  "even_tower",
  "J-cycle-finite-structure",
  "cycleMin_starts_two_odds",
  "cycleMin_launch_is_OO",
  "cycleMin_wrap_is_EO",
  "cycleMin_firstEven_is_overshoot",
  "sureLink_iff",
  "assembleFill_oddCount",
  "CycleMinShape_not_of_CycleMin",
  "cycleMin_projects_balloonSchema",
  "cycleMin_bead_prefix_dominates_hug",
  "J-first-even-overshoots",
  "J-cyclemax-succ-sq",
  "J-even-count-le-three",
  "J-cyclemin-last-odd-run",
  "cycleMin_prefix_odds_ge_hug",
  "J-cyclemin-walk-word-identity",
  "aboveAnchor_prefix_odds_ge_hug",
  "J-two-even-leftover",
  "J-three-even",
  "J-gapped-cycle-itinerary",
  "J-o7eeee-gap",
  "J-o6eeeoe-gap",
  "J-one-three-eee-gap",
  "J-cyclemin-fudge",
  "J-cyclemin-slack",
  "J-cyclemin-last-cluster",
  "J-cyclemin-prefix",
  "J-flight-walk-divergence",
  "J-flight-envelope-transport",
  "J-flight-height-law",
  "J-flight-divergent-structure",
  "J-flight-return-quantization",
  "Lemma 3.21b",
] as const;
