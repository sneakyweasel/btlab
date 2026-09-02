export type DecisionKind = "theorem" | "cartoon" | "leftover" | "off-figure";

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
  part: "shared" | "string" | "balloon" | "escape";
  kind: DecisionKind;
  focus: DecisionFocus;
  title: string;
  why: string;
  lemma: string;
};

export const DECISION_PARTS = ["shared", "string", "balloon", "escape"] as const;

export const DECISION_PART_LABEL: Record<(typeof DECISION_PARTS)[number], string> = {
  shared: "Shared layer",
  string: "String",
  balloon: "Balloon",
  escape: "Not this figure",
};

export const DECISION_KIND_LABEL: Record<DecisionKind, string> = {
  theorem: "theorem",
  cartoon: "cartoon",
  leftover: "leftover",
  "off-figure": "off-figure",
};

/**
 * One row per figure decision, keyed to the itinerary-structure extract.
 * Cartoons stay visible; they are not CycleMin theorems.
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
    title: "The envelope binds string and balloon",
    why: "Every realized finite word obeys the power envelope. A contracting prefix of the string is descent, not a balloon. A contracting balloon cannot close.",
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
    why: "If the start is already on the balloon there is no preperiod. Grey ??? have minimum length 0. Three greys are a picture of unknown color, not a lower bound.",
    lemma: "J-itinerary-semantics",
  },
  {
    id: "string-oo",
    part: "string",
    kind: "cartoon",
    focus: "string-oo",
    title: "Solid OO on the stem is a cartoon",
    why: "Launch OO is forced on the balloon, not on a preperiod. The even tower EEE is a legal string onto 1. The stem OO is a launching first visit, not Theorem 3.2(ii).",
    lemma: "J-cycle-finite-structure — balloon only",
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
    kind: "cartoon",
    focus: "string-e",
    title: "Solid t = E is the even-parent cartoon",
    why: "If the first meeting is odd CycleMin n, the generic parent sits in the even cell of n. At most one odd parent exists. The figure draws that even t, not a theorem that every string ends E.",
    lemma: "J-inverse-preimage-asymmetry",
  },
  {
    id: "join-seam",
    part: "string",
    kind: "cartoon",
    focus: "join",
    title: "Join at CycleMin is one placement",
    why: "The join is the first meeting. It equals the CycleMin cut only if they coincide. The stem aims at n so the seam is visible. A join can sit elsewhere on the loop.",
    lemma: "Collision Factorization",
  },
  {
    id: "string-descent",
    part: "string",
    kind: "theorem",
    focus: "string",
    title: "A contracting prefix is descent",
    why: "E, OE, OOEE, OOOEE, and OOEOE are certified descents. They may appear on a string. They are not extra balloon odd-run mass.",
    lemma: "J-finite-progress-boundary, J-four-step-descent-density, J-five-step-descent-density",
  },
  {
    id: "string-capture",
    part: "string",
    kind: "theorem",
    focus: "string",
    title: "If the balloon is 1, the string is a capture",
    why: "Named even-towers and OEEE reach 1. That is the only known balloon. Hitting 1 is one trajectory, not a halt theorem.",
    lemma: "Capture / even_tower_to_one",
  },
  {
    id: "string-hug",
    part: "string",
    kind: "theorem",
    focus: "string",
    title: "Hug does not bind a falling string",
    why: "Prefix-odd domination is proved on CycleMin and on AboveAnchor. A string that descends toward a smaller balloon is not AboveAnchor, so it need not be hug-admissible.",
    lemma: "aboveAnchor_prefix_odds_ge_hug",
  },
  {
    id: "balloon-cut",
    part: "balloon",
    kind: "theorem",
    focus: "balloon",
    title: "The circle is a CycleMin rotation",
    why: "Every cycle has a rotation that starts at the smallest value. That minimum is odd. The knot is n, not 1 unless the balloon is {1}.",
    lemma: "J-cycle-finite-structure / exists_cycleMin",
  },
  {
    id: "balloon-oo",
    part: "balloon",
    kind: "theorem",
    focus: "balloon-oo",
    title: "Solid OO is a₁ ≥ 2",
    why: "A minimum spelling cannot start E or OE. Launch is OO: T(n) is odd and the first high leaves n.",
    lemma: "cycleMin_starts_two_odds",
  },
  {
    id: "balloon-expand",
    part: "balloon",
    kind: "theorem",
    focus: "balloon-fade",
    title: "The balloon is expanding",
    why: "A mixed cycle must beat 2^L by 3^o. At length 11 that forces o ≥ 7, so the five leftover letters at the bound are odds: O⁷EEEE.",
    lemma: "cycle_itinerary_formally_expanding",
  },
  {
    id: "balloon-evens",
    part: "balloon",
    kind: "theorem",
    focus: "balloon-e",
    title: "Four solid E, period at least 11",
    why: "Fewer than four evens is impossible at n ≥ 2. Hence L ≥ 11. Extra evens past those four may lengthen an even-run; they are empty at the length-11 bound, so they are not a fifth E.",
    lemma: "J-even-count-le-three",
  },
  {
    id: "balloon-overshoot",
    part: "balloon",
    kind: "theorem",
    focus: "balloon-first-e",
    title: "First E overshoots; last E lands",
    why: "The first even sits at or above (n+1)², so the maximum is at least that. The last even lands in [n²+1, (n+1)²). Those can be the same even-run.",
    lemma: "J-first-even-overshoots, J-cyclemax-succ-sq, cycle_last_even_interval",
  },
  {
    id: "balloon-run",
    part: "balloon",
    kind: "theorem",
    focus: "balloon",
    title: "Run form O^{a₁}E ⋯ O^{aₑ}E",
    why: "Lemma 3.21b after rotation to a minimum. Unused odd-runs may be empty, so consecutive E are allowed. Peak count equals circuit count m; p ≥ 3 is not a letter law.",
    lemma: "Paper A Lemma 3.21b",
  },
  {
    id: "balloon-seam",
    part: "balloon",
    kind: "theorem",
    focus: "balloon-seam",
    title: "Last odd-run aₑ ≤ 1",
    why: "The word ends O^a E with a ≤ 1. Legal 2+2 seams are OE|n|OO and EE|n|OO. Forced isolated OE is refuted.",
    lemma: "J-cyclemin-last-odd-run",
  },
  {
    id: "balloon-hug",
    part: "balloon",
    kind: "theorem",
    focus: "balloon",
    title: "Every CycleMin prefix is hug-admissible",
    why: "On the balloon, each prefix has at least hugOdds(k) odds. That is why extra odds sit as overlapping O in the odd-runs, not as a free grey color.",
    lemma: "cycleMin_prefix_odds_ge_hug, J-cyclemin-walk-word-identity",
  },
  {
    id: "balloon-fade",
    part: "balloon",
    kind: "theorem",
    focus: "balloon-fade",
    title: "Overlapping O is known parity, unknown count",
    why: "A stack is one letter that may repeat. Overlapping O is more a_i (minimum extra at L=11 is five odds). Extra E past the four forced evens are empty at that bound, so they do not get a fifth bead. Grey is reserved for unknown color on the stem.",
    lemma: "Lemma 3.21b + J-even-count-le-three",
  },
  {
    id: "leftovers",
    part: "balloon",
    kind: "leftover",
    title: "Leftover chips fill the overlapping letters",
    focus: "balloon-fade",
    why: "O⁷EEEE, O⁶EEEOE, and the (1,3) EEE family have CycleMin shape and still do not close. Fudge leftovers and slack 3^o−2^{o+4} live on those spellings, not on the ideal circle. They fill the overlapping stacks. Shape is necessary, not a cycle.",
    lemma: "J-o7eeee-gap, J-o6eeeoe-gap, J-one-three-eee-gap, J-cyclemin-fudge, J-cyclemin-slack, J-cyclemin-last-cluster, J-cyclemin-prefix-*",
  },
  {
    id: "even-count-leftovers",
    part: "balloon",
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
    title: "An unbounded walk has no balloon and no string",
    why: "A descent-free flight is hug-admissible and has unbounded walk. It either enters a cycle above the floor or diverges with quantized near-returns. No string is drawn for that fate.",
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
