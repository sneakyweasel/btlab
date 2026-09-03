export type TourSlug =
  | "the-map"
  | "cycle-itinerary"
  | "expanding"
  | "envelope"
  | "preimages"
  | "descent-floor"
  | "finance"
  | "walk-charge";

export type TourChapter = {
  slug: TourSlug;
  number: number;
  term: string;
  blurb: string;
  body: string;
  paper: string;
};

export const TOUR_CHAPTERS: TourChapter[] = [
  {
    slug: "the-map",
    number: 1,
    term: "The Juggler map",
    blurb:
      "Odds flap, evens fall, decimals shed—and still it flies.",
    // "Even numbers shrink. Odd numbers grow. Decimals vanish. Do it forever?",
    body:
      "J is that one-step map. The Juggler sequence is the flight: n, J(n), J²(n), … . Paper A writes the even drop as E and the odd leap as O. The sequence of values is the trajectory. The itinerary of a prefix is the O/E string of those parities — not the values. An itinerary is realized at n only when the walk actually follows those letters. Ignoring floors, o odd letters in k steps would send the start to n · 3^o / 2^k. The finished walk of 37 has 9 O letters in 17 steps (and 8 E letters), so the ideal exponent is 3^9 / 2^17 = 19683/131072 ≈ 0.150 < 1: contracting — even the ideal arithmetic shrinks. The crumbs that fall off each floor are the budget later inequalities will spend. The paper does not prove that every start reaches 1.",
    paper: "Abstract and §1: the map J, floor, the even branch E, the odd branch O, trajectory, itinerary, and the ideal exponent 3^o/2^k. Lemma 1.1 lists the three possible fates.",
  },
  {
    slug: "cycle-itinerary",
    number: 2,
    term: "At the Cycle’s Abyss",
    blurb:
      "The black ring marks CycleMin, the smallest value. That bead is odd and the next one is too; an even returns, and four evens are forced.",
    body:
      "If a nonempty itinerary sends n back to n, that itinerary is a cycle itinerary. The unique fixed point is 1; a cycle is nontrivial when it contains some n ≥ 2. Rotate the necklace and you still have the same loop. CycleMin is the rotation that starts at the smallest value. That minimum is odd, so the spelling cannot start E or OE: the first two letters are OO. It cannot end on an odd letter: the last letter is E. Paper A’s finance inequality is always written at that minimum. At that cut n is return, minimum, and launch at once: last peak lands by E, then OO leaves the minimum.\n\nThe stem is the realized itinerary before the first visit to the cycle. It is not a cycle itinerary. It may be empty if the start is already on the cycle. A contracting prefix of the stem is descent, not a cycle. If the cycle is 1, the stem is a capture. A return before the join would be a shorter cycle. The join is the first meeting of an off-cycle parent with an on-cycle parent — not the CycleMin cut unless they coincide. An unbounded walk has no cycle and no stem. The walk of 3 is the stem OOOEEE onto 1. The figure on this page is an idealization. The cycle is a Lean candidate schema: six sure letters (launch OO and four E) plus interval slots — a₁ extras 0+, middle odd-runs 0+, aₑ ∈ {0,1}, extra E 0+. Those slots are bounds, not grey letter beads. Lean projects a CycleMin word onto the forced stations (launch OO, wrap EO, first-E overshoot, last-E cell, #E ≥ 4, #O ≥ 7). The combinatorial e-run O^{a₁}E ⋯ O^{aₑ}E with e = #E, a₁ ≥ 2, aₑ ≤ 1 is Lean (cycleMin_has_full_odd_even_run_form). The bead schema is a projection of that run list, not an assembleFill reconstruction. Lemma 3.21b’s leftover use for e ≤ 3 stays the Paper A argument. On a fill the counts are exact: #O = 2+a₁+mid+last, #E = 4+extra. Extra evens are bunched in one slot, so a shaped leftover such as O³EO²EO²EE is not an assembleFill. The stem OO?E is an optional first visit; it may attach at any sure cycle letter, not only CycleMin. The stem ? is a 0+ slot. Cycle letters are O or E; unknown beads are stem-only. If a nontrivial cycle existed it would need that CycleMin shape. It would not need that stem.\n\nThe first even overshoots (n+1)²; the last even lands in [n²+1, (n+1)²). Exactly two table links are sure: launch OO and wrap EO. Exactly two letters can touch the minimum from behind: OE|n|OO (isolated last E) or EE|n|OO (trailing even run). Trailing EE is realized when aₑ = 0, but it is not a sure link. Fewer than four E letters is impossible, so a nontrivial period is at least 11. Shape is necessary, not a cycle: CycleMinShape_not_of_CycleMin, witness O⁷EEEE. The unique known loop is 1.",
    paper:
      "§1 conventions and Theorem 3.2: CycleMin geometry. Theorem 3.22: even-count ≥ 4. Last-odd-run and the two legal seams. Lean bead accounting: formal/Problems/Juggler/IdealCycleMin.lean.",
  },
  {
    slug: "expanding",
    number: 3,
    term: "Expanding versus contracting",
    blurb: "Count the O letters. Compare 3^o with 2 to the length. A real loop must expand.",
    body:
      "Ignoring floors, o odd letters and length L would multiply n by 3^o / 2^L. If that ratio is less than 1 the itinerary is contracting; if it is greater, expanding. A contracting itinerary cannot close a nontrivial cycle. That is why every real loop must have enough O letters to beat the even shrinks — and, later, at least four E letters.",
    paper: "Theorem 3.2: a nontrivial cycle itinerary is formally expanding.",
  },
  {
    slug: "envelope",
    number: 4,
    term: "Power envelope",
    blurb: "If a start actually follows an itinerary, the result cannot outrun a known power bound.",
    body:
      "Floors only make the walk smaller than the ideal power. So after a realized itinerary of length k with o odd letters, the image sits at most at n to the power 3^o / 2^k. Slack Δ is the room left under that ceiling: n^{3^o} minus the image to the power 2^k. Section 4 uses this envelope. The exact leftover composition of Appendix C is a different identity and is not an input to the finance theorem.",
    paper: "Theorem 2.2 / Corollary 2.3: the finite-itinerary power envelope.",
  },
  {
    slug: "preimages",
    number: 5,
    term: "One-step preimages",
    blurb: "J is not invertible. The one-step preimage of m is a set. Even parents fill a square interval. An odd image has at most one odd parent.",
    body:
      "Work backwards. J is not invertible, so the one-step preimage of an image m is a set: J^{-1}(m) = {k : J(k) = m}. That is an exact integer interval in N, not an approximation. The even numbers that map to q are exactly the even integers in [q², (q+1)²). The odd numbers that map to m sit in a much thinner one-step preimage: there is at most one integer n with m² ≤ n³ < (m+1)². That asymmetry is how Paper A classifies short loop-shapes. Local leftover spellings are itineraries the easy one-step preimages did not kill — they are not open cycles.",
    paper: "§1 one-step preimage; Lemma 3.1: odd one-step preimages are unique. Even one-step preimages are square intervals.",
  },
  {
    slug: "descent-floor",
    number: 6,
    term: "Verified descent floor N₀",
    blurb: "Every start from 2 through N₀ has already been checked to reach 1. A floor is an input.",
    body:
      "N₀ is not the theorem. It is a certified computation you feed the inequality. Paper A uses three floors: the known 10⁶, the laboratory floor 26,254,995, and the printed floor 162,849,448. Combined with finance, those floors become period lower bounds. Raising N₀ is more computation, not a new idea, and it is not a halt theorem.",
    paper: "§1 and Proposition 1.3 / 5.1, Corollary 5.10: floors are computational inputs.",
  },
  {
    slug: "finance",
    number: 7,
    term: "Finance",
    blurb: "At a cycle minimum the surplus 3^o − 2^L must be paid by a finite budget of floor crumbs.",
    body:
      "Write the envelope at the smallest point of a hypothetical loop. The formal surplus 3^o − 2^L has to be paid by accumulated floor error. That is the inequality n log n · (3^o − 2^L) ≤ L · 3^o. With the floor 10⁶ it excludes every period at most 25,780. A length the table does not kill is a finance-survivor. That is not evidence for a cycle.",
    paper: "Theorem 4.4 (finance) and Theorem 4.6 (the 10⁶ instance).",
  },
  {
    slug: "walk-charge",
    number: 8,
    term: "Walk charge",
    blurb: "Section 5 carries the same floor crumbs to one common currency, then prices the worst itinerary.",
    body:
      "Finance treats each step’s budget separately. Walk charge couples them: transport the losses to a reduced base, take the hug (rotation) itinerary as the adversary, identify that itinerary, and bound the average with Denjoy–Koksma over certified Ostrowski blocks. On the window [50508, 301994) this is census-free. The printed bound L ≥ 478245 is a certified evaluation of the same kill criterion at the second floor — not an extension of that window. This chapter is a picture only; the site does not recompute hug charge.",
    paper: "§5: transport, hug, itinerary identity, Denjoy–Koksma, window, Corollary 5.10.",
  },
];

export function chapterBySlug(slug: string | undefined): TourChapter | undefined {
  return TOUR_CHAPTERS.find((chapter) => chapter.slug === slug);
}

export function neighborChapters(slug: TourSlug): {
  prev: TourChapter | null;
  next: TourChapter | null;
} {
  const index = TOUR_CHAPTERS.findIndex((chapter) => chapter.slug === slug);
  return {
    prev: index > 0 ? TOUR_CHAPTERS[index - 1] : null,
    next: index >= 0 && index < TOUR_CHAPTERS.length - 1 ? TOUR_CHAPTERS[index + 1] : null,
  };
}
