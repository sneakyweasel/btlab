export type TourSlug =
  | "the-map"
  | "cycle-itinerary"
  | "cycle-survivors"
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
      "J is the one-step map; the sequence is the flight n, J(n), J²(n), … . Values are the trajectory; the O/E word is the itinerary. The paper does not prove that every start reaches 1.",
    paper: "§1: J, E, O, trajectory, itinerary, 3^o/2^k. Lemma 1.1: three fates.",
  },
  {
    slug: "cycle-itinerary",
    number: 2,
    term: "At the Cycle’s Abyss",
    blurb:
      "The black ring marks CycleMin, the smallest value. That bead is odd and the next one is too; an even returns, and four evens are forced.",
    body:
      "A cycle itinerary is a nonempty word that sends n back to n. CycleMin is the rotation at the smallest value: it starts OO and ends E. The stem is the walk before the first visit — not a cycle itinerary. The unique known loop is 1.",
    paper:
      "§1 and Theorem 3.2: CycleMin. Theorem 3.22: #E ≥ 4. IdealCycleMin.lean.",
  },
  {
    slug: "cycle-survivors",
    number: 3,
    term: "Cycle survivors",
    blurb:
      "A survivor of an easy kill is still not a cycle.",
    body:
      "CycleMin shape is necessary, not a cycle: O⁷EEEE inhabits the shape and never returns (CycleMinShape_not_of_CycleMin). A three-valley spelling such as O³EO²EO²EE is shaped and not an assembleFill. A finance survivor such as 365 is the same warning. None of these close.",
    paper:
      "CycleMinShape_not_of_CycleMin. Theorems 3.12–3.21 kill short even-counts. Finance survivors are not cycles.",
  },
  {
    slug: "expanding",
    number: 4,
    term: "Expanding versus contracting",
    blurb: "Count the O letters. Compare 3^o with 2 to the length. A real loop must expand.",
    body:
      "Ignoring floors, o odd letters and length L would multiply n by 3^o / 2^L. If that ratio is less than 1 the itinerary is contracting; if it is greater, expanding. A contracting itinerary cannot close a nontrivial cycle. That is why every real loop must have enough O letters to beat the even shrinks — and, later, at least four E letters.",
    paper: "Theorem 3.2: a nontrivial cycle itinerary is formally expanding.",
  },
  {
    slug: "envelope",
    number: 5,
    term: "Power envelope",
    blurb: "If a start actually follows an itinerary, the result cannot outrun a known power bound.",
    body:
      "Floors only make the walk smaller than the ideal power. So after a realized itinerary of length k with o odd letters, the image sits at most at n to the power 3^o / 2^k. Slack Δ is the room left under that ceiling: n^{3^o} minus the image to the power 2^k. Section 4 uses this envelope. The exact leftover composition of Appendix C is a different identity and is not an input to the finance theorem.",
    paper: "Theorem 2.2 / Corollary 2.3: the finite-itinerary power envelope.",
  },
  {
    slug: "preimages",
    number: 6,
    term: "One-step preimages",
    blurb: "J is not invertible. The one-step preimage of m is a set. Even parents fill a square interval. An odd image has at most one odd parent.",
    body:
      "Work backwards. J is not invertible, so the one-step preimage of an image m is a set: J^{-1}(m) = {k : J(k) = m}. That is an exact integer interval in N, not an approximation. The even numbers that map to q are exactly the even integers in [q², (q+1)²). The odd numbers that map to m sit in a much thinner one-step preimage: there is at most one integer n with m² ≤ n³ < (m+1)². That asymmetry is how Paper A classifies short loop-shapes. Local leftover spellings are itineraries the easy one-step preimages did not kill — they are not open cycles.",
    paper: "§1 one-step preimage; Lemma 3.1: odd one-step preimages are unique. Even one-step preimages are square intervals.",
  },
  {
    slug: "descent-floor",
    number: 7,
    term: "Verified descent floor N₀",
    blurb: "Every start from 2 through N₀ has already been checked to reach 1. A floor is an input.",
    body:
      "N₀ is not the theorem. It is a certified computation you feed the inequality. Paper A uses three floors: the known 10⁶, the laboratory floor 26,254,995, and the printed floor 162,849,448. Combined with finance, those floors become period lower bounds. Raising N₀ is more computation, not a new idea, and it is not a halt theorem.",
    paper: "§1 and Proposition 1.3 / 5.1, Corollary 5.10: floors are computational inputs.",
  },
  {
    slug: "finance",
    number: 8,
    term: "Finance",
    blurb:
      "Ideal dynamics expands, exact dynamics returns; the difference is paid in floor crumbs, and the crumbs run out.",
    body:
      "The necklace. Rotate a hypothetical cycle so that its minimum n comes first. Its word is then a necklace of blocks O^{a}E: from a valley at least n, a run of odd climbs to an even peak, one square root down to the next valley. Each block has an ideal exponent μ(a) = 3^a / 2^{a+1}; OE contracts (3/4), OOE expands (9/8). The first two letters are OO and the first peak clears (n+1)². The last peak is the dynamical entry: an even integer in [n²+1, (n+1)²), so that one square root lands exactly on n.\n\nThe ledger. Unroll the one-step floor defects around the necklace against the minimum. The word is formally expanding — 3^o > 2^L — yet the trajectory returns, so the surplus θ(L) = 1 − 2^L/3^o must be financed by accumulated floor error: n log n · (3^o − 2^L) ≤ L · 3^o. The only analytic input is log(1+u) ≤ u. The four forms of that inequality — constant 1, per-state defects, the statewise parity charge that yields n_max(L), and the certified 6/5 table — are rungs of one ladder and must not be conflated.\n\nThe staircase. For each length, n_max(L) is the largest minimum the parity charge still allows. Once every start up to N₀ is known to reach 1, a length with n_max(L) ≤ N₀ has no cycle. At the floor 10⁶ the bar clears the line first at L = 25,781; the 141 lengths below 100,000 that clear it are the finance survivors, and they sit on the lattice a·(25781, 16266) + b·(1054, 665) around the convergents of log 2 / log 3. Run-type packing kills 42 more. A survivor is a length the inequality did not kill; it is not a candidate cycle.",
    paper:
      "§4: the excursion necklace, Lemmas 4.1–4.3, Theorem 4.4 (finance, cycleMin_finance), Corollary 4.4c, Corollary 4.5, Theorem 4.6 (the 10⁶ table, 141 survivors), Theorems 4.7–4.8 (run packing), Proposition 4.9 (survivor lattice).",
  },
  {
    slug: "walk-charge",
    number: 9,
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
