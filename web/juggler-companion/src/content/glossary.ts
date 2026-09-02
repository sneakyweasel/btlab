export type TourSlug =
  | "the-map"
  | "trajectory-word"
  | "cycle-word"
  | "expanding"
  | "envelope"
  | "cells"
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
      "Even numbers shrink. Odd numbers grow. Decimals vanish. Do it forever?",
    body:
      "J is the one-step map. The Juggler sequence starting at n is the trajectory of iterates n, J(n), J²(n), … . Floor means the integer part: remove everything after the decimal point. So floor(5.196) = 5 and floor(6) = 6. Start with a positive integer n. If n is even, take the square root and then floor. If n is odd, raise n to the three-halves and then floor: floor(n^{3/2}) = floor(n√n) = floor(√(n³)). That is not the cube root. The floor is applied after every step, not once at the end. Those two rules are the whole map. Paper A writes the even branch as E and the odd branch as O. The leftover crumbs after each floor are what later inequalities budget. The paper does not prove that every start reaches 1.",
    paper: "Abstract and §1: the map J, floor, the even branch E, and the odd branch O. Lemma 1.1 lists the three possible fates.",
  },
  {
    slug: "trajectory-word",
    number: 2,
    term: "Trajectory and word",
    blurb: "The trajectory is the list of values. The word is the list of odd/even letters.",
    body:
      "Apply J again and again. The sequence of values is the trajectory (also called an orbit in some dynamics texts). The word of the first k steps is the length-k string over {O, E} that records the parity of each value: O if that value is odd, E if it is even. The word is not the trajectory. The integer k is any finite prefix; the definition does not assume that the walk reaches 1. A word is realized at n only when the trajectory of n actually follows those parities — a formal string that no start follows is not an itinerary. Ignoring floors, o odd letters in length k would multiply by 3^o / 2^k; that ratio is the ideal exponent of the word. The famous walk of 3 is 3, 5, 11, 36, 6, 2, 1, with realized word OOOEEE. Hitting 1 here is one trajectory, not a proof that every start does.",
    paper: "§1: trajectory, word, realized word, and ideal exponent 3^o/2^k.",
  },
  {
    slug: "cycle-word",
    number: 3,
    term: "Cycle word and CycleMin",
    blurb: "A loop of O and E letters. Rotating it is the same loop from a different start.",
    body:
      "If a nonempty word sends n back to n, that word is a cycle word. The unique fixed point is 1; a cycle is nontrivial when it contains some n ≥ 2. Rotate the necklace and you still have the same loop. CycleMin is the rotation that starts at the smallest value on the loop. Paper A’s finance inequality is always written at that minimum.",
    paper: "§1 conventions and Theorem 3.2: cycle words, minimum-based rotations.",
  },
  {
    slug: "expanding",
    number: 4,
    term: "Expanding versus contracting",
    blurb: "Count the O letters. Compare 3^o with 2 to the length. A real loop must expand.",
    body:
      "Ignoring floors, o odd letters and length L would multiply n by 3^o / 2^L. If that ratio is less than 1 the word is contracting; if it is greater, expanding. A contracting word cannot close a nontrivial cycle. That is why every real loop must have enough O letters to beat the even shrinks — and, later, at least four E letters.",
    paper: "Theorem 3.2: a nontrivial cycle word is formally expanding.",
  },
  {
    slug: "envelope",
    number: 5,
    term: "Power envelope",
    blurb: "If a start actually follows a word, the result cannot outrun a known power bound.",
    body:
      "Floors only make the walk smaller than the ideal power. So after a realized word of length k with o odd letters, the image sits at most at n to the power 3^o / 2^k. Slack Δ is the room left under that ceiling: n^{3^o} minus the image to the power 2^k. Section 4 uses this envelope. The exact leftover composition of Appendix C is a different identity and is not an input to the finance theorem.",
    paper: "Theorem 2.2 / Corollary 2.3: the finite-word power envelope.",
  },
  {
    slug: "cells",
    number: 6,
    term: "Inverse cells",
    blurb: "J is not invertible. The preimage of m is a set. Even parents fill a square interval. An odd image has at most one odd parent.",
    body:
      "Work backwards. J is not invertible, so the preimage of an image m is a set: the cell J^{-1}(m) = {k : J(k) = m}. That is an exact integer interval in N, not a cellular-automaton cell and not an approximation. The even numbers that map to q are exactly the even integers in [q², (q+1)²). The odd numbers that map to m sit in a much thinner cell: there is at most one integer n with m² ≤ n³ < (m+1)². That asymmetry is how Paper A classifies short loop-shapes. Local leftover spellings are words the easy cells did not kill — they are not open cycles.",
    paper: "§1 cell / preimage; Lemma 3.1: odd cells are unique. Even cells are square intervals.",
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
    blurb: "At a cycle minimum the surplus 3^o − 2^L must be paid by a finite budget of floor crumbs.",
    body:
      "Write the envelope at the smallest point of a hypothetical loop. The formal surplus 3^o − 2^L has to be paid by accumulated floor error. That is the inequality n log n · (3^o − 2^L) ≤ L · 3^o. With the floor 10⁶ it excludes every period at most 25,780. A length the table does not kill is a finance-survivor. That is not evidence for a cycle.",
    paper: "Theorem 4.4 (finance) and Theorem 4.6 (the 10⁶ instance).",
  },
  {
    slug: "walk-charge",
    number: 9,
    term: "Walk charge",
    blurb: "Section 5 carries the same floor crumbs to one common currency, then prices the worst word.",
    body:
      "Finance treats each step’s budget separately. Walk charge couples them: transport the losses to a reduced base, take the hug (rotation) word as the adversary, identify that word, and bound the average with Denjoy–Koksma over certified Ostrowski blocks. On the window [50508, 301994) this is census-free. The printed bound L ≥ 478245 is a certified evaluation of the same kill criterion at the second floor — not an extension of that window. This chapter is a picture only; the site does not recompute hug charge.",
    paper: "§5: transport, hug, word identity, Denjoy–Koksma, window, Corollary 5.10.",
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
