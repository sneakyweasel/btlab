export type TourSlug =
  | "the-map"
  | "cycle-itinerary"
  | "cycle-survivors"
  | "expanding"
  | "envelope"
  | "run-suffix"
  | "preimages"
  | "oe-fiber"
  | "descent-floor"
  | "finance"
  | "gap-transfer"
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
    body:
      "$J$ is the one-step map; the sequence is the flight $n$, $J(n)$, $J^2(n)$, … . Values are the trajectory; the O/E word is the itinerary. The paper does not prove that every start reaches 1.",
    paper: "§1: $J$, $E$, $O$, trajectory, itinerary, $3^o/2^k$. Lemma 1.1: three fates.",
  },
  {
    slug: "cycle-itinerary",
    number: 2,
    term: "At the Cycle’s Abyss",
    blurb:
      "The black ring marks CycleMin, the smallest value. That bead is odd and the next one is too; an even returns, and four evens are forced in Lean (Theorem 3.22); eight once the minimum is at least 300 (Theorem 3.31).",
    body:
      "A cycle itinerary is a nonempty word that sends $n$ back to $n$. CycleMin is the rotation at the smallest value: it starts OO and ends E. The stem is the walk before the first visit — not a cycle itinerary. The unique known loop is 1.",
    paper:
      "§1 and Theorem 3.2: CycleMin. Theorem 3.22: $\\#E \\ge 4$ in Lean. Theorem 3.31: $\\#E \\ge 8$ once the minimum is at least 300. `IdealCycleMin.lean`.",
  },
  {
    slug: "cycle-survivors",
    number: 3,
    term: "Cycle survivors",
    blurb:
      "A survivor of an easy kill is still not a cycle.",
    body:
      "CycleMin shape is necessary, not a cycle: $O^7EEEE$ inhabits the shape and never returns (`CycleMinShape_not_of_CycleMin`). A three-valley spelling such as $O^3EO^2EO^2EE$ is shaped and not an `assembleFill`. A finance survivor such as 365 is the same warning. None of these close.",
    paper:
      "`CycleMinShape_not_of_CycleMin`. Theorems 3.12–3.21 kill short even-counts. Finance survivors are not cycles.",
  },
  {
    slug: "expanding",
    number: 4,
    term: "Expanding versus contracting",
    blurb: "Count the O letters. Compare $3^o$ with 2 to the length. A real loop must expand.",
    body:
      "Ignoring floors, $o$ odd letters and length $L$ would multiply $n$ by $3^o/2^L$. If that ratio is less than 1 the itinerary is contracting; if it is greater, expanding. A contracting itinerary cannot close a nontrivial cycle. That is why every real loop must have enough O letters to beat the even shrinks — and, later, at least four E letters in Lean, eight once the minimum is at least 300.",
    paper: "Theorem 3.2: a nontrivial cycle itinerary is formally expanding.",
  },
  {
    slug: "envelope",
    number: 5,
    term: "Power envelope",
    blurb: "If a start actually follows an itinerary, the result cannot outrun a known power bound.",
    body:
      "Floors only make the walk smaller than the ideal power. So after a realized itinerary of length $k$ with $o$ odd letters, the image sits at most at $n$ to the power $3^o/2^k$. Slack $\\Delta$ is the room left under that ceiling: $n^{3^o}$ minus the image to the power $2^k$. Section 4 uses this envelope. The exact leftover composition of Appendix C is a different identity and is not an input to the finance theorem.",
    paper: "Theorem 2.2 / Corollary 2.3: the finite-itinerary power envelope.",
  },
  {
    slug: "run-suffix",
    number: 6,
    term: "Run-suffix law",
    blurb:
      "One odd run, one suffix, one inequality. Eleven exclusions are ten evaluations of it.",
    body:
      "**The split.** Rotate a hypothetical cycle to its smallest value and read a maximal odd run $O^a$ followed by a suffix $u$ that is empty or begins with an even letter. The backward exponent $T(u)=2^{|u|}/3^{\\#O(u)}$ is one factor 2 per even letter and one factor $2/3$ per odd letter, read from the return backwards. At leading order the law says $(3/2)^a \\le T(u)$: the whole word must be formally expanding, and no tail of it beginning with an odd letter may be. That is the mirror of Theorem 3.2(i).\n\n**The crossing.** Lemma 3.24 puts a closed-form lower envelope under the state after the run; Lemma 3.25 puts an integer upper envelope $B(u)$ on the state entering the suffix. They collide once the cycle minimum is large enough. The crude form (Theorem 3.26) pays a factor 4 and needs a margin $\\log 4 / \\log n$; the sharp form (Theorem 3.29) uses the minimum at every step of the run and pays only $(1+1/n)$. The $a=7$ sharp chain is `O7EEEEGap.lean`. Empty suffix is the whole word as a tail: the envelope sits at $n$ itself and the law degenerates to finance.\n\n**The table.** Each of the ten suffixes is one evaluation of the same inequality. Nine least-$a$ values are the ones the leftover-family theorems print; for $u=E$ the law strengthens Lemma 3.4(v) and kills OOE at $n \\ge 1032$. The sharp thresholds are all at most 7. Theorem 3.31 then enumerates the seven-even forms and doubles the floor-free period to 22 once the minimum is at least 300. That census is not Lean, and the CycleMin checker stays on Theorem 3.22.",
    paper:
      "§3.9: Lemmas 3.24–3.25, Theorems 3.26 and 3.29, Corollaries 3.27 and 3.30, Theorem 3.31, Remark 3.32. `O7EEEEGap.lean` is the $a=7$ sharp chain. The CycleMin checker stays on Theorem 3.22.",
  },
  {
    slug: "preimages",
    number: 7,
    term: "One-step preimages",
    blurb:
      "J is not invertible. A backward-closed set swallows the even square interval of every member.",
    body:
      "Work backwards. $J$ is not invertible, so the one-step preimage of $m$ is a set. If $J(n)$ is in a backward-closed class $A$ then $n$ is in $A$. The even block $E(m)$ is every even $n$ in the square interval from $m^2$ to $(m+1)^2$; each has $J(n)=m$, so the whole block joins $A$. An odd image still has at most one odd parent. The OE fiber is a different production and lives on the next page. None of this excludes a fate.",
    paper:
      "Paper C Lemma 3.1; Lean `even_block_mem`. Odd one-step uniqueness is Paper A Lemma 3.1.",
  },
  {
    slug: "oe-fiber",
    number: 8,
    term: "OE fiber",
    blurb:
      "Odd $n$ with floor of $n$ to the three-fourths equal to $m$. Those whose next image is even join $A$ in two steps.",
    body:
      "The OE fiber $\\Phi(m)$ is every odd $n$ with $\\lfloor n^{3/4}\\rfloor = m$. Sea beads have even $\\lfloor n^{3/2}\\rfloor$, so $J(J(n))=m$ and they join a backward-closed $A$. Ember beads sit on the fiber but do not use this production. The printed figure is $m=100{,}000$: $H$ odd $n$ on the interval, $G$ of them with even image. Along the fiber the quantity $\\{n^{3/2}/2\\}$ advances by a nearly constant step, and both colors appear. Shares on this $m$ are an observation, not the sweep proof. None of this excludes a fate.",
    paper:
      "Paper C Lemmas 3.2 and 4.1; Lean `oe_fiber_mem`. The printed fiber is $m=10^5$.",
  },
  {
    slug: "descent-floor",
    number: 9,
    term: "Verified descent floor N₀",
    blurb: "Every start from 2 through $N_0$ has already been checked to reach 1. A floor is an input.",
    body:
      "$N_0$ is not the theorem. It is a certified computation you feed the inequality. Paper A uses four floors: the known $10^6$, the laboratory floor $26{,}254{,}995$, the second floor $162{,}849{,}448$, and the main printed floor $350{,}000{,}000$. Combined with finance and walk charge, those floors become period lower bounds. Raising $N_0$ is more computation, not a new idea, and it is not a halt theorem.",
    paper: "§1 and Proposition 1.3 / 5.1, Corollaries 5.10–5.11: floors are computational inputs.",
  },
  {
    slug: "finance",
    number: 10,
    term: "Finance",
    blurb:
      "Ideal dynamics expands, exact dynamics returns; the difference is paid in floor crumbs, and the crumbs run out.",
    body:
      "**The necklace.** Rotate a hypothetical cycle so that its minimum $n$ comes first. Its word is then a necklace of blocks $O^{a}E$: from a valley at least $n$, a run of odd climbs to an even peak, one square root down to the next valley. Each block has an ideal exponent $\\mu(a)=3^a/2^{a+1}$; OE contracts ($3/4$), OOE expands ($9/8$). The first two letters are OO and the first peak clears $(n+1)^2$. The last peak is the dynamical entry: an even integer in $[n^2+1,\\,(n+1)^2)$, so that one square root lands exactly on $n$.\n\n**The ledger.** Unroll the one-step floor defects around the necklace against the minimum. The word is formally expanding — $3^o>2^L$ — yet the trajectory returns, so the surplus $\\theta(L)=1-2^L/3^o$ must be financed by accumulated floor error: $n\\log n\\cdot(3^o-2^L)\\le L\\cdot 3^o$. The only analytic input is $\\log(1+u)\\le u$. The four forms of that inequality — constant 1, per-state defects, the statewise parity charge that yields $n_{\\max}(L)$, and the certified $6/5$ table — are rungs of one ladder and must not be conflated.\n\n**The staircase.** For each length, $n_{\\max}(L)$ is the largest minimum the parity charge still allows. Once every start up to $N_0$ is known to reach 1, a length with $n_{\\max}(L)\\le N_0$ has no cycle. At the floor $10^6$ the bar clears the line first at $L=25{,}781$; the 141 lengths below $100{,}000$ that clear it are the finance survivors, and they sit on the lattice $a\\cdot(25781,\\,16266)+b\\cdot(1054,\\,665)$ around the convergents of $\\log 2/\\log 3$. Run-type packing kills 42 more. A survivor is a length the inequality did not kill; it is not a candidate cycle.",
    paper:
      "§4: the excursion necklace, Lemmas 4.1–4.3, Theorem 4.4 (finance, `cycleMin_finance`), Corollary 4.4c, Corollary 4.5, Theorem 4.6 (the $10^6$ table, 141 survivors), Theorems 4.7–4.8 (run packing), Proposition 4.9 (survivor lattice).",
  },
  {
    slug: "gap-transfer",
    number: 11,
    term: "Gap transfer",
    blurb:
      "The surplus is a linear form; Rhin kills only the short ones. The floors already do more.",
    body:
      "**The linear form.** Rotate a hypothetical cycle to its minimum $n$. Finance bounds the surplus $\\theta=1-2^L/3^o$ by $L/(n\\log n)$. The same surplus is the linear form $\\Lambda=o\\log 3-L\\log 2=-\\log(1-\\theta)$. The only new inequality is $\\log\\frac{1}{1-\\theta}\\le\\frac{\\theta}{1-\\theta}$, and it turns the finance bound into $n\\log n\\cdot\\min(\\Lambda,1)\\le 2L$. That is Theorem 4.10, Lean name `cycleMin_gap_transfer`. A contracting pair is not a cycle; the inequality is then free.\n\n**The plane.** Rhin’s 1987 measure puts a classical lower bound under $\\Lambda$. Fed through the transfer, every pair with $L^{14.3}\\le n\\log n/915$ is short — excluded for every $n\\ge 2$. The complementary long regime is the open problem. The named finance survivors and fan members sit at $L\\approx n^{0.59}$, far above the frontier. Clicking a survivor marks it in the long regime; Rhin does not kill it.\n\n**The comparison.** At the printed floor $N_0=3.5\\cdot 10^8$ the Rhin reduction forces only $L\\ge 4$; Corollary 5.11 already has $L\\ge 780239$. The same gap holds at every certified floor. Corollary 4.11 is a floor-free reduction, weaker than the table, and does not kill the long survivors. Baker/Rhin as a leftover killer stays closed. The CycleMin checker stays on Theorem 3.22.",
    paper:
      "Theorem 4.10 (`cycleMin_gap_transfer`, `GapTransfer.lean`). Corollary 4.11: Rhin 1987 as hypothesis. The no-cycle problem is the exclusion of the long regime.",
  },
  {
    slug: "walk-charge",
    number: 12,
    term: "Walk charge",
    blurb: "Section 5 carries the same floor crumbs to one common currency, then prices the worst itinerary.",
    body:
      "Finance treats each step’s budget separately. Walk charge couples them: transport the losses to a reduced base, take the hug (rotation) itinerary as the adversary, identify that itinerary, and bound the average with Denjoy–Koksma over certified Ostrowski blocks. On the window $[50508,\\,16785921)$ — the whole semiconvergent fan — the charge bound is census-free. The kill itself is not: the comparison against $\\theta(L)$ is a per-length Diophantine quantity the envelope does not control, and that is what blocks the surviving fan members. This chapter is a picture only; the site does not recompute hug charge.",
    paper: "§5: transport, hug, itinerary identity, Denjoy–Koksma, window, Corollaries 5.10–5.11.",
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
