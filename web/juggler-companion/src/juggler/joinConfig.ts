import {
  IDEAL_BALLOON_BEADS,
  IDEAL_STRING_BEADS,
  idealJoinLabel,
  type IdealBead,
} from "./constants";

/** Arrival letter of the cyclic parent at a sure-bead join. */
export type JoinArrival = "O" | "E" | "O_or_E";

export type StemTerminal = "E" | "E_or_O";

export type JoinSite =
  | "valley"
  | "launchO"
  | "firstE"
  | "middleE"
  | "thirdE"
  | "lastE";

export type JoinConfig = {
  index: number;
  site: JoinSite;
  name: string;
  vertex: "O" | "E";
  arrival: JoinArrival;
  arrivalWhy: string;
  cycleParent: string;
  stem: string;
  stemTerminal: StemTerminal;
  allowed: string;
  forbidden: readonly string[];
  lean: string;
};

/**
 * Lean-backed join table on the six sure letters.
 *
 * Every orbit index is a legal first-meeting site
 * (`every_orbit_index_is_join_site`). Interval slots may be empty, so
 * they are not stops. CycleMin *cuts* that start E or OE are forbidden
 * (`rotate_even_not_cycleMin`, `rotate_OE_not_cycleMin`); that is a
 * different rotation from walking the stem join.
 */
const JOIN_TABLE: readonly JoinConfig[] = [
  {
    index: 0,
    site: "valley",
    name: "CycleMin n",
    vertex: "O",
    arrival: "E",
    arrivalWhy: "Last letter is E. An odd cyclic parent of n is impossible.",
    cycleParent: "even, last-even cell [n^2, (n+1)^2)",
    stem: "another even in that cell, or the unique odd parent (then t < n)",
    stemTerminal: "E_or_O",
    allowed: "First meeting at the valley.",
    forbidden: [
      "odd cyclic parent (join_valley_arrival_even / cycleMin_not_end_odd)",
      "two odd parents (odd_parents_eq)",
    ],
    lean: "seam_parent_cases, join_valley_arrival_even, odd_parent_of_cycleMin_off_cycle",
  },
  {
    index: 1,
    site: "launchO",
    name: "launch O",
    vertex: "O",
    arrival: "O",
    arrivalWhy: "Cycle just left n by O. The unique odd parent is n itself.",
    cycleParent: "n, odd, at least the valley",
    stem: "even parents of T(n) only",
    stemTerminal: "E",
    allowed: "First meeting at T(n).",
    forbidden: [
      "odd stem (join_arrives_odd_external_even — the unique odd parent is already on-cycle)",
      "using this vertex as a CycleMin cut: the rotated word starts OE (rotate_OE_not_cycleMin)",
    ],
    lean: "join_arrives_odd_cycle_parent_ge, join_arrives_odd_external_even",
  },
  {
    index: 2,
    site: "firstE",
    name: "first E",
    vertex: "E",
    arrival: "O",
    arrivalWhy: "a1 extras are odds, or the second launch O. Cycle arrives O.",
    cycleParent: "odd, at least the valley",
    stem: "even parents of the first peak only",
    stemTerminal: "E",
    allowed: "First meeting at the first peak.",
    forbidden: [
      "odd stem (cycle owns the unique odd parent)",
      "reading this peak as the CycleMin cut (rotate_even_not_cycleMin)",
    ],
    lean: "join_arrives_odd_external_even, rotate_even_not_cycleMin",
  },
  {
    index: 3,
    site: "middleE",
    name: "E 2",
    vertex: "E",
    arrival: "O_or_E",
    arrivalWhy:
      "Middle odd slot may be empty (arrive from first E) or occupied (arrive O).",
    cycleParent: "odd and ≥ n if the middle odds fire; even in the square cell if they do not",
    stem: "even-only if arrival O; even or odd if arrival E",
    stemTerminal: "E_or_O",
    allowed: "First meeting at this sure E. The middle slot itself is not a stop.",
    forbidden: [
      "joining the empty middle interval (not a vertex)",
      "CycleMin cut starting here (rotate_even_not_cycleMin)",
    ],
    lean: "join_arrives_odd_external_even / join_arrives_even_cycle_parent_cell, cycle_in_edge_unique_at",
  },
  {
    index: 4,
    site: "thirdE",
    name: "E 3",
    vertex: "E",
    arrival: "E",
    arrivalWhy: "Previous sure bead is E, and extra evens are E. Arrival stays E.",
    cycleParent: "even, square cell of this vertex",
    stem: "other evens in that cell, and the odd parent if occupied",
    stemTerminal: "E_or_O",
    allowed: "First meeting on this extra-even side.",
    forbidden: [
      "joining the extra-E interval when it is empty",
      "CycleMin cut starting here (rotate_even_not_cycleMin)",
    ],
    lean: "join_arrives_even_cycle_parent_cell, cycle_in_edge_unique_at",
  },
  {
    index: 5,
    site: "lastE",
    name: "last E",
    vertex: "E",
    arrival: "O_or_E",
    arrivalWhy: "Last odd-run a_e is 0 (arrive E) or 1 (arrive O).",
    cycleParent: "the last peak's predecessor: even if a_e = 0, odd if a_e = 1",
    stem: "even-only if a_e = 1; even or odd if a_e = 0",
    stemTerminal: "E_or_O",
    allowed: "First meeting at the last peak. One more step is the valley.",
    forbidden: [
      "joining the a_e slot when it is empty",
      "CycleMin cut starting here (rotate_even_not_cycleMin)",
    ],
    lean: "exists_cycleMin_last_odd_run, join_arrives_odd_external_even / join_arrives_even_cycle_parent_cell",
  },
];

export function idealJoinConfig(
  index: number,
  beads: readonly IdealBead[] = IDEAL_BALLOON_BEADS,
): JoinConfig {
  const row = JOIN_TABLE.find((item) => item.index === index);
  if (row) {
    return { ...row, name: idealJoinLabel(index, beads) };
  }
  return {
    index,
    site: "middleE",
    name: idealJoinLabel(index, beads),
    vertex: beads[index]?.letter === "O" ? "O" : "E",
    arrival: "O_or_E",
    arrivalWhy: "Not a sure-letter stop on this schema.",
    cycleParent: "the unique cyclic predecessor of this vertex",
    stem: "any other parent",
    stemTerminal: "E_or_O",
    allowed: "A realized extra letter can be a first meeting.",
    forbidden: ["interval slots that may be empty"],
    lean: "every_orbit_index_is_join_site, cycle_in_edge_unique_at",
  };
}

export function stemTerminalLetter(joinIndex: number): StemTerminal {
  return idealJoinConfig(joinIndex).stemTerminal;
}

/** Last stem bead follows the join: even-only, or E-or-O. */
export function stemBeadsForJoin(joinIndex: number): IdealBead[] {
  const terminal = stemTerminalLetter(joinIndex);
  return IDEAL_STRING_BEADS.map((bead, index) => {
    if (index !== IDEAL_STRING_BEADS.length - 1) return bead;
    if (terminal === "E") return { letter: "E", tone: "sure" };
    return { letter: "?", tone: "unknown" };
  });
}

export const JOIN_INTERVALS_NOT_STOPS =
  "Interval slots may be empty, so they are not join stops. A realized extra odd or extra even is an ordinary orbit vertex.";

export const JOIN_VS_WORD_ROTATION =
  "Join left/right walks the stem around sure letters. Necklace rotate changes the CycleMin cut. Cuts that start E or OE are not CycleMin.";
