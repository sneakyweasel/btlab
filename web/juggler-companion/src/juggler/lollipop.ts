/**
 * Mirrors `formal/Problems/Juggler/IdealLollipop.lean`.
 * The companion may not paint a mark Lean does not have.
 */
import {
  IDEAL_BALLOON_BEADS,
  idealJoinLabel,
  type IdealBead,
} from "./constants";

export type FigureMark =
  | "forced"
  | "optional"
  | "unknown"
  | "leftover"
  | "offFigure";

export type CycleArrival = "oArrival" | "eArrival";

export type ArrivalRigidity =
  | { kind: "rigid"; arr: CycleArrival }
  | { kind: "dependsOnFill" };

export type StemTerminal = "even" | "unknown";

export type SureLetterSite =
  | "valley"
  | "launchO"
  | "firstE"
  | "middleE"
  | "thirdE"
  | "lastE"
  | "extraLetter";

export type CutForbidden = "rotateEven" | "rotateOE";

export type StemKind = "empty" | "capture" | "descent" | "join";

export type WitnessFate = "compiledCycle" | "leftover" | "capture";

export type StemDisplayMode = "empty" | "unknownSlot" | "optionalLaunch";

export type PaintedBead = {
  letter: "O" | "E" | "?";
  tone: IdealBead["tone"];
  mark: FigureMark;
  caption?: string;
  glyph?: string;
};

export type CycleFigure = {
  launchOO: FigureMark;
  fourSureE: FigureMark;
  expanding: FigureMark;
  evenCountGe4: FigureMark;
  oddCountGe7: FigureMark;
  lengthGe11: FigureMark;
  a1Ge2: FigureMark;
  lastOddLe1: FigureMark;
  twoSeams: FigureMark;
  firstEvenOvershoot: FigureMark;
  lastEvenCell: FigureMark;
  lastEvenNeOddSq: FigureMark;
  valleyOdd: FigureMark;
  twoSureLinks: FigureMark;
  hugPrefix: FigureMark;
  shapeNotCycle: FigureMark;
};

export const SCHEMATIC_CYCLE_FIGURE: CycleFigure = {
  launchOO: "forced",
  fourSureE: "forced",
  expanding: "forced",
  evenCountGe4: "forced",
  oddCountGe7: "forced",
  lengthGe11: "forced",
  a1Ge2: "forced",
  lastOddLe1: "forced",
  twoSeams: "forced",
  firstEvenOvershoot: "forced",
  lastEvenCell: "forced",
  lastEvenNeOddSq: "forced",
  valleyOdd: "forced",
  twoSureLinks: "forced",
  hugPrefix: "forced",
  shapeNotCycle: "leftover",
};

export type JoinFigure = {
  site: SureLetterSite;
  index: number;
  rigidity: ArrivalRigidity;
  terminal: StemTerminal;
  vertex: "O" | "E" | "?";
  isValley: boolean;
  cutForbiddens: readonly CutForbidden[];
  lean: string;
  arrivalWhy: string;
  cycleParent: string;
  stem: string;
  allowed: string;
  forbidden: readonly string[];
};

export type RealizedWitness = {
  n: bigint;
  word: string;
  fate: WitnessFate;
  joinIndex: number;
  stemParent: bigint | null;
  label: string;
};

export type IdealLollipop = {
  cycle: CycleFigure;
  stem: StemKind;
  join: JoinFigure;
  witness: RealizedWitness | null;
};

export function stemTerminalOf(arr: CycleArrival): StemTerminal {
  return arr === "oArrival" ? "even" : "unknown";
}

export function siteRigidity(site: SureLetterSite): ArrivalRigidity {
  if (site === "valley" || site === "thirdE") return { kind: "rigid", arr: "eArrival" };
  if (site === "launchO" || site === "firstE") return { kind: "rigid", arr: "oArrival" };
  return { kind: "dependsOnFill" };
}

export function siteVertex(site: SureLetterSite): "O" | "E" | "?" {
  if (site === "valley" || site === "launchO") return "O";
  if (site === "extraLetter") return "?";
  return "E";
}

export function siteCutForbiddens(site: SureLetterSite): CutForbidden[] {
  if (site === "valley" || site === "extraLetter") return [];
  if (site === "launchO") return ["rotateOE"];
  return ["rotateEven"];
}

export function joinTerminal(rigidity: ArrivalRigidity): StemTerminal {
  return rigidity.kind === "rigid" ? stemTerminalOf(rigidity.arr) : "unknown";
}

const SITE_COPY: Record<
  Exclude<SureLetterSite, "extraLetter">,
  Pick<JoinFigure, "lean" | "arrivalWhy" | "cycleParent" | "stem" | "allowed" | "forbidden">
> = {
  valley: {
    arrivalWhy: "Last letter is E (valley_is_eArrival). An odd cyclic parent of n is impossible.",
    cycleParent: "even, last-even cell [n^2, (n+1)^2)",
    stem: "another even in that cell, or the unique odd parent (then t < n)",
    allowed: "First meeting at the valley.",
    forbidden: [
      "odd cyclic parent (join_valley_arrival_even / cycleMin_not_end_odd)",
      "two odd parents (odd_parents_eq)",
    ],
    lean: "valley_is_eArrival, eArrival_stem_parent_cases, valley_stem_cases, oArrival_stem_even",
  },
  launchO: {
    arrivalWhy: "Previous letter is the valley O (launchO_is_oArrival). Cycle arrives O.",
    cycleParent: "n, odd, at least the valley",
    stem: "even parents of T(n) only",
    allowed: "First meeting at T(n).",
    forbidden: [
      "odd stem (oArrival_stem_even / join_arrives_odd_external_even)",
      "CycleMin cut starting here (rotate_OE_not_cycleMin)",
    ],
    lean: "launchO_is_oArrival, oArrival_stem_even, rotate_OE_not_cycleMin",
  },
  firstE: {
    arrivalWhy: "a1 extras are odds, or the second launch O (cycleMin_firstE_follows_odd_run).",
    cycleParent: "odd, at least the valley",
    stem: "even parents of the first peak only",
    allowed: "First meeting at the first peak.",
    forbidden: [
      "odd stem (cycle owns the unique odd parent)",
      "CycleMin cut starting here (rotate_even_not_cycleMin)",
    ],
    lean: "cycleMin_firstE_follows_odd_run, odd_run_terminates_oArrival, rotate_even_not_cycleMin",
  },
  middleE: {
    arrivalWhy:
      "Middle odd slot may be empty (arrive from first E) or occupied (arrive O). Fill-dependent.",
    cycleParent: "odd and ≥ n if the middle odds fire; even in the square cell if they do not",
    stem: "even-only if arrival O; even or odd if arrival E",
    allowed: "First meeting at this sure E. The middle slot itself is not a stop.",
    forbidden: [
      "joining the empty middle interval (not a vertex)",
      "CycleMin cut starting here (rotate_even_not_cycleMin)",
    ],
    lean: "join_middleE_depends, join_arrives_odd_external_even / join_arrives_even_cycle_parent_cell",
  },
  thirdE: {
    arrivalWhy:
      "On the balloon / assembleFill the previous station is even (assembleFill_empty_thirdE_eArrival). A general CycleMin third even need not be.",
    cycleParent: "even, square cell of this vertex",
    stem: "other evens in that cell, and the odd parent if occupied",
    allowed: "First meeting on this extra-even side.",
    forbidden: [
      "joining the extra-E interval when it is empty",
      "CycleMin cut starting here (rotate_even_not_cycleMin)",
    ],
    lean: "join_thirdE_rigid_e, assembleFill_empty_thirdE_eArrival, rotate_even_not_cycleMin",
  },
  lastE: {
    arrivalWhy: "Last odd-run a_e is 0 (arrive E) or 1 (arrive O). Fill-dependent.",
    cycleParent: "the last peak's predecessor: even if a_e = 0, odd if a_e = 1",
    stem: "even-only if a_e = 1; even or odd if a_e = 0",
    allowed: "First meeting at the last peak. One more step is the valley.",
    forbidden: [
      "joining the a_e slot when it is empty",
      "CycleMin cut starting here (rotate_even_not_cycleMin)",
    ],
    lean: "join_lastE_depends, exists_cycleMin_last_odd_run",
  },
};

const SURE_SITES: readonly Exclude<SureLetterSite, "extraLetter">[] = [
  "valley",
  "launchO",
  "firstE",
  "middleE",
  "thirdE",
  "lastE",
];

export function joinFigure(site: SureLetterSite, index = siteIndex(site)): JoinFigure {
  const rigidity = siteRigidity(site);
  const copy =
    site === "extraLetter"
      ? {
          arrivalWhy: "Not a sure-letter stop on this schema.",
          cycleParent: "the unique cyclic predecessor of this vertex",
          stem: "any other parent",
          allowed: "A realized extra letter can be a first meeting.",
          forbidden: ["interval slots that may be empty"],
          lean: "every_orbit_index_is_join_site, cycle_in_edge_unique_at, join_extraLetter_depends",
        }
      : SITE_COPY[site];
  return {
    site,
    index,
    rigidity,
    terminal: joinTerminal(rigidity),
    vertex: siteVertex(site),
    isValley: site === "valley",
    cutForbiddens: siteCutForbiddens(site),
    ...copy,
  };
}

export function siteIndex(site: SureLetterSite): number {
  const at = SURE_SITES.indexOf(site as Exclude<SureLetterSite, "extraLetter">);
  return at === -1 ? -1 : at;
}

export function siteAtIndex(index: number): SureLetterSite {
  return SURE_SITES[index] ?? "extraLetter";
}

/** Lean `sureLetterJoinTable`: six sure letters. */
export const SURE_LETTER_JOIN_TABLE: readonly JoinFigure[] = SURE_SITES.map((site, index) =>
  joinFigure(site, index),
);

export const JOIN_INTERVALS_NOT_STOPS =
  "Interval slots may be empty, so they are not join stops. every_orbit_index_is_join_site is about realized vertices.";

export const JOIN_VS_WORD_ROTATION =
  "Join left/right walks the stem around sure letters. Necklace rotate changes the CycleMin cut. Cuts that start E or OE are not CycleMin.";

export const FIGURE_BANNER =
  "No nontrivial cycle is known. This is CycleMin geometry, not a realized loop. The only compiled cycle is {1}.";

export const DEFAULT_STEM_BEADS: readonly PaintedBead[] = [
  {
    letter: "?",
    tone: "unknown",
    mark: "unknown",
    caption: "0+",
    glyph: "0+",
  },
];

export const OPTIONAL_LAUNCH_STEM: readonly PaintedBead[] = [
  { letter: "O", tone: "sure", mark: "optional", caption: "optional" },
  { letter: "O", tone: "sure", mark: "optional", caption: "optional" },
  { letter: "?", tone: "unknown", mark: "unknown", caption: "unknown", glyph: "0+" },
];

export function terminalBead(join: JoinFigure): PaintedBead {
  if (join.terminal === "even") {
    return { letter: "E", tone: "sure", mark: "forced", caption: "t even" };
  }
  return { letter: "?", tone: "unknown", mark: "unknown", caption: "t = E|O" };
}

export function paintStem(mode: StemDisplayMode, join: JoinFigure): PaintedBead[] {
  if (mode === "empty") return [];
  if (mode === "unknownSlot") {
    return [...DEFAULT_STEM_BEADS, terminalBead(join)];
  }
  return [...OPTIONAL_LAUNCH_STEM, terminalBead(join)];
}

export function toIdealBead(bead: PaintedBead): IdealBead {
  return { letter: bead.letter, tone: bead.tone };
}

export function defaultStemIsNotSureOOE(beads: readonly PaintedBead[]): boolean {
  const sure = beads.filter((bead) => bead.mark === "forced" || bead.tone === "sure");
  return sure.map((bead) => bead.letter).join("") !== "OOE";
}

export const SCHEMATIC_LOLLIPOP: IdealLollipop = {
  cycle: SCHEMATIC_CYCLE_FIGURE,
  stem: "empty",
  join: joinFigure("valley", 0),
  witness: null,
};

export const COMPILED_CYCLE_WITNESS: RealizedWitness = {
  n: 1n,
  word: "O",
  fate: "compiledCycle",
  joinIndex: 0,
  stemParent: null,
  label: "{1}",
};

export const WALK_OF_3_WITNESS: RealizedWitness = {
  n: 3n,
  word: "OOOEEE",
  fate: "capture",
  joinIndex: 0,
  stemParent: 2n,
  label: "walk of 3",
};

export const EVEN_TOWER_WITNESS: RealizedWitness = {
  n: 16n,
  word: "EEE",
  fate: "capture",
  joinIndex: 0,
  stemParent: 2n,
  label: "even tower",
};

export const LEFTOVER_O7EEEE_WITNESS: RealizedWitness = {
  n: 0n,
  word: "OOOOOOOEEEE",
  fate: "leftover",
  joinIndex: 0,
  stemParent: null,
  label: "O⁷EEEE",
};

export const PIN_MISS_WORDS = ["OOEEEOOOOOE", "OOOEEEOOOOE"] as const;

export function arrivalLetter(join: JoinFigure): "O" | "E" | "O_or_E" {
  if (join.rigidity.kind === "dependsOnFill") return "O_or_E";
  return join.rigidity.arr === "oArrival" ? "O" : "E";
}

export function stemTerminalLetterUi(join: JoinFigure): "E" | "E_or_O" {
  return join.terminal === "even" ? "E" : "E_or_O";
}

/** Display row used by the join card. Names come from JoinFigure. */
export type JoinConfig = {
  index: number;
  site: SureLetterSite;
  name: string;
  vertex: "O" | "E" | "?";
  arrival: "O" | "E" | "O_or_E";
  arrivalWhy: string;
  cycleParent: string;
  stem: string;
  stemTerminal: "E" | "E_or_O";
  rigidity: ArrivalRigidity;
  allowed: string;
  forbidden: readonly string[];
  lean: string;
  isValley: boolean;
  fillDependent: boolean;
};

export function joinFigureToConfig(
  join: JoinFigure,
  beads: readonly IdealBead[] = IDEAL_BALLOON_BEADS,
): JoinConfig {
  return {
    index: join.index,
    site: join.site,
    name: join.index >= 0 ? idealJoinLabel(join.index, beads) : "extra letter",
    vertex: join.vertex,
    arrival: arrivalLetter(join),
    arrivalWhy: join.arrivalWhy,
    cycleParent: join.cycleParent,
    stem: join.stem,
    stemTerminal: stemTerminalLetterUi(join),
    rigidity: join.rigidity,
    allowed: join.allowed,
    forbidden: join.forbidden,
    lean: join.lean,
    isValley: join.isValley,
    fillDependent: join.rigidity.kind === "dependsOnFill",
  };
}

export function idealJoinConfig(
  index: number,
  beads: readonly IdealBead[] = IDEAL_BALLOON_BEADS,
): JoinConfig {
  return joinFigureToConfig(joinFigure(siteAtIndex(index), index), beads);
}

export function stemTerminalLetter(joinIndex: number): "E" | "E_or_O" {
  return idealJoinConfig(joinIndex).stemTerminal;
}

export function stemBeadsForJoin(
  joinIndex: number,
  mode: StemDisplayMode = "unknownSlot",
): PaintedBead[] {
  return paintStem(mode, joinFigure(siteAtIndex(joinIndex), joinIndex));
}

export function captureWitnessFromStates(
  states: readonly bigint[],
  label: string,
): RealizedWitness | null {
  if (states.length < 2 || states.at(-1) !== 1n) return null;
  const word = states
    .slice(0, -1)
    .map((state) => (state % 2n === 1n ? "O" : "E"))
    .join("");
  return {
    n: states[0] ?? 0n,
    word,
    fate: "capture",
    joinIndex: 0,
    stemParent: states.at(-2) ?? null,
    label,
  };
}

export function paintCaptureStem(witness: RealizedWitness): PaintedBead[] {
  return Array.from(witness.word).map((letter, index) => ({
    letter: letter === "O" ? "O" : "E",
    tone: "sure" as const,
    mark: "offFigure" as const,
    caption: index === witness.word.length - 1 ? "onto {1}" : undefined,
  }));
}
