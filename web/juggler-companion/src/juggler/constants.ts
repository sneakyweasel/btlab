/**
 * Paper A printed constants. Display fork of
 * src/visualization/juggler_finite_dynamics.py — not a second theorem.
 */

export const TRAJECTORY_STEPS_MAX = 80;
export const DISPLAY_BITS_MAX = 256;
export const WORD_MAX = 8;
export const CYCLE_WORD_MAX = 16;
/** Tour strings may be longer than a leftover necklace (365 is 21 letters). */
export const TOUR_WORD_MAX = 24;
export const SLACK_BITS = 80;

export const PAPER_FLOOR = 1_000_000;
export const PAPER_PERIOD = 25_781;
export const PAPER_L_CAP = 100_000;
export const PAPER_EXCEPTION_COUNT = 141;
export const LAB_FLOOR = 26_254_995;
export const LAB_PARITY_PERIOD = 50_508;
export const LAB_WALK_PERIOD = 176_251;
export const PRINTED_FLOOR = 162_849_448;
export const PRINTED_PERIOD = 478_245;
export const WALK_WINDOW_LO = 50_508;
export const WALK_WINDOW_HI = 301_994;

export const NOTE_TRAJECTORY_3 = [3n, 5n, 11n, 36n, 6n, 2n, 1n] as const;
export const NOTE_PEAK_37 = 24_906_114_455_136n;

export const N_PRESETS = [
  { label: "3 — note trajectory", value: 3n },
  { label: "37 — note peak", value: 37n },
  { label: "1999 — four-block", value: 1999n },
] as const;

/** Live map starts: the browser walks these under the 256-bit cap. */
export const LIVE_STARTS = [
  {
    label: "3",
    value: 3n,
    note: "The printed trajectory of 3: OOOEEE to 1. Hitting 1 here is one trajectory, not a halt proof.",
  },
  {
    label: "9",
    value: 9n,
    note: "A short live walk under the 256-bit cap, easy to step through.",
  },
  {
    label: "37 peak",
    value: 37n,
    note: "Paper A’s note peak: a small start that climbs high, then falls. One walk, not a theorem.",
  },
  {
    label: "5 OE",
    value: 5n,
    note: "First OE meeting at 11: 5 -O→ 11 ←E- 122. Collision Factorization witness, not a leftover-killer.",
  },
  {
    label: "122 OE",
    value: 122n,
    note: "Even parent of the first OE meeting at 11. Pair with 5. Not a cycle.",
  },
  {
    label: "100 EE",
    value: 100n,
    note: "First EE meeting at 10: 100 → 10 ← 102. Collision Factorization witness, not a leftover-killer.",
  },
  {
    label: "102 EE",
    value: 102n,
    note: "Even parent of the first EE meeting at 10. Pair with 100. Not a cycle.",
  },
  {
    label: "113",
    value: 113n,
    note: "A longer live walk that still fits in the browser walker.",
  },
  {
    label: "365 leftover",
    value: 365n,
    note: "A finance leftover: the inequality did not kill this shape. That is not a cycle.",
  },
  {
    label: "1999",
    value: 1999n,
    note: "A four-block start from the playground list. Still live, under 256 bits.",
  },
] as const;

/** Live-walkable starts shown on the monster chip row. */
export const MONSTER_ROW_LIVE = [
  {
    label: "2^32",
    value: 4294967296n,
    note: "Even tower 2^32 → 2^16 → … → 1. The browser can walk it. Not a shipped peak and not a theorem.",
  },
] as const;

export const ITINERARY_PRESETS = ["OOE", "OOOEE", "OOOEOE", "OOOOEE"] as const;
export const CYCLE_PRESETS = [
  "OOOOOOOEEEE",
  "OOOOOOEEEOE",
  "OOOEOOEOOEE",
  "OOE",
  "OEO",
] as const;

export const CYCLE_TOUR_PRESET_GROUPS = [
  { role: "survivor", label: "Survivors" },
  { role: "killed", label: "Easy kills" },
  { role: "off-shape", label: "Outside CycleMin" },
] as const;

export type CycleTourPresetRole = (typeof CYCLE_TOUR_PRESET_GROUPS)[number]["role"];

export const CYCLE_TOUR_PRESETS = [
  {
    id: "o7eeee",
    role: "survivor",
    word: "OOOOOOOEEEE",
    label: "O⁷EEEE",
    hint: "CycleMin shape, four trailing evens. Survivor of the even-count kill: not a cycle.",
  },
  {
    id: "o6eeeoe",
    role: "survivor",
    word: "OOOOOOEEEOE",
    label: "O⁶EEEOE",
    hint: "OE seam: isolated last E. Survivor of the even-count kill: not a cycle.",
  },
  {
    id: "three-valleys",
    role: "survivor",
    word: "OOOEOOEOOEE",
    label: "3 valleys",
    hint: "CycleMin shape with three odd-runs. Not an assembleFill. Not a cycle.",
  },
  {
    id: "ooe",
    role: "killed",
    word: "OOE",
    label: "OOE",
    hint: "Too few evens. Expanding, not superquadratic. Killed already.",
  },
  {
    id: "oeo",
    role: "killed",
    word: "OEO",
    label: "OEO",
    hint: "Starts OE, not OO. Too few evens. Killed already.",
  },
  {
    id: "offcut",
    role: "off-shape",
    word: "EEOOOOOOOEE",
    label: "Wrong cut",
    hint: "O⁷EEEE rotated off the minimum. This cut is not CycleMin.",
  },
  {
    id: "pin-2005",
    role: "off-shape",
    word: "OOEEEOOOOOE",
    label: "pin (2,0,0,5)",
    hint: "Necklace pin miss. Last odd-run 5. Outside CycleMinShape.",
  },
  {
    id: "pin-3004",
    role: "off-shape",
    word: "OOOEEEOOOOE",
    label: "pin (3,0,0,4)",
    hint: "Necklace pin miss. Last odd-run 4. Outside CycleMinShape.",
  },
] as const;

export type IdealTone = "sure" | "count" | "unknown";
export type IdealBead = {
  letter: "O" | "E" | "?";
  tone: IdealTone;
};

/** Mirrors `BalloonStation` in `formal/Problems/Juggler/IdealCycleMin.lean`. */
export type EvenRole = "first" | "middle" | "last";
export type IntervalOddKind = "a1Extras" | "middle" | "lastZeroOrOne";
export type BalloonStation =
  | { kind: "sureLaunchO" }
  | { kind: "sureEven"; role: EvenRole }
  | { kind: "intervalOdd"; odd: IntervalOddKind }
  | { kind: "intervalExtraEven" };

export type BalloonIntervalKind =
  | IntervalOddKind
  | "extraEven";

export type BalloonInterval = {
  afterBead: number;
  kind: BalloonIntervalKind;
  min: number;
  max: number | null;
  label: string;
};

/**
 * Candidate bead schema in CycleMin reading order.
 * Same order as Lean `balloonSchema`. The full e-run is Lean
 * (`cycleMin_has_full_odd_even_run_form`); this schema is a projection
 * of that run list. `assembleFill` is not a characterization.
 */
export const BALLOON_SCHEMA: readonly BalloonStation[] = [
  { kind: "sureLaunchO" },
  { kind: "intervalOdd", odd: "a1Extras" },
  { kind: "sureEven", role: "first" },
  { kind: "intervalOdd", odd: "middle" },
  { kind: "sureEven", role: "middle" },
  { kind: "intervalExtraEven" },
  { kind: "sureEven", role: "middle" },
  { kind: "intervalOdd", odd: "lastZeroOrOne" },
  { kind: "sureEven", role: "last" },
];

/**
 * Default painted stem is not sure `OOE`. Lean `defaultStemSlots` is one
 * unknown-color `0+` slot. Optional launching `OO` lives in `lollipop.ts`.
 */
export const IDEAL_STRING_BEADS: readonly IdealBead[] = [
  { letter: "?", tone: "unknown" },
];

/**
 * Collapse a known-parity unknown-count run to one bead.
 * The stem keeps a single unknown-color 0+ slot.
 */
export function packCountRuns(beads: readonly IdealBead[]): IdealBead[] {
  const packed: IdealBead[] = [];
  for (const bead of beads) {
    const last = packed.at(-1);
    if (bead.tone === "count" && last?.tone === "count" && last.letter === bead.letter) {
      continue;
    }
    packed.push(bead);
  }
  return packed;
}

function sureBeadsFromSchema(schema: readonly BalloonStation[]): IdealBead[] {
  const beads: IdealBead[] = [];
  for (const station of schema) {
    if (station.kind === "sureLaunchO") {
      beads.push({ letter: "O", tone: "sure" }, { letter: "O", tone: "sure" });
    } else if (station.kind === "sureEven") {
      beads.push({ letter: "E", tone: "sure" });
    }
  }
  return beads;
}

/**
 * Six sure letters from the Lean candidate schema: launch OO and four E.
 * Interval slots are bounds, not letter beads.
 */
export const IDEAL_BALLOON_BEADS: readonly IdealBead[] =
  sureBeadsFromSchema(BALLOON_SCHEMA);

/** Lean `sureLink_iff`: exactly two table adjacencies are sure. */
export const SURE_LINKS: readonly (readonly [number, number])[] = [
  [0, 1],
  [5, 0],
];

export const IDEAL_BALLOON_INTERVALS: readonly BalloonInterval[] = [
  { afterBead: 1, kind: "a1Extras", min: 0, max: null, label: "a₁ extras 0+" },
  { afterBead: 2, kind: "middle", min: 0, max: null, label: "middle 0+" },
  { afterBead: 3, kind: "extraEven", min: 0, max: null, label: "extra E 0+" },
  { afterBead: 4, kind: "lastZeroOrOne", min: 0, max: 1, label: "aₑ ∈ {0,1}" },
];

export function intervalBoundLabel(interval: BalloonInterval): string {
  return interval.max === null
    ? `${interval.min}+`
    : `${interval.min} or ${interval.max}`;
}

/** Leftover count, not a letter. aₑ is the other kind. */
export function intervalIsMass(interval: BalloonInterval): boolean {
  return interval.kind !== "lastZeroOrOne";
}

/** Ring-facing slot name. Not the lattice family index. */
export function intervalSlotName(interval: BalloonInterval): string {
  switch (interval.kind) {
    case "a1Extras":
      return "a₁";
    case "middle":
      return "a∗";
    case "extraEven":
      return "e₊";
    case "lastZeroOrOne":
      return "aₑ";
  }
}

/** Known parity, unknown count. Not a sure letter. */
export function intervalCountBead(interval: BalloonInterval): IdealBead {
  return {
    letter: interval.kind === "extraEven" ? "E" : "O",
    tone: "count",
  };
}

export const IDEAL_STRING_LETTERS = IDEAL_STRING_BEADS.map(
  (bead) => bead.letter,
);
export const IDEAL_BALLOON_LETTERS = IDEAL_BALLOON_BEADS.map(
  (bead) => bead.letter,
);

/**
 * First-visit stops that are forced to exist: two launch O and four E.
 * Interval slots may be empty, so they are not stops.
 */
export function idealJoinSpots(
  beads: readonly IdealBead[] = IDEAL_BALLOON_BEADS,
): number[] {
  return beads.flatMap((bead, index) => (bead.tone === "sure" ? [index] : []));
}

export function stepIdealJoin(
  joinIndex: number,
  delta: number,
  spots: readonly number[] = idealJoinSpots(),
): number {
  if (spots.length === 0) return 0;
  const at = spots.indexOf(joinIndex);
  const from = at === -1 ? 0 : at;
  const span = spots.length;
  return spots[(((from + delta) % span) + span) % span];
}

export function idealJoinLabel(
  index: number,
  beads: readonly IdealBead[] = IDEAL_BALLOON_BEADS,
): string {
  if (index === 0) return "CycleMin n";
  if (index === 1 && beads[1]?.letter === "O") return "launch O";
  const sureEvens = beads.flatMap((bead, beadIndex) =>
    bead.letter === "E" && bead.tone === "sure" ? [beadIndex] : [],
  );
  const evenAt = sureEvens.indexOf(index);
  if (evenAt === 0) return "first E";
  if (evenAt === sureEvens.length - 1) return "last E";
  if (evenAt > 0) return `E ${evenAt + 1}`;
  return beads[index]?.letter ?? "?";
}

/** Capture stems onto the only known cycle {1}. Not nontrivial cycles. */
export const STRING_TOUR_PRESETS = [
  {
    id: "3",
    label: "3",
    hint: "The printed walk: one climb, then EEE into 1.",
    states: [3n, 5n, 11n, 36n, 6n, 2n, 1n],
  },
  {
    id: "7",
    label: "7 · OEEE",
    hint: "Named capture block OEEE. Still a string onto 1.",
    states: [7n, 18n, 4n, 2n, 1n],
  },
  {
    id: "9",
    label: "9 · two climbs",
    hint: "OOEOEEE: a second peak, then it joins the walk of 3 at 11.",
    states: [9n, 27n, 140n, 11n, 36n, 6n, 2n, 1n],
  },
  {
    id: "16",
    label: "16 · even tower",
    hint: "All-E string. Nested square roots, no odd climb.",
    states: [16n, 4n, 2n, 1n],
  },
  {
    id: "25",
    label: "25 · three climbs",
    hint: "OOOEEOEOEEE. Passes through the OEEE capture of 7.",
    states: [25n, 125n, 1397n, 52214n, 228n, 15n, 58n, 7n, 18n, 4n, 2n, 1n],
  },
  {
    id: "69",
    label: "69 · repeated block",
    hint: "OOEOOEEE then the walk of 3. Expanding transient, then capture.",
    states: [69n, 573n, 13716n, 117n, 1265n, 44992n, 212n, 14n, 3n, 5n, 11n, 36n, 6n, 2n, 1n],
  },
  {
    id: "365",
    label: "365 leftover",
    hint: "Finance leftover shape that still captures. Six odd-runs, not a cycle.",
    states: [
      365n, 6973n, 582276n, 763n, 21075n, 3059506n, 1749n, 73145n, 19782308n,
      4447n, 296551n, 161491284n, 12707n, 1432400n, 1196n, 34n, 5n, 11n, 36n, 6n,
      2n, 1n,
    ],
  },
] as const;
export const RECORD_LENGTHS = [1, 3, 11, 19, 84, 569, 1054, 25781, 50508] as const;

/**
 * Starts for the excursion necklace of §4. The browser walks each start
 * for |word| realized steps and reads the wave; whether the word is
 * followed is reported, never assumed. None of these is a cycle.
 */
export const NECKLACE_PRESETS = [
  {
    id: "365",
    n: 365n,
    word: "OOEOOEOOEOOEOEEEOOEEE",
    label: "365 · six excursions",
    hint: "The finance-leftover shape: four OOE climbs, then the wave falls through n. Not a cycle minimum.",
  },
  {
    id: "1999",
    n: 1999n,
    word: "OOEOOOOEEOOE",
    label: "1999 · rising valleys",
    hint: "Valleys 1999 → 5169 → 50093 → 193753: the four consecutive expanding blocks of §6. The first peak overshoots; nothing lands.",
  },
  {
    id: "o7eeee-5",
    n: 5n,
    word: "OOOOOOOEEEE",
    label: "O⁷EEEE at 5",
    hint: "The CycleMin-shaped survivor tried on a real start: the walk leaves the word at the third letter.",
  },
  {
    id: "37",
    n: 37n,
    word: "OOOOEOOOEEOOEEEEE",
    label: "37 · the note peak",
    hint: "Three blocks, then a tower of evens. The second peak is the printed 24,906,114,455,136, far above (n+1)².",
  },
] as const;

/** Necklace words are capped like tour strings. */
export const NECKLACE_WORD_MAX = 32;
