/**
 * Paper A printed constants. Display fork of
 * src/visualization/juggler_finite_dynamics.py — not a second theorem.
 */

export const TRAJECTORY_STEPS_MAX = 80;
export const DISPLAY_BITS_MAX = 256;
export const WORD_MAX = 8;
export const CYCLE_WORD_MAX = 16;
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
    label: "16",
    value: 16n,
    note: "Even tower: nested square roots 16 → 4 → 2 → 1. The even branch only.",
  },
  {
    label: "37 peak",
    value: 37n,
    note: "Paper A’s note peak: a small start that climbs high, then falls. One walk, not a theorem.",
  },
  {
    label: "113",
    value: 113n,
    note: "A longer live walk that still fits in the browser walker.",
  },
  {
    label: "256",
    value: 256n,
    note: "Even tower: 256 → 16 → 4 → 2 → 1. Four even letters, then 1.",
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
  {
    label: "65536",
    value: 65536n,
    note: "Even tower: 65536 → 256 → 16 → 4 → 2 → 1. A taller square-root stack.",
  },
  {
    label: "2^32",
    value: 4294967296n,
    note: "Even tower 2^32. Still live: nested square roots the browser can walk.",
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

export const CYCLE_TOUR_PRESETS = [
  {
    id: "o7eeee",
    word: "OOOOOOOEEEE",
    minIndex: 0,
    label: "O⁷EEEE",
    hint: "CycleMin shape, four trailing evens. Named leftover: not a cycle.",
  },
  {
    id: "o6eeeoe",
    word: "OOOOOOEEEOE",
    minIndex: 0,
    label: "O⁶EEEOE",
    hint: "OE seam: isolated last E. Named leftover: not a cycle.",
  },
  {
    id: "offcut",
    word: "EEOOOOOOOEE",
    minIndex: 2,
    label: "Wrong cut",
    hint: "The same leftover, rotated off the minimum. Click the min bead.",
  },
  {
    id: "ooe",
    word: "OOE",
    minIndex: 0,
    label: "OOE",
    hint: "Too few evens. Expanding, not superquadratic. Not a cycle.",
  },
  {
    id: "oeo",
    word: "OEO",
    minIndex: 0,
    label: "OEO",
    hint: "Starts OE, not OO. Too few evens. Not a cycle.",
  },
  {
    id: "three-valleys",
    word: "OOOEOOEOOEE",
    minIndex: 0,
    label: "3 valleys",
    hint: "CycleMin shape with three odd-runs. Not a cycle.",
  },
] as const;

/** Capture strings onto the only known balloon {1}. Not cycles. */
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
