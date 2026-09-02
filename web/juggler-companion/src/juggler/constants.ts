/**
 * Paper A printed constants. Display fork of
 * src/visualization/juggler_finite_dynamics.py — not a second theorem.
 */

export const ORBIT_STEPS_MAX = 80;
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

export const NOTE_ORBIT_3 = [3n, 5n, 11n, 36n, 6n, 2n, 1n] as const;
export const NOTE_PEAK_37 = 24_906_114_455_136n;

export const N_PRESETS = [
  { label: "3 — note orbit", value: 3n },
  { label: "37 — note peak", value: 37n },
  { label: "1999 — four-block", value: 1999n },
] as const;

/** Short starts for the map tour: 37 plus the note-orbit odds and 1999. */
export const MAP_STARTS = [
  { label: "37 peak", value: 37n },
  { label: "3", value: 3n },
  { label: "5", value: 5n },
  { label: "11", value: 11n },
  { label: "1999", value: 1999n },
] as const;

export const WORD_PRESETS = ["OOE", "OOOEE", "OOOEOE", "OOOOEE"] as const;
export const CYCLE_PRESETS = ["OEO", "OOE", "OOOEOE", "OOOOEE"] as const;
export const RECORD_LENGTHS = [1, 3, 11, 19, 84, 569, 1054, 25781, 50508] as const;
