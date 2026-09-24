import snapshot from "../data/beatty_profile.json";

export type BeattyRow = { order: number; phase: number; weight: number; left: number; ratio: number };
export type BeattySelection = { kind: "jump"; order: number } | { kind: "phase"; phase: number };
export type BeattySamples = "late" | "early" | "all";
export type BeattyLayers = { profile: boolean; band: boolean; samples: boolean; gaps: boolean };
export const BEATTY = snapshot;
export const BEATTY_ROWS: readonly BeattyRow[] = snapshot.rows.map(
  ([order, phase, weight, left, ratio]) => ({ order, phase, weight, left, ratio }),
);
const byOrder = new Map(BEATTY_ROWS.map(row => [row.order, row]));
// Larger than both the certified coordinate width and binary display rounding.
const DISPLAY_EPSILON = 1e-12;

export function beattyRow(order: number): BeattyRow {
  const row = byOrder.get(order);
  if (!row) throw new RangeError(`Choose an integer from 1 to ${BEATTY.orders}`);
  return row;
}

/** Strict atom convention: the jump at t is excluded from F_M(t). */
export function beattyLevel(phase: number): number {
  if (!Number.isFinite(phase) || phase < 0 || phase > 1) throw new RangeError("Phase must lie in [0, 1]");
  let low = 0, high = BEATTY_ROWS.length;
  while (low < high) {
    const middle = Math.floor((low + high) / 2);
    if (BEATTY_ROWS[middle].phase < phase) low = middle + 1;
    else high = middle;
  }
  if (low < BEATTY_ROWS.length) return BEATTY_ROWS[low].left;
  const last = BEATTY_ROWS[BEATTY_ROWS.length - 1];
  return last.left + last.weight;
}

export function beattyPhase(selection: BeattySelection): number {
  return selection.kind === "jump" ? beattyRow(selection.order).phase : selection.phase;
}

export function beattySamples(range: BeattySamples): readonly BeattyRow[] {
  return BEATTY_ROWS.filter(row => range === "all" || (range === "early" ? row.order <= 1000 : row.order > BEATTY.orders - 1000));
}

/** Display enclosure padded outward beyond the certified coordinate error. */
export function beattyBounds(phase: number): [number, number] {
  const left = beattyLevel(phase);
  const lower = phase === 0 ? 1 : Math.floor((left - 1e-12) * 1e6) / 1e6;
  const upper = phase === 0 ? 1 : Math.ceil((Math.min(BEATTY.envelope, left + BEATTY.tailUpper) + 1e-12) * 1e6) / 1e6;
  return [lower, upper];
}

/** R^+ is an exact-count ratio; its shipped coordinate is rounded. */
export function beattyResidualBounds(order: number): [number, number] {
  const row = beattyRow(order);
  const [lower, upper] = beattyBounds(row.phase);
  return [
    Math.floor((row.ratio - upper - DISPLAY_EPSILON) * 1e6) / 1e6,
    Math.ceil((row.ratio - lower + DISPLAY_EPSILON) * 1e6) / 1e6,
  ];
}

export type BeattyCDFPoint = { value: number; cumulative: number };

// U is uniform in phase. The mass of a plateau is its phase-interval length,
// not 1 / number of jumps. Consecutive masses telescope to the next phase.
export const BEATTY_PROFILE_CDF: readonly BeattyCDFPoint[] = [
  ...BEATTY_ROWS.map(row => ({ value: row.left, cumulative: row.phase })),
  { value: beattyLevel(1), cumulative: 1 },
];

/** Right-continuous P(X <= y), including all tied observations at y. */
export function beattyCDFAt(points: readonly BeattyCDFPoint[], value: number): number {
  let low = 0, high = points.length;
  while (low < high) {
    const middle = Math.floor((low + high) / 2);
    if (points[middle].value <= value) low = middle + 1;
    else high = middle;
  }
  return low ? points[low - 1].cumulative : 0;
}

export function beattyEmpiricalCDF(range: BeattySamples): BeattyCDFPoint[] {
  const values = beattySamples(range).map(row => row.ratio).sort((a, b) => a - b);
  const points: BeattyCDFPoint[] = [];
  values.forEach((value, index) => {
    const cumulative = (index + 1) / values.length;
    if (points.length && points[points.length - 1].value === value) points[points.length - 1].cumulative = cumulative;
    else points.push({ value, cumulative });
  });
  return points;
}

const probability = (value: number) => Math.max(0, Math.min(1, value));

/** F_M <= F <= F_M + T gives H_M(y - T) <= P(F(U) <= y) <= H_M(y).
 * The small horizontal and vertical pads cover rounded shipped coordinates.
 * These are display transforms of the existing tail certificate, not a new audit.
 */
export const BEATTY_LIMIT_CDF = {
  lower: BEATTY_PROFILE_CDF.map(point => ({ value: point.value + BEATTY.tailUpper + DISPLAY_EPSILON, cumulative: probability(point.cumulative - DISPLAY_EPSILON) })),
  upper: BEATTY_PROFILE_CDF.map(point => ({ value: point.value - DISPLAY_EPSILON, cumulative: probability(point.cumulative + DISPLAY_EPSILON) })),
};

export function beattyLimitCDFBounds(value: number): [number, number] {
  return [beattyCDFAt(BEATTY_LIMIT_CDF.lower, value), beattyCDFAt(BEATTY_LIMIT_CDF.upper, value)];
}

export function beattySegments(min: number, max: number): [number, number, number][] {
  const segments: [number, number, number][] = [];
  let start = 0;
  for (const row of BEATTY_ROWS) {
    if (row.phase >= min && start <= max) segments.push([Math.max(start, min), Math.min(row.phase, max), row.left]);
    start = row.phase;
    if (start > max) break;
  }
  if (start <= max) segments.push([Math.max(start, min), max, beattyLevel(1)]);
  return segments;
}
