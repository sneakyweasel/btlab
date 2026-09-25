import progress from "../data/beatty_progress.json";

export type BeattyClaim = {
  id: string;
  tag: string;
  statement: string;
  lean: string | null;
  source: string;
  firstRecorded: string | null;
  theme: BeattyTheme;
};

export const BEATTY_THEMES = [
  { key: "counting", label: "Counting and survivors", hint: "Exact word counts, renewal series, binomial bounds." },
  { key: "profile", label: "Profile and cluster set", hint: "The jump profile F, its phases and the accumulation set." },
  { key: "laws", label: "Limit laws", hint: "Empirical and weak limits of the normalized counts." },
  { key: "geometry", label: "Geometry and dimension", hint: "Gaps, Minkowski content, Hausdorff and packing dimension." },
  { key: "gamma", label: "Gamma normalization", hint: "The absolutely continuous second law and its density." },
] as const;

export type BeattyTheme = (typeof BEATTY_THEMES)[number]["key"];

// Checked in order: the first matching theme wins. Gamma rows are a separate law.
const THEME_RULES: readonly [BeattyTheme, RegExp][] = [
  ["gamma", /gamma/],
  ["geometry", /hausdorff|minkowski|dim|cantor|packing|content|gap|tube|frostman|liouville|isolated|diophantine|star|cf-expansion|jump-cover|measure-dichotomy|three-halves|jump-range/],
  ["laws", /law|weak|empirical|equidistribution|occupation/],
  ["counting", /survivor|tilt/],
  ["profile", /profile|cluster|accumulation|envelope|jump|series|phase|rotation|mass|continuity|rational-limits|asymptotic/],
  ["counting", /survivor|counting|renewal|crossing|first-passage|binomial|tilt|arb|specialization/],
];

export function beattyTheme(id: string): BeattyTheme {
  const rule = THEME_RULES.find(([, pattern]) => pattern.test(id));
  if (!rule) throw new Error(`Unclassified Beatty claim ${id}`);
  return rule[0];
}

export const BEATTY_PROGRESS = {
  source: progress.source,
  sourceSha256: progress.sourceSha256,
  dating: progress.dating,
};

export const BEATTY_CLAIMS: readonly BeattyClaim[] = progress.claims.map(claim => ({ ...claim, theme: beattyTheme(claim.id) }));

export const BEATTY_TAGS = ["EXACT — LEAN VERIFIED", "EXACT — HUMAN PROOF", "COMPUTATIONALLY VERIFIED"] as const;

export function tagCounts(claims: readonly BeattyClaim[]): Record<string, number> {
  const counts: Record<string, number> = {};
  for (const claim of claims) counts[claim.tag] = (counts[claim.tag] ?? 0) + 1;
  return counts;
}

export function leanModules(claims: readonly BeattyClaim[]): string[] {
  return [...new Set(claims.flatMap(claim => claim.lean ? [claim.lean] : []))].sort();
}

export type TimelinePoint = { time: number; total: number; lean: number; id: string };

/** Cumulative counts at each first-recorded timestamp, in commit order. */
export function beattyTimeline(claims: readonly BeattyClaim[]): TimelinePoint[] {
  const dated = claims.filter(claim => claim.firstRecorded)
    .map(claim => ({ claim, time: Date.parse(claim.firstRecorded!) }))
    .sort((a, b) => a.time - b.time || a.claim.id.localeCompare(b.claim.id));
  let total = 0, lean = 0;
  return dated.map(({ claim, time }) => {
    total += 1;
    if (claim.tag === "EXACT — LEAN VERIFIED") lean += 1;
    return { time, total, lean, id: claim.id };
  });
}

/** Human-readable name from a claim ID: "J-beatty-slope-gamma-lp" → "slope gamma lp". */
export function claimTitle(id: string): string {
  return id.replace(/^J-beatty-/, "").replace(/-/g, " ");
}
