/**
 * Dimension atlas for the Beatty first-passage cluster sets K_alpha.
 *
 * The game functions port src/research/juggler_sequence/beatty_dimension_game.py.
 * They are floating-point exponent calculations with constants dropped: they
 * locate where the cover recursion and the window measure meet and prove nothing.
 */

export type Element = { kind: "g" | "d"; t: number };
export type Pattern = readonly Element[];

export type Evidence = "LEAN" | "HUMAN" | "COMPUTATIONAL" | "OBSERVATION" | "CONJECTURE";

export const EVIDENCE_LABEL: Record<Evidence, string> = {
  LEAN: "EXACT — LEAN VERIFIED",
  HUMAN: "EXACT — HUMAN PROOF",
  COMPUTATIONAL: "COMPUTATIONALLY VERIFIED",
  OBSERVATION: "OBSERVATION",
  CONJECTURE: "CONJECTURE",
};

/** s*(nu) = 2(sqrt(1+3nu)-1)/(3nu), the upper bound of J-beatty-slope-star-upper. */
export function starDim(nu: number): number {
  return nu === 1 ? 2 / 3 : 2 * (Math.sqrt(1 + 3 * nu) - 1) / (3 * nu);
}

/** 2/(2+nu), the Hausdorff dimension of the limit law (J-beatty-slope-law-dimension). */
export function lawDim(nu: number): number {
  return 2 / (2 + nu);
}

/** Closed form for one jump nu followed by a dense stretch rho: dimension and window exponent. */
export function twoScaleDim(nu: number, rho: number): { s: number; gamma: number } {
  if (rho <= 1 + 3 / nu) return { s: 2 / (2 + nu), gamma: 1 };
  const r = rho * nu;
  const root = Math.sqrt((rho - 1) * (3 * r + rho - 4));
  return { s: 2 * (root - (rho - 1)) / (3 * (r - 1)), gamma: nu + 2 - (2 + root) / rho };
}

/** Whether the cover recursion certifies H^s = 0 (the periodic solution has w > 0). */
export function upperPositive(pattern: Pattern, s: number, periods = 3000): boolean {
  const floor = 1.5 * s - 1;
  let w = floor;
  for (let p = 0; p < periods; p++) {
    for (let i = pattern.length - 1; i >= 0; i--) {
      const { kind, t } = pattern[i];
      if (kind === "d") {
        w = Math.max(floor, t * w);
        continue;
      }
      const y = Math.min(Math.max((t * w + t - s + 1) / (1 + s / 2), 1), t);
      w = Math.max(floor, t * w, Math.min(s + s * y / 2 - 1, t * w + t - y));
      if (w > 1e3) return true;
    }
  }
  return w > 1e-12;
}

/** Upper-bound threshold by bisection on s in [0, 2/3]. */
export function upperDim(pattern: Pattern, periods = 3000, steps = 50): number {
  let lo = 0, hi = 2 / 3 + 1e-12;
  for (let i = 0; i < steps; i++) {
    const mid = (lo + hi) / 2;
    if (upperPositive(pattern, mid, periods)) hi = mid;
    else lo = mid;
  }
  return hi;
}

/** Largest s the window measure with these exponents supports, in the periodic regime. */
export function lowerS(pattern: Pattern, gammas: readonly number[]): number {
  let c = 1, d = 0, j = 0;
  for (const { kind, t } of pattern) {
    const g = kind === "g" ? gammas[j++] : 1;
    c /= t;
    d = (d + t - g) / t;
  }
  let a = d / (1 - c), best = Infinity;
  j = 0;
  for (const { kind, t } of pattern) {
    if (kind === "g") {
      const g = gammas[j++];
      best = Math.min(best, a / (t / 2 + 1.5 - g / 2));
      a = (a + t - g) / t;
    } else {
      const end = (a + t - 1) / t;
      best = Math.min(best, Math.min(a, end) / 1.5);
      a = end;
    }
  }
  return Math.max(best, 0);
}

function mulberry32(seed: number): () => number {
  let state = seed >>> 0;
  return () => {
    state = (state + 0x6d2b79f5) >>> 0;
    let x = state;
    x = Math.imul(x ^ (x >>> 15), x | 1);
    x ^= x + Math.imul(x ^ (x >>> 7), x | 61);
    return ((x ^ (x >>> 14)) >>> 0) / 4294967296;
  };
}

function gauss(random: () => number, sigma: number): number {
  const u = Math.max(random(), 1e-300), v = random();
  return sigma * Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v);
}

/** Minimise f by the Nelder-Mead simplex method (standard coefficients). */
function nelderMead(f: (x: number[]) => number, x0: number[], step = 1, iters = 6000): [number[], number] {
  const n = x0.length;
  let simplex = [x0.slice(), ...x0.map((_, i) => x0.map((v, j) => v + (i === j ? step : 0)))];
  let values = simplex.map(f);
  for (let it = 0; it < iters; it++) {
    const order = values.map((_, i) => i).sort((a, b) => values[a] - values[b]);
    simplex = order.map(i => simplex[i]);
    values = order.map(i => values[i]);
    if (values[n] - values[0] < 1e-15) {
      let spread = 0;
      for (const point of simplex) for (let j = 0; j < n; j++) spread = Math.max(spread, Math.abs(point[j] - simplex[0][j]));
      if (spread < 1e-12) break;
    }
    const centroid = Array.from({ length: n }, (_, j) => simplex.slice(0, n).reduce((sum, p) => sum + p[j], 0) / n);
    const worst = simplex[n];
    const reflect = centroid.map((c, j) => c + (c - worst[j]));
    const fr = f(reflect);
    if (values[0] <= fr && fr < values[n - 1]) { simplex[n] = reflect; values[n] = fr; continue; }
    if (fr < values[0]) {
      const expand = centroid.map((c, j) => c + 2 * (c - worst[j]));
      const fe = f(expand);
      if (fe < fr) { simplex[n] = expand; values[n] = fe; } else { simplex[n] = reflect; values[n] = fr; }
      continue;
    }
    const contract = centroid.map((c, j) => c + 0.5 * (worst[j] - c));
    const fc = f(contract);
    if (fc < values[n]) { simplex[n] = contract; values[n] = fc; continue; }
    const best = simplex[0];
    simplex = [best, ...simplex.slice(1).map(p => best.map((b, j) => b + 0.5 * (p[j] - b)))];
    values = [values[0], ...simplex.slice(1).map(f)];
  }
  let i = 0;
  for (let k = 1; k <= n; k++) if (values[k] < values[i]) i = k;
  return [simplex[i], values[i]];
}

/** Maximise lowerS over window exponents gamma_i in [1, t_i] (restarted Nelder-Mead). */
export function lowerDim(pattern: Pattern, restarts = 25, seed = 0): { s: number; gammas: number[] } {
  const tops = pattern.filter(e => e.kind === "g").map(e => e.t);
  if (!tops.length) return { s: lowerS(pattern, []), gammas: [] };
  const random = mulberry32(seed + 1);
  const toGammas = (x: number[]) => tops.map((t, i) => 1 + (t - 1) / (1 + Math.exp(-Math.max(Math.min(x[i], 60), -60))));
  const loss = (x: number[]) => -lowerS(pattern, toGammas(x));
  let bestS = lowerS(pattern, tops.map(() => 1)), bestG = tops.map(() => 1);
  for (let r = 0; r < restarts; r++) {
    const x0 = tops.map(() => (r ? gauss(random, 3) : 0));
    let [x] = nelderMead(loss, x0);
    let v: number;
    [x, v] = nelderMead(loss, x, 0.1);
    if (-v > bestS) { bestS = -v; bestG = toGammas(x); }
  }
  return { s: bestS, gammas: bestG };
}

/** Approximation exponent of a periodic pattern in the model: the largest jump. */
export function patternNu(pattern: Pattern): number {
  return Math.max(1, ...pattern.filter(e => e.kind === "g").map(e => e.t));
}

export const GAME_FAMILIES: readonly { name: string; pattern: Pattern }[] = [
  ["regular nu=2", [["g", 2]]],
  ["regular nu=3", [["g", 3]]],
  ["regular nu=5", [["g", 5]]],
  ["two-scale nu=2 rho=5", [["g", 2], ["d", 5]]],
  ["two-scale nu=3 rho=10", [["g", 3], ["d", 10]]],
  ["two-scale nu=2 rho=1e9", [["g", 2], ["d", 1e9]]],
  ["alternating 2,4", [["g", 2], ["g", 4]]],
  ["alternating 1.5,6", [["g", 1.5], ["g", 6]]],
  ["pair then dense", [["g", 3], ["g", 3], ["d", 10]]],
  ["two blocks", [["g", 2], ["d", 3], ["g", 4], ["d", 1.5]]],
  ["jump, small jump, dense", [["g", 4], ["g", 1.3], ["d", 5]]],
  ["three jumps", [["g", 3.288], ["g", 4.063], ["g", 2.453]]],
  ["mixed A", [["d", 2.492], ["g", 4.927], ["d", 9.042], ["g", 2.252]]],
  ["mixed B", [["d", 10.833], ["g", 4.249], ["g", 1.51], ["d", 13.433]]],
  ["mixed C", [["g", 2.241], ["g", 3.654], ["d", 12.468], ["g", 2.018]]],
].map(([name, raw]) => ({
  name: name as string,
  pattern: (raw as [string, number][]).map(([kind, t]) => ({ kind: kind as "g" | "d", t })),
}));

/** Convergent denominators Q_k of [a_0; a_1, ...] as bigints (Q_{-1}=0, Q_0=1). */
export function denominators(quotients: readonly number[]): bigint[] {
  const out: bigint[] = [];
  let previous = 0n, current = 1n;
  out.push(current);
  for (const a of quotients.slice(1)) {
    [previous, current] = [current, BigInt(a) * current + previous];
    out.push(current);
  }
  return out;
}

export function bigLog(value: bigint): number {
  const digits = value.toString();
  if (digits.length < 300) return Math.log(Number(value));
  return Math.log(Number(digits.slice(0, 17))) + (digits.length - 17) * Math.LN10;
}

/** Growth ratios log Q_(k+1) / log Q_k over the certified prefix, from Q_k >= 100 (earlier ratios are noise). */
export function growthRatios(quotients: readonly number[]): { k: number; ratio: number; a: number }[] {
  const q = denominators(quotients);
  const out: { k: number; ratio: number; a: number }[] = [];
  for (let k = 1; k + 1 < q.length; k++) {
    if (q[k] < 100n) continue;
    out.push({ k, ratio: bigLog(q[k + 1]) / bigLog(q[k]), a: quotients[k + 1] });
  }
  return out;
}

export type SlopeStatement = { text: string; evidence: Evidence; claim?: string; source?: string };

export type Slope = {
  key: string;
  name: string;
  tex: string;
  /** Certified partial quotients [a_0; a_1, ...] (Arb, 256 bits) or exact periodic expansions. */
  quotients: readonly number[];
  quotientsSource: string;
  /** Proved range of dim_H K_alpha, for the map. */
  dim: [number, number];
  /** Diophantine class nu when known; null places the slope beside the map. */
  nu: [number, number] | null;
  statements: readonly SlopeStatement[];
};

const repeat = (head: number, value: number, count: number) => [head, ...Array.from({ length: count - 1 }, () => value)];

export const SLOPES: readonly Slope[] = [
  {
    key: "golden",
    name: "Golden ratio",
    tex: String.raw`\varphi=\tfrac{1+\sqrt5}{2}`,
    quotients: repeat(1, 1, 40),
    quotientsSource: "exact periodic expansion [1; 1, 1, …]",
    dim: [2 / 3, 2 / 3],
    nu: [1, 1],
    statements: [
      { text: "Quadratic, hence badly approximable: dim_H K = 2/3 with positive finite two-thirds Hausdorff measure.", evidence: "LEAN", claim: "J-beatty-slope-quadratic-hausdorff" },
      { text: "Positive two-thirds measure holds exactly at badly approximable slopes.", evidence: "LEAN", claim: "J-beatty-slope-critical-measure-dichotomy" },
    ],
  },
  {
    key: "sqrt2",
    name: "Square root of two",
    tex: String.raw`\sqrt2`,
    quotients: repeat(1, 2, 40),
    quotientsSource: "exact periodic expansion [1; 2, 2, …]",
    dim: [2 / 3, 2 / 3],
    nu: [1, 1],
    statements: [
      { text: "Quadratic, hence badly approximable: dim_H K = 2/3 with positive finite two-thirds Hausdorff measure.", evidence: "LEAN", claim: "J-beatty-slope-quadratic-hausdorff" },
    ],
  },
  {
    key: "e",
    name: "Euler's number",
    tex: "e",
    quotients: [2, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8, 1, 1, 10, 1, 1, 12, 1, 1, 14, 1, 1, 16, 1, 1, 18, 1, 1, 20, 1, 1, 22, 1, 1, 24, 1, 1, 26, 1],
    quotientsSource: "40 partial quotients certified by Arb at 256 bits",
    dim: [2 / 3, 2 / 3],
    nu: [1, 1],
    statements: [
      { text: "dim_H K = 2/3 exactly when the irrationality exponent is 2; for e that exponent is classical (cited, not formalized).", evidence: "LEAN", claim: "J-beatty-slope-dim-irrationality-exponent" },
      { text: "The partial quotients are unbounded, so e is not badly approximable and the two-thirds measure vanishes.", evidence: "LEAN", claim: "J-beatty-slope-critical-measure-dichotomy" },
    ],
  },
  {
    key: "log23",
    name: "The logarithmic slope",
    tex: String.raw`\log_2 3`,
    quotients: [1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4, 3, 1, 1, 15, 1, 9, 2, 5, 7, 1, 1, 4, 8, 1, 11, 1, 20, 2, 1, 10, 1, 4, 1],
    quotientsSource: "40 partial quotients certified by Arb at 256 bits",
    dim: [0.16195, 2 / 3],
    nu: null,
    statements: [
      { text: "dim_H K ≤ 2/3 and the packing dimension is 2/3, as for every irrational slope.", evidence: "LEAN", claim: "J-beatty-slope-hausdorff-upper" },
      { text: "Rhin's effective irrationality measure gives H^(2/39.9)(K) > 0.", evidence: "HUMAN", claim: "J-beatty-rhin-hausdorff-lower-bound" },
      { text: "Wu and Wang's measure gives dim_H K ≥ 0.16195… (note §20, written corollary).", evidence: "HUMAN", source: "note §20" },
      { text: "The irrationality exponent of log₂3 is unknown, so its Diophantine class, and dim_H K, remain open.", evidence: "OBSERVATION" },
    ],
  },
  {
    key: "liouville",
    name: "A Liouville slope",
    tex: String.raw`1+\sum_{k\ge1}10^{-k!}`,
    quotients: [],
    quotientsSource: "not shown: a finite prefix of partial quotients would not display the Liouville property",
    dim: [0, 0],
    nu: null,
    statements: [
      { text: "Every Liouville slope has dim_H K = 0, while the packing dimension stays 2/3.", evidence: "LEAN", claim: "J-beatty-slope-liouville-dimension-zero" },
    ],
  },
];

/** Claims the atlas cites, with the tag the ledger must carry (checked by tests). */
export const ATLAS_CLAIMS: Record<string, Evidence> = {
  "J-beatty-slope-packing-dim": "LEAN",
  "J-beatty-slope-law-packing": "LEAN",
  "J-beatty-slope-law-dimension": "LEAN",
  "J-beatty-slope-star-upper": "LEAN",
  "J-beatty-slope-dim-class-lower": "LEAN",
  "J-beatty-slope-regular-exact-dim": "LEAN",
  "J-beatty-slope-isolated-exact": "LEAN",
  "J-beatty-slope-ae-hausdorff-dimension": "LEAN",
  "J-beatty-slope-quadratic-hausdorff": "LEAN",
  "J-beatty-slope-critical-measure-dichotomy": "LEAN",
  "J-beatty-slope-dim-irrationality-exponent": "LEAN",
  "J-beatty-slope-hausdorff-upper": "LEAN",
  "J-beatty-slope-liouville-dimension-zero": "LEAN",
  "J-beatty-slope-minkowski-dimension": "LEAN",
  "J-beatty-certificate-cantor-dimension": "LEAN",
  "J-beatty-rhin-hausdorff-lower-bound": "HUMAN",
};

/**
 * Head of the tube volume at log_2 3 from the first M gaps:
 * vol(K_eps) = 2 eps + sum_r min(w_r, 2 eps) (J-beatty-certificate-cantor-dimension).
 * The omitted gaps add at most min(tail, sum over them of 2 eps), bounded here by the tail mass.
 */
export function tubeVolumeHead(weights: readonly number[], eps: number): number {
  let sum = 2 * eps;
  for (const w of weights) sum += Math.min(w, 2 * eps);
  return sum;
}
