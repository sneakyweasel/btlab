/**
 * Excursion necklace of Paper A §4 and the exact surplus θ(L).
 *
 * Display fork of the necklace geometry in
 * docs/theory/juggler_finite_dynamics_note.md ("The excursion necklace").
 * Walks stay under DISPLAY_BITS_MAX. θ(L) is live only through
 * LIVE_FINANCE_L_MAX; larger lengths and every n_max are finance.json.
 */

import snapshot from "../data/necklace_presets.json";
import { DISPLAY_BITS_MAX, LIVE_FINANCE_L_MAX, LIVE_NECKLACE_BITS } from "./constants";
import { formatInt, log10Of } from "./format";
import { bitLength, floorPower, letterOf, powInt } from "./map";

export type BlockRegime = "contracting" | "expanding" | "critical";

/** μ(a) = 3^a / 2^(a+1): ideal exponent of one block O^a E. */
export type BlockExponent = {
  odds: number;
  num: bigint;
  den: bigint;
  approx: number;
  regime: BlockRegime;
};

export function blockExponent(odds: number): BlockExponent {
  if (odds < 0) throw new Error("blockExponent requires a nonnegative run");
  const num = powInt(3n, odds);
  const den = powInt(2n, odds + 1);
  const regime: BlockRegime = num > den ? "expanding" : num < den ? "contracting" : "critical";
  return { odds, num, den, approx: Number(num) / Number(den), regime };
}

export type Excursion = {
  index: number;
  /** a_i: odd letters before the closing E. */
  odds: number;
  /** v_i: the state where the block starts (odd on a cycle minimum). */
  valley: bigint;
  /** p_i: the even state just before the closing E; null if the walk stopped. */
  peak: bigint | null;
  /** v_{i+1} = ⌊√p_i⌋; null if the walk stopped. */
  landing: bigint | null;
  /** v_i … p_i (odds + 1 states when complete). */
  states: bigint[];
  mu: BlockExponent;
  complete: boolean;
};

export type NecklaceView = {
  n: bigint;
  word: string;
  /** Parities actually followed, one letter per completed step. */
  realized: string;
  states: bigint[];
  follows: boolean;
  failIndex: number | null;
  bitCapped: boolean;
  excursions: Excursion[];
  nSquared: bigint;
  nPlusOneSquared: bigint;
  firstPeak: bigint | null;
  /** p_0 ≥ (n+1)²  — Lemma 3.4(i), the forced lift. */
  firstPeakOvershoots: boolean | null;
  lastPeak: bigint | null;
  /** n²+1 ≤ p_{e−1} < (n+1)²  — the entry one-step preimage. */
  lastPeakLands: boolean | null;
  /** J^{|word|}(n), or null if the walk stopped early. */
  image: bigint | null;
  returns: boolean;
  /** First step index whose state is below n, or null if the walk stays ≥ n. */
  belowMinimumIndex: number | null;
};

/**
 * Read a finished walk as a necklace of excursions O^{a_i}E.
 * No Juggler step is computed here.
 */
export function necklaceFromStates(
  n: bigint,
  word: string,
  states: readonly bigint[],
  bitCapped = false,
): NecklaceView {
  if (n < 1n) throw new Error("necklaceFromStates requires a positive start");
  if (states.length === 0 || states[0] !== n) {
    throw new Error("necklaceFromStates requires states to start at n");
  }
  const realized = states
    .slice(0, -1)
    .map((state) => letterOf(state))
    .join("");

  let failIndex: number | null = null;
  for (let index = 0; index < word.length; index += 1) {
    if (index >= realized.length) {
      failIndex = index;
      break;
    }
    if (realized[index] !== word[index]) {
      failIndex = index;
      break;
    }
  }
  const follows = failIndex === null && !bitCapped;

  const excursions: Excursion[] = [];
  let blockStart = 0;
  for (let index = 0; index < realized.length; index += 1) {
    if (realized[index] !== "E") continue;
    const odds = index - blockStart;
    excursions.push({
      index: excursions.length,
      odds,
      valley: states[blockStart],
      peak: states[index],
      landing: states[index + 1] ?? null,
      states: states.slice(blockStart, index + 1),
      mu: blockExponent(odds),
      complete: true,
    });
    blockStart = index + 1;
  }
  if (blockStart < realized.length) {
    const odds = realized.length - blockStart;
    excursions.push({
      index: excursions.length,
      odds,
      valley: states[blockStart],
      peak: null,
      landing: null,
      states: states.slice(blockStart),
      mu: blockExponent(odds),
      complete: false,
    });
  }

  const nSquared = n * n;
  const nPlusOneSquared = (n + 1n) * (n + 1n);
  const complete = excursions.filter((block) => block.complete);
  const firstPeak = complete[0]?.peak ?? null;
  const lastPeak = complete.at(-1)?.peak ?? null;
  const image = states.length === word.length + 1 ? states[word.length] : null;

  let belowMinimumIndex: number | null = null;
  for (let index = 1; index < states.length; index += 1) {
    if (states[index] < n) {
      belowMinimumIndex = index;
      break;
    }
  }

  return {
    n,
    word,
    realized,
    states: [...states],
    follows,
    failIndex,
    bitCapped,
    excursions,
    nSquared,
    nPlusOneSquared,
    firstPeak,
    firstPeakOvershoots: firstPeak === null ? null : firstPeak >= nPlusOneSquared,
    lastPeak,
    lastPeakLands:
      lastPeak === null ? null : lastPeak >= nSquared + 1n && lastPeak < nPlusOneSquared,
    image,
    returns: image !== null && image === n,
    belowMinimumIndex,
  };
}

/**
 * Walk n for |word| realized steps. Live only for small starts;
 * Movement-1 presets use resolveNecklace.
 */
export function necklaceView(
  n: bigint,
  word: string,
  bitCap = DISPLAY_BITS_MAX,
): NecklaceView {
  if (n < 1n) throw new Error("necklaceView requires a positive start");
  const states: bigint[] = [n];
  let current = n;
  let bitCapped = false;
  for (let step = 0; step < word.length; step += 1) {
    if (bitLength(current) > bitCap) {
      bitCapped = true;
      break;
    }
    current = floorPower(current);
    states.push(current);
  }
  return necklaceFromStates(n, word, states, bitCapped);
}

const shippedByKey = new Map(
  snapshot.presets.map((row) => [`${row.n}:${row.word}`, row] as const),
);

export function shippedNecklaceView(n: bigint, word: string): NecklaceView | null {
  const row = shippedByKey.get(`${n.toString()}:${word}`);
  if (!row) return null;
  return necklaceFromStates(
    n,
    word,
    row.states.map((text) => BigInt(text)),
  );
}

export type NecklaceSource = "live" | "shipped";

export type ResolvedNecklace = NecklaceView & { source: NecklaceSource };

/** JSON-safe picture of a necklace. No bigint — React 19 cannot serialize those. */
export type NecklaceFigure = {
  word: string;
  realized: string;
  follows: boolean;
  failIndex: number | null;
  bitCapped: boolean;
  returns: boolean;
  belowMinimumIndex: number | null;
  firstPeakOvershoots: boolean | null;
  lastPeakLands: boolean | null;
  firstPeakLabel: string | null;
  lastPeakLabel: string | null;
  imageLabel: string | null;
  bandLoLabel: string;
  bandHiLabel: string;
  logs: number[];
  labels: string[];
  odd: boolean[];
  below: boolean[];
  logN: number;
  logSq: number;
  logSq1: number;
  firstPeakStep: number | null;
  lastPeakStep: number | null;
  closed: boolean;
  tiles: Array<{
    index: number;
    odds: number;
    complete: boolean;
    last: boolean;
    regime: BlockRegime;
    mu: string;
    valley: string;
    peak: string | null;
  }>;
};

export function necklaceFigure(view: NecklaceView): NecklaceFigure {
  const complete = view.excursions.filter((block) => block.complete);
  const firstPeakStep = complete[0] ? complete[0].states.length - 1 : null;
  const lastPeakStep =
    complete.length > 0
      ? view.excursions.slice(0, complete.length).reduce((sum, block) => sum + block.states.length, 0) - 1
      : null;
  return {
    word: view.word,
    realized: view.realized,
    follows: view.follows,
    failIndex: view.failIndex,
    bitCapped: view.bitCapped,
    returns: view.returns,
    belowMinimumIndex: view.belowMinimumIndex,
    firstPeakOvershoots: view.firstPeakOvershoots,
    lastPeakLands: view.lastPeakLands,
    firstPeakLabel: view.firstPeak === null ? null : formatInt(view.firstPeak),
    lastPeakLabel: view.lastPeak === null ? null : formatInt(view.lastPeak),
    imageLabel: view.image === null ? null : formatInt(view.image),
    bandLoLabel: formatInt(view.nSquared + 1n),
    bandHiLabel: formatInt(view.nPlusOneSquared),
    logs: view.states.map(log10Of),
    labels: view.states.map(formatInt),
    odd: view.states.map((state) => state % 2n === 1n),
    below: view.states.map((state) => state < view.n),
    logN: log10Of(view.n),
    logSq: log10Of(view.nSquared),
    logSq1: log10Of(view.nPlusOneSquared),
    firstPeakStep,
    lastPeakStep,
    closed: view.states.length === view.word.length + 1,
    tiles: view.excursions.map((block) => ({
      index: block.index,
      odds: block.odds,
      complete: block.complete,
      last: block.index === view.excursions.length - 1,
      regime: block.mu.regime,
      mu: `${block.mu.num.toString()}/${block.mu.den.toString()}`,
      valley: formatInt(block.valley),
      peak: block.peak === null ? null : formatInt(block.peak),
    })),
  };
}

/** Presets are shipped. Other starts walk only under LIVE_NECKLACE_BITS. */
export function resolveNecklace(n: bigint, word: string): ResolvedNecklace | null {
  const shipped = shippedNecklaceView(n, word);
  if (shipped) return { ...shipped, source: "shipped" };
  if (bitLength(n) > LIVE_NECKLACE_BITS) return null;
  return { ...necklaceView(n, word, LIVE_NECKLACE_BITS), source: "live" };
}

/**
 * Exact o_min(L) = min{ o : 3^o > 2^L }. Live only through
 * LIVE_FINANCE_L_MAX; larger lengths use shippedLedger.
 */
export function oMinExact(length: number): number {
  if (!Number.isInteger(length) || length < 1) {
    throw new Error("oMinExact requires a positive integer length");
  }
  if (length > LIVE_FINANCE_L_MAX) {
    throw new Error(`oMinExact is live only through L=${LIVE_FINANCE_L_MAX}`);
  }
  const pow2 = 1n << BigInt(length);
  let o = Math.max(1, Math.floor((length * Math.LN2) / Math.log(3)));
  let pow3 = powInt(3n, o);
  while (pow3 <= pow2) {
    pow3 *= 3n;
    o += 1;
  }
  while (o > 1 && pow3 / 3n > pow2) {
    pow3 /= 3n;
    o -= 1;
  }
  return o;
}

export type ExactTheta = {
  length: number;
  o: number;
  /** 3^o − 2^L, exact. */
  num: bigint;
  /** 3^o, exact. */
  den: bigint;
  /** θ = num / den to `digits` decimal places, exact rounding down. */
  decimal: string;
  approx: number;
};

/**
 * θ(L) = 1 − 2^L / 3^{o_min(L)}. Live only through LIVE_FINANCE_L_MAX.
 */
export function thetaExact(length: number, digits = 12): ExactTheta {
  const o = oMinExact(length);
  const den = powInt(3n, o);
  const num = den - (1n << BigInt(length));
  const scale = 10n ** BigInt(digits);
  const scaled = (num * scale) / den;
  const text = scaled.toString().padStart(digits + 1, "0");
  const decimal = `${text.slice(0, -digits)}.${text.slice(-digits)}`;
  const approx = Number((num * 10n ** 18n) / den) / 1e18;
  return { length, o, num, den, decimal, approx };
}

/**
 * Theorem 4.4 with constant 1, solved for the budget side:
 * the cycle minimum must satisfy n log n ≤ L / θ. Returns L / (n ln n).
 * A picture of the inequality, not the certified table.
 */
export function financeBudgetConstantOne(length: number, n: number): number {
  if (n <= 1) return Number.POSITIVE_INFINITY;
  return length / (n * Math.log(n));
}

/** Largest real n with n ln n ≤ L / θ (constant-1 Theorem 4.4 crossing). */
export function constantOneCrossing(length: number, theta: number): number {
  if (theta <= 0) return Number.POSITIVE_INFINITY;
  const target = length / theta;
  let lo = 2;
  let hi = 2;
  while (hi * Math.log(hi) < target) hi *= 2;
  for (let iter = 0; iter < 200; iter += 1) {
    const mid = (lo + hi) / 2;
    if (mid * Math.log(mid) < target) lo = mid;
    else hi = mid;
  }
  return lo;
}
