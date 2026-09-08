/**
 * Paper C productions. Display fork of
 * src/research/juggler_sequence/fate_contagion.py.
 * Even block E(m): every even n in [m², (m+1)²) has J(n) = m.
 * OE fiber Φ(m): odd n with m⁴ ≤ n³ < (m+1)⁴; even ⌊n^{3/2}⌋
 * means J(J(n)) = m. Sweep coordinate {n^{3/2}/2} is display-only.
 * Even-block average: U(m') is the even images on the fibers of E(m').
 * Not a halt theorem.
 */

import {
  BLOCK_AVERAGE_C0,
  EVEN_BLOCK_BEAD_MAX,
  FIBER_BEAD_MAX,
  GOOD_ALPHA_HALF,
  GOOD_ALPHA_ZERO,
  PAIRING_SLACK,
  SWEEP_M0,
  SWEEP_SHARE,
} from "./constants";
import { floorPower, icbrt, isqrt } from "./map";

export { icbrt };

function requireNat(m: number, name: string): bigint {
  if (!Number.isInteger(m) || m < 0) {
    throw new Error(`${name} requires a nonnegative integer`);
  }
  return BigInt(m);
}

export function fiberBounds(m: number): { lo: number; hi: number } {
  const mb = requireNat(m, "fiberBounds");
  const m4 = mb * mb * mb * mb;
  const next4 = (mb + 1n) * (mb + 1n) * (mb + 1n) * (mb + 1n);
  let lo = icbrt(m4);
  if (lo * lo * lo < m4) lo += 1n;
  let hi = icbrt(next4);
  if (hi * hi * hi < next4) hi += 1n;
  if (lo % 2n === 0n) lo += 1n;
  return { lo: Number(lo), hi: Number(hi) };
}

export function evenBlock(m: number): number[] {
  const mb = requireNat(m, "evenBlock");
  const lo = mb * mb;
  const hi = (mb + 1n) * (mb + 1n);
  const evens: number[] = [];
  for (let n = lo; n < hi; n += 1n) {
    if (n % 2n === 0n) evens.push(Number(n));
  }
  return evens;
}

export function evenBlockCount(m: number): number {
  const { lo, hi } = evenPreimageInterval(m);
  const first = lo % 2 === 0 ? lo : lo + 1;
  if (first >= hi) return 0;
  return Math.floor((hi - 1 - first) / 2) + 1;
}

export function evenPreimageInterval(m: number): { lo: number; hi: number } {
  const mb = requireNat(m, "evenPreimageInterval");
  return { lo: Number(mb * mb), hi: Number((mb + 1n) * (mb + 1n)) };
}

/** Display-only {n^{3/2}/2} in [0, 1). Parity of the image is exact. */
export function sweepPhase(n: bigint): number {
  if (n < 0n) {
    throw new Error("sweepPhase requires a nonnegative integer");
  }
  const cube = n * n * n;
  const k = isqrt(cube);
  const rem = cube - k * k;
  const kNum = Number(k);
  const remNum = Number(rem);
  const frac = kNum === 0 ? 0 : Math.min(Math.max(remNum / (2 * kNum), 0), 0.999);
  const half = frac / 2;
  return k % 2n === 0n ? half : 0.5 + half;
}

export type FiberPoint = {
  n: number;
  image: number;
  imageEven: boolean;
  sweep: number;
};

export function oeFiber(m: number): FiberPoint[] {
  const { lo, hi } = fiberBounds(m);
  const points: FiberPoint[] = [];
  for (let n = lo; n < hi; n += 2) {
    const nb = BigInt(n);
    const image = isqrt(nb * nb * nb);
    points.push({
      n,
      image: Number(image),
      imageEven: image % 2n === 0n,
      sweep: sweepPhase(nb),
    });
  }
  return points;
}

export function fiberStats(m: number): {
  m: number;
  H: number;
  G: number;
  proportion: number | null;
} {
  const points = oeFiber(m);
  const H = points.length;
  const G = points.filter((point) => point.imageEven).length;
  return { m, H, G, proportion: H === 0 ? null : G / H };
}

function mod1(value: number): number {
  return ((value % 1) + 1) % 1;
}

/** Distance on R/Z to the nearest image of c. */
export function circleDistance(x: number, c: number): number {
  return Math.abs(mod1(x - c + 0.5) - 0.5);
}

/**
 * First odd-to-odd step of {n^{3/2}/2} on Φ(m).
 * Display fork of fate_contagion.fiber_stats; ≈ {3/2 m^{2/3}}.
 */
export function fiberStepAlpha(m: number): number | null {
  const { lo, hi } = fiberBounds(m);
  if (lo + 2 >= hi) return null;
  const delta = (Math.pow(lo + 2, 1.5) - Math.pow(lo, 1.5)) / 2;
  return delta - Math.floor(delta);
}

export type SweepVerdict =
  | "empty"
  | "good"
  | "thin-zero"
  | "thin-half"
  | "below-scale";

export type SweepLemmaView = {
  m: number;
  H: number;
  G: number;
  scarcer: number;
  proportion: number | null;
  alpha: number | null;
  reduced: number | null;
  distZero: number | null;
  distHalf: number | null;
  needZero: number;
  needHalf: number;
  nearZero: boolean;
  nearHalf: boolean;
  atLemmaScale: boolean;
  good: boolean;
  verdict: SweepVerdict;
  sweepFloor: number;
  pairingFloor: number;
  meetsSweep: boolean | null;
  meetsPairing: boolean | null;
};

export function sweepLemmaView(m: number): SweepLemmaView {
  const { H, G, proportion } = fiberStats(m);
  const scale = m <= 0 ? Number.POSITIVE_INFINITY : m ** (-1 / 3);
  const needZero = GOOD_ALPHA_ZERO * scale;
  const needHalf = GOOD_ALPHA_HALF * scale;
  const alpha = fiberStepAlpha(m);
  const distZero = alpha === null ? null : circleDistance(alpha, 0);
  const distHalf = alpha === null ? null : circleDistance(alpha, 0.5);
  const nearZero = distZero !== null && distZero < needZero;
  const nearHalf = distHalf !== null && distHalf < needHalf;
  const atLemmaScale = m >= SWEEP_M0;
  const scarcer = Math.min(G, H - G);
  const sweepFloor = H * SWEEP_SHARE;
  const pairingFloor = H / 3 - PAIRING_SLACK;
  const good = atLemmaScale && alpha !== null && H > 0 && !nearZero && !nearHalf;
  let verdict: SweepVerdict;
  if (H === 0 || alpha === null) {
    verdict = "empty";
  } else if (nearZero) {
    verdict = "thin-zero";
  } else if (nearHalf) {
    verdict = "thin-half";
  } else if (!atLemmaScale) {
    verdict = "below-scale";
  } else {
    verdict = "good";
  }
  return {
    m,
    H,
    G,
    scarcer,
    proportion,
    alpha,
    reduced: distZero,
    distZero,
    distHalf,
    needZero,
    needHalf,
    nearZero,
    nearHalf,
    atLemmaScale,
    good,
    verdict,
    sweepFloor,
    pairingFloor,
    meetsSweep: H === 0 ? null : scarcer + 1e-12 >= sweepFloor,
    meetsPairing: H === 0 ? null : scarcer + 1e-12 >= pairingFloor,
  };
}

export type EvenBlockView = {
  m: number;
  lo: number;
  hi: number;
  count: number;
  evens: number[];
  listed: boolean;
  harmonicLo: number;
  harmonicHi: number;
};

/** Even in E(m) nearest the strip midline (the seed’s vertical). */
export function centerEvenInBlock(view: EvenBlockView, pad = 5): number {
  const evenLo = Math.max(0, view.lo - pad);
  const evenHi = view.hi + pad;
  const atLine = (evenLo + evenHi) / 2;
  if (view.evens.length > 0) {
    return view.evens.reduce((best, n) =>
      Math.abs(n - atLine) < Math.abs(best - atLine) ? n : best,
    );
  }
  const first = view.lo % 2 === 0 ? view.lo : view.lo + 1;
  const last = view.hi % 2 === 0 ? view.hi - 2 : view.hi - 1;
  if (view.count <= 0 || first >= view.hi) return first;
  let n = 2 * Math.round(atLine / 2);
  if (n < first) return first;
  if (n > last) return last;
  return n;
}

export function randomEvenInBlock(view: EvenBlockView): number {
  return centerEvenInBlock(view);
}

export function evenBlockView(m: number): EvenBlockView {
  const { lo, hi } = evenPreimageInterval(m);
  const count = evenBlockCount(m);
  const listed = count <= EVEN_BLOCK_BEAD_MAX;
  return {
    m,
    lo,
    hi,
    count,
    evens: listed ? evenBlock(m) : [],
    listed,
    harmonicLo: m === 0 ? 0 : (1 / m) * (1 - 2 / m),
    harmonicHi: m === 0 ? 0 : (m + 1) / (m * m),
  };
}

export type FiberView = {
  m: number;
  lo: number;
  hi: number;
  points: FiberPoint[];
  H: number;
  G: number;
  proportion: number | null;
  listed: boolean;
};

export function fiberView(m: number): FiberView {
  const { lo, hi } = fiberBounds(m);
  const points = oeFiber(m);
  const H = points.length;
  const G = points.filter((point) => point.imageEven).length;
  return {
    m,
    lo,
    hi,
    points: H <= FIBER_BEAD_MAX ? points : points.slice(0, FIBER_BEAD_MAX),
    H,
    G,
    proportion: H === 0 ? null : G / H,
    listed: H <= FIBER_BEAD_MAX,
  };
}

/** A sea member of Φ(m), or any fiber bead if the production is empty. */
export function randomOePath(view: FiberView): number | null {
  const sea = view.points.filter((point) => point.imageEven);
  const pool = sea.length > 0 ? sea : view.points;
  if (pool.length === 0) return null;
  return pool[Math.floor(Math.random() * pool.length)].n;
}

export function oeMembersMapToSeed(m: number): boolean {
  return oeFiber(m)
    .filter((point) => point.imageEven)
    .every((point) => floorPower(floorPower(BigInt(point.n))) === BigInt(m));
}

export function evenMembersMapToSeed(m: number): boolean {
  return evenBlock(m).every((n) => floorPower(BigInt(n)) === BigInt(m));
}

export type BlockFiberShare = {
  m: number;
  H: number;
  G: number;
  proportion: number | null;
};

export type BlockAverageView = {
  mPrime: number;
  lo: number;
  hi: number;
  fibers: BlockFiberShare[];
  evenM: number;
  H: number;
  evenH: number;
  U: number;
  share: number | null;
  meanEven: number | null;
  errorTerm: number;
  quarter: number;
  bound: number;
  meetsBound: boolean | null;
  boundPositive: boolean;
};

/** n-range of the fibers with m in [m'², (m'+1)²). Display I(m'). */
export function blockInterval(mPrime: number): { lo: number; hi: number } {
  const { lo } = fiberBounds(mPrime * mPrime);
  const { hi } = fiberBounds((mPrime + 1) * (mPrime + 1) - 1);
  return { lo, hi };
}

/**
 * Proposition 4.4 on E(m'): U is the even images on even-m fibers.
 * Display fork of fate_contagion.block_stats. Not the van der Corput proof.
 */
export function blockAverageView(mPrime: number): BlockAverageView {
  requireNat(mPrime, "blockAverageView");
  if (mPrime < 1) {
    throw new Error("blockAverageView requires a positive integer");
  }
  const mLo = mPrime * mPrime;
  const mHi = (mPrime + 1) * (mPrime + 1);
  const fibers: BlockFiberShare[] = [];
  let H = 0;
  let U = 0;
  let evenH = 0;
  for (let m = mLo; m < mHi; m += 1) {
    const stats = fiberStats(m);
    H += stats.H;
    if (m % 2 === 0) {
      fibers.push({
        m,
        H: stats.H,
        G: stats.G,
        proportion: stats.proportion,
      });
      U += stats.G;
      evenH += stats.H;
    }
  }
  const { lo, hi } = blockInterval(mPrime);
  const errorTerm =
    BLOCK_AVERAGE_C0 * mPrime ** (11 / 9) * Math.log(mPrime + 1);
  const quarter = H / 4;
  return {
    mPrime,
    lo,
    hi,
    fibers,
    evenM: fibers.length,
    H,
    evenH,
    U,
    share: H === 0 ? null : U / H,
    meanEven: evenH === 0 ? null : U / evenH,
    errorTerm,
    quarter,
    bound: quarter - errorTerm,
    meetsBound: H === 0 ? null : U + 1e-12 >= quarter - errorTerm,
    boundPositive: quarter > errorTerm,
  };
}
