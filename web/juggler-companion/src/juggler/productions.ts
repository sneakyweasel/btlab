/**
 * Paper C productions. Display fork of
 * src/research/juggler_sequence/fate_contagion.py.
 * Even block E(m): every even n in [m², (m+1)²) has J(n) = m.
 * OE fiber Φ(m): odd n with m⁴ ≤ n³ < (m+1)⁴; even ⌊n^{3/2}⌋
 * means J(J(n)) = m. Sweep coordinate {n^{3/2}/2} is display-only.
 * Not a halt theorem.
 */

import {
  EVEN_BLOCK_BEAD_MAX,
  FIBER_BEAD_MAX,
} from "./constants";
import { floorPower, isqrt } from "./map";

export function icbrt(x: bigint): bigint {
  if (x < 0n) {
    throw new Error("icbrt requires a nonnegative integer");
  }
  if (x <= 1n) return x;
  let lo = 0n;
  let hi = x;
  while (lo < hi) {
    const mid = (lo + hi + 1n) >> 1n;
    if (mid * mid * mid <= x) lo = mid;
    else hi = mid - 1n;
  }
  return lo;
}

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

export function oeMembersMapToSeed(m: number): boolean {
  return oeFiber(m)
    .filter((point) => point.imageEven)
    .every((point) => floorPower(floorPower(BigInt(point.n))) === BigInt(m));
}

export function evenMembersMapToSeed(m: number): boolean {
  return evenBlock(m).every((n) => floorPower(BigInt(n)) === BigInt(m));
}
