/**
 * Inverse cells. Display fork of
 * src/research/juggler_sequence/floor_cells.py.
 * Even parents of q sit in [q², (q+1)²). An odd image has at most one
 * integer parent (Lemma 3.1).
 */

export function evenCell(q: number): { lo: number; hi: number } {
  if (!Number.isInteger(q) || q < 0) {
    throw new Error("evenCell requires a nonnegative integer");
  }
  return { lo: q * q, hi: (q + 1) * (q + 1) };
}

export function evenPredecessors(q: number, listMax = 40): {
  lo: number;
  hi: number;
  evens: number[];
  evenCount: number;
  truncated: boolean;
} {
  const { lo, hi } = evenCell(q);
  const evens: number[] = [];
  for (let n = lo; n < hi; n += 1) {
    if (n % 2 === 0 && n >= 1) evens.push(n);
  }
  return {
    lo,
    hi,
    evenCount: evens.length,
    truncated: evens.length > listMax,
    evens: evens.slice(0, listMax),
  };
}

export function oddCellIntegers(m: number): number[] {
  if (!Number.isInteger(m) || m < 0) {
    throw new Error("oddCellIntegers requires a nonnegative integer");
  }
  const lo2 = m * m;
  const hi2 = (m + 1) * (m + 1);
  let lo = 0;
  let hi = m + 3;
  while (lo < hi) {
    const mid = Math.floor((lo + hi) / 2);
    if (mid * mid * mid < lo2) lo = mid + 1;
    else hi = mid;
  }
  const nMin = lo;
  lo = 0;
  hi = 2 * m + 5;
  while (lo < hi) {
    const mid = Math.floor((lo + hi) / 2);
    if (mid * mid * mid < hi2) lo = mid + 1;
    else hi = mid;
  }
  const nMax = lo - 1;
  if (nMax < nMin) return [];
  const out: number[] = [];
  for (let n = nMin; n <= nMax; n += 1) out.push(n);
  return out;
}
