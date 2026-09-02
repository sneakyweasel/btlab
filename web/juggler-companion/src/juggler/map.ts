/**
 * Exact Juggler step. Display fork of
 * src/research/juggler_sequence/power_words.py:floor_power.
 * Even: floor(sqrt n). Odd: floor(n^{3/2}) = isqrt(n^3).
 */

export function bitLength(n: bigint): number {
  const value = n < 0n ? -n : n;
  if (value === 0n) return 0;
  return value.toString(2).length;
}

export function isqrt(n: bigint): bigint {
  if (n < 0n) {
    throw new Error("isqrt requires a nonnegative integer");
  }
  if (n < 2n) return n;
  let x0 = 1n << BigInt(Math.floor((bitLength(n) + 1) / 2));
  let x1 = (x0 + n / x0) >> 1n;
  while (x1 < x0) {
    x0 = x1;
    x1 = (x0 + n / x0) >> 1n;
  }
  return x0;
}

export function floorPower(n: bigint): bigint {
  if (n < 1n) {
    throw new Error("floorPower is defined on positive integers");
  }
  if (n % 2n === 0n) return isqrt(n);
  return isqrt(n * n * n);
}

export function letterOf(n: bigint): "O" | "E" {
  return n % 2n === 1n ? "O" : "E";
}

export function powInt(base: bigint, exp: number): bigint {
  if (exp < 0) throw new Error("powInt requires a nonnegative exponent");
  let result = 1n;
  let b = base;
  let e = exp;
  while (e > 0) {
    if (e & 1) result *= b;
    e >>= 1;
    if (e) b *= b;
  }
  return result;
}
