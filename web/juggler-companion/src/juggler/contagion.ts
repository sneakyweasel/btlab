/**
 * Paper C §5.1–5.3. Display fork of
 * src/research/juggler_sequence/fate_contagion.py (RECURSIONS, lambda_root).
 * The three sources are the E-images, OE on E-blocks, and OE on the rest.
 * Official λ** adds later words; this file only roots (5.1) and (5.2).
 * Not a halt theorem.
 */

export type RecursionTerm = {
  c: number;
  e: number;
  source: 1 | 2 | 3;
};

export type RecursionId = "star" | "pair";

export type RecursionSpec = {
  id: RecursionId;
  name: string;
  equation: string;
  printed: number;
  terms: readonly RecursionTerm[];
};

/** (5.1): items 1 and 2. Root λ* = 0.3774. */
export const STAR_RECURSION: RecursionSpec = {
  id: "star",
  name: "λ*",
  equation: "2^{-λ} + (1/3)(3/8)^λ = 1",
  printed: 0.3774,
  terms: [
    { c: 1, e: 1 / 2, source: 1 },
    { c: 1 / 3, e: 3 / 8, source: 2 },
  ],
};

/** (5.2): items 1–3. Root λ_pair = 0.4480. */
export const PAIR_RECURSION: RecursionSpec = {
  id: "pair",
  name: "λ_pair",
  equation: "2^{-λ} + (1/9)(3/8)^λ + (2/9)(3/4)^λ = 1",
  printed: 0.4480,
  terms: [
    { c: 1, e: 1 / 2, source: 1 },
    { c: 1 / 9, e: 3 / 8, source: 2 },
    { c: 2 / 9, e: 3 / 4, source: 3 },
  ],
};

export const RECURSIONS: Record<RecursionId, RecursionSpec> = {
  star: STAR_RECURSION,
  pair: PAIR_RECURSION,
};

/** Paper C Theorem 5.3. Later words, not the three sources. */
export const LAMBDA_STAR_STAR_PRINTED = 0.4926;

export function zetaOf(terms: readonly RecursionTerm[], lam: number): number {
  return terms.reduce((sum, term) => sum + term.c * term.e ** lam, 0) - 1;
}

/** Display fork of fate_contagion.lambda_root. */
export function lambdaRoot(terms: readonly RecursionTerm[]): number {
  const f = (lam: number) => zetaOf(terms, lam);
  let lo = 0;
  let hi = 1;
  if (f(lo) <= 0) return 0;
  for (let i = 0; i < 200; i += 1) {
    const mid = (lo + hi) / 2;
    if (f(mid) > 0) lo = mid;
    else hi = mid;
  }
  return (lo + hi) / 2;
}

export type SourceId = 1 | 2 | 3;

export type SourceBand = {
  id: SourceId;
  label: string;
  hint: string;
  parentLo: number;
  parentHi: number;
  imageLo: number;
  imageHi: number;
  coeffStar: number;
  coeffPair: number;
  scale: number;
};

export type ThreeSourcesView = {
  x: number;
  cuts: {
    x316: number;
    x14: number;
    x38: number;
    sqrt: number;
    x34: number;
    x: number;
  };
  sources: SourceBand[];
};

export function threeSourcesView(x: number): ThreeSourcesView {
  if (!Number.isFinite(x) || x < 2) {
    throw new Error("threeSourcesView requires x ≥ 2");
  }
  const x316 = x ** (3 / 16);
  const x14 = x ** (1 / 4);
  const x38 = x ** (3 / 8);
  const sqrt = Math.sqrt(x);
  const x34 = x ** (3 / 4);
  const sources: SourceBand[] = [
    {
      id: 1,
      label: "E-images",
      hint: "even n in E(m) for m in A ∩ (x^{1/4}, √x]",
      parentLo: x14,
      parentHi: sqrt,
      imageLo: sqrt,
      imageHi: x,
      coeffStar: 1,
      coeffPair: 1,
      scale: 1 / 2,
    },
    {
      id: 2,
      label: "OE on E-blocks",
      hint: "U(m') for m' in A ∩ (x^{3/16}, x^{3/8}]",
      parentLo: x316,
      parentHi: x38,
      imageLo: sqrt,
      imageHi: x,
      coeffStar: 1 / 3,
      coeffPair: 1 / 9,
      scale: 3 / 8,
    },
    {
      id: 3,
      label: "OE on the rest",
      hint: "odd n on Φ(m) for m in A^rest ∩ (x^{3/8}, x^{3/4}]",
      parentLo: x38,
      parentHi: x34,
      imageLo: sqrt,
      imageHi: x,
      coeffStar: 0,
      coeffPair: 2 / 9,
      scale: 3 / 4,
    },
  ];
  return {
    x,
    cuts: { x316, x14, x38, sqrt, x34, x },
    sources,
  };
}

export function coeffOf(source: SourceBand, recursion: RecursionId): number {
  return recursion === "star" ? source.coeffStar : source.coeffPair;
}
