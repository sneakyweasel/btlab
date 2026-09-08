/**
 * Paper C §5.1–5.7. Display fork of
 * src/research/juggler_sequence/fate_contagion.py (RECURSIONS, lambda_root).
 * Three sources are (5.1)–(5.2). The V-ladder is Theorem 5.3; ρ_w is (5.7)
 * and Proposition 5.13. Official λ** is the V6 truncation. Not a halt theorem.
 */

export type RecursionTerm = {
  c: number;
  e: number;
  source?: 1 | 2 | 3;
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

export type LadderId =
  | "star"
  | "pair"
  | "oeoee"
  | "v3"
  | "v4"
  | "v5"
  | "v6"
  | "ideal";

export type LadderRung = {
  id: LadderId;
  name: string;
  added: string;
  python: string;
  printed: number;
  terms: readonly RecursionTerm[];
  official: boolean;
  muted: boolean;
  words: readonly string[];
};

const PAIR_TERMS: readonly RecursionTerm[] = [
  { c: 1, e: 1 / 2 },
  { c: 1 / 9, e: 3 / 8 },
  { c: 2 / 9, e: 3 / 4 },
];

function extendPair(
  extras: readonly RecursionTerm[],
): readonly RecursionTerm[] {
  return [...PAIR_TERMS, ...extras];
}

/** Theorem 5.3 truncations plus the depth-two ideal ceiling. */
export const LADDER_RUNGS: readonly LadderRung[] = [
  {
    id: "star",
    name: "λ*",
    added: "E + OEE",
    python: "block_average_only",
    printed: 0.3774,
    terms: STAR_RECURSION.terms,
    official: false,
    muted: false,
    words: ["E", "OEE"],
  },
  {
    id: "pair",
    name: "λ_pair",
    added: "+ OE rest",
    python: "block_average_plus_third",
    printed: 0.4480,
    terms: PAIR_RECURSION.terms,
    official: false,
    muted: false,
    words: ["OE"],
  },
  {
    id: "oeoee",
    name: "OEOEE",
    added: "+ 1/27 at 9/32",
    python: "block_third_plus_oeoee",
    printed: 0.4801,
    terms: extendPair([{ c: 1 / 27, e: 9 / 32 }]),
    official: false,
    muted: false,
    words: ["OEOEE"],
  },
  {
    id: "v3",
    name: "V3",
    added: "+ 1/81 at 27/128",
    python: "block_third_plus_oeoee_v3",
    printed: 0.4891,
    terms: extendPair([
      { c: 1 / 27, e: 9 / 32 },
      { c: 1 / 81, e: 27 / 128 },
    ]),
    official: false,
    muted: false,
    words: ["OEOEOEE"],
  },
  {
    id: "v4",
    name: "V4",
    added: "+ 1/243 at 81/512",
    python: "block_third_plus_oeoee_v4",
    printed: 0.4916,
    terms: extendPair([
      { c: 1 / 27, e: 9 / 32 },
      { c: 1 / 81, e: 27 / 128 },
      { c: 1 / 243, e: 81 / 512 },
    ]),
    official: false,
    muted: false,
    words: ["OEOEOEOEE"],
  },
  {
    id: "v5",
    name: "V5",
    added: "+ 1/729 at 243/2048",
    python: "block_third_plus_oeoee_v5",
    printed: 0.4924,
    terms: extendPair([
      { c: 1 / 27, e: 9 / 32 },
      { c: 1 / 81, e: 27 / 128 },
      { c: 1 / 243, e: 81 / 512 },
      { c: 1 / 729, e: 243 / 2048 },
    ]),
    official: false,
    muted: false,
    words: ["OEOEOEOEOEE"],
  },
  {
    id: "v6",
    name: "λ**",
    added: "+ 1/2187 at 729/8192",
    python: "block_third_plus_oeoee_v6",
    printed: 0.4926,
    terms: extendPair([
      { c: 1 / 27, e: 9 / 32 },
      { c: 1 / 81, e: 27 / 128 },
      { c: 1 / 243, e: 81 / 512 },
      { c: 1 / 729, e: 243 / 2048 },
      { c: 1 / 2187, e: 729 / 8192 },
    ]),
    official: true,
    muted: false,
    words: ["OEOEOEOEOEOEE"],
  },
  {
    id: "ideal",
    name: "ideal",
    added: "depth-two ceiling",
    python: "depth_two_ideal",
    printed: 0.4927,
    terms: [
      { c: 1, e: 1 / 2 },
      { c: 1 / 3, e: 3 / 4 },
    ],
    official: false,
    muted: true,
    words: [],
  },
];

export const TOUR_LADDER_ID: LadderId = "v6";

export function ladderRung(id: LadderId): LadderRung {
  const rung = LADDER_RUNGS.find((row) => row.id === id);
  if (!rung) throw new Error(`unknown ladder rung ${id}`);
  return rung;
}

export type RhoWord = {
  word: string;
  short: string;
  hint: string;
  appendix: boolean;
};

/** Proposition 5.13 classification. OOEEE/OOEE are the fiber test, not Theorem 5.3. */
export const RHO_WORDS: readonly RhoWord[] = [
  { word: "E", short: "E", hint: "exact, ρ = 1/2", appendix: false },
  { word: "OEE", short: "OEE", hint: "block average, ideal", appendix: false },
  { word: "OEOEE", short: "OEOEE", hint: "V2, same ρ as OOEEE", appendix: false },
  { word: "OEOEOEE", short: "V3", hint: "V3 = (OE)^2 OEE", appendix: false },
  { word: "OEOEOEOEE", short: "V4", hint: "V4", appendix: false },
  { word: "OEOEOEOEOEE", short: "V5", hint: "V5", appendix: false },
  { word: "OEOEOEOEOEOEE", short: "V6", hint: "V6, official λ**", appendix: false },
  { word: "OE", short: "OE", hint: "the one lossy production", appendix: false },
  {
    word: "OOEE",
    short: "OOEE",
    hint: "ρ > 1/2 — why Appendix C adds an E",
    appendix: true,
  },
  {
    word: "OOEEE",
    short: "OOEEE",
    hint: "Appendix C classification; not a Theorem 5.3 term",
    appendix: true,
  },
];

export function wordCounts(word: string): { a: number; b: number } {
  let a = 0;
  let b = 0;
  for (const ch of word) {
    if (ch === "E") a += 1;
    else if (ch === "O") b += 1;
    else throw new Error(`wordCounts expects O/E, got ${word}`);
  }
  return { a, b };
}

/** (5.7): ρ_w = 2^{-a} (3/2)^b */
export function rhoOfWord(word: string): number {
  const { a, b } = wordCounts(word);
  return 2 ** -a * 1.5 ** b;
}

/** (5.7): c^ideal = 2^{-|w|} / ρ_w */
export function idealCoeffOfWord(word: string): number {
  return 2 ** -word.length / rhoOfWord(word);
}

export function fiberExponent(rho: number): number {
  return 1 - rho;
}

export function rhoIdeal(rho: number): boolean {
  return rho <= 0.5 + 1e-12;
}

export function rungForWord(word: string): LadderId | null {
  const found = LADDER_RUNGS.find((rung) => rung.words.includes(word));
  return found?.id ?? null;
}
