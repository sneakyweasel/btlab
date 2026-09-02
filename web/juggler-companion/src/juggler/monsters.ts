/**
 * Shipped monster orbits. Peaks exceed the live 256-bit walker,
 * so the site loads them from JSON and does not recompute the walk.
 */

import snapshot from "../data/monster_orbits.json";
import { DISPLAY_BITS_MAX, ORBIT_STEPS_MAX } from "./constants";
import { orbitFromStates, walkOrbit, type OrbitView } from "./orbit";

export type OrbitSource = "live" | "monster";

export type ResolvedOrbit = OrbitView & {
  source: OrbitSource;
  label?: string;
  blurb?: string;
  peakBits?: number;
};

export type MonsterChip = {
  n: bigint;
  label: string;
  blurb: string;
  peakBits: number;
};

type MonsterRow = (typeof snapshot.orbits)[number];

const catalog: MonsterChip[] = snapshot.orbits.map((row) => ({
  n: BigInt(row.n),
  label: row.label,
  blurb: row.blurb,
  peakBits: row.peakBits,
}));

const byN = new Map<string, MonsterRow>(
  snapshot.orbits.map((row) => [row.n, row]),
);

if (snapshot.bitCapLive !== DISPLAY_BITS_MAX) {
  throw new Error("monster snapshot live cap is not 256 bits");
}

export function monsterCatalog(): readonly MonsterChip[] {
  return catalog;
}

export function monsterOrbit(n: bigint): ResolvedOrbit | null {
  const row = byN.get(n.toString());
  if (!row) return null;
  const states = row.states.map((text) => BigInt(text));
  return {
    ...orbitFromStates(n, states, row.word),
    source: "monster",
    label: row.label,
    blurb: row.blurb,
    peakBits: row.peakBits,
  };
}

export function resolveOrbit(n: bigint, steps: number = ORBIT_STEPS_MAX): ResolvedOrbit {
  const shipped = monsterOrbit(n);
  if (shipped) return shipped;
  return { ...walkOrbit(n, steps), source: "live" };
}
