/**
 * Shipped monster trajectories. Peaks exceed the live 256-bit walker,
 * so the site loads them from JSON and does not recompute the walk.
 */

import snapshot from "../data/monster_trajectories.json";
import { DISPLAY_BITS_MAX, TRAJECTORY_STEPS_MAX } from "./constants";
import { trajectoryFromStates, walkTrajectory, type TrajectoryView } from "./trajectory";

export type TrajectorySource = "live" | "monster";

export type ResolvedTrajectory = TrajectoryView & {
  source: TrajectorySource;
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

type MonsterRow = (typeof snapshot.trajectories)[number];

const catalog: MonsterChip[] = snapshot.trajectories.map((row) => ({
  n: BigInt(row.n),
  label: row.label,
  blurb: row.blurb,
  peakBits: row.peakBits,
}));

const byN = new Map<string, MonsterRow>(
  snapshot.trajectories.map((row) => [row.n, row]),
);

if (snapshot.bitCapLive !== DISPLAY_BITS_MAX) {
  throw new Error("monster snapshot live cap is not 256 bits");
}

export function monsterCatalog(): readonly MonsterChip[] {
  return catalog;
}

export function monsterTrajectory(n: bigint): ResolvedTrajectory | null {
  const row = byN.get(n.toString());
  if (!row) return null;
  const states = row.states.map((text) => BigInt(text));
  return {
    ...trajectoryFromStates(n, states, row.word),
    source: "monster",
    label: row.label,
    blurb: row.blurb,
    peakBits: row.peakBits,
  };
}

export function resolveTrajectory(
  n: bigint,
  steps: number = TRAJECTORY_STEPS_MAX,
): ResolvedTrajectory {
  const shipped = monsterTrajectory(n);
  if (shipped) return shipped;
  return { ...walkTrajectory(n, steps), source: "live" };
}
