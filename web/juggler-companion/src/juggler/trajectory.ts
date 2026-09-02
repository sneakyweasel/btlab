/**
 * Bounded trajectory walk. Display fork of
 * visualization.juggler_finite_dynamics.walk_trajectory.
 */

import {
  DISPLAY_BITS_MAX,
  TRAJECTORY_STEPS_MAX,
} from "./constants";
import { bitLength, floorPower, letterOf } from "./map";

export type TrajectoryRow = {
  step: number;
  state: bigint;
  letter: "" | "O" | "E";
  parity: "odd" | "even";
  bits: number;
};

export type TrajectoryView = {
  n: bigint;
  stepsAsked: number;
  states: bigint[];
  word: string;
  reachedOne: boolean;
  bitCapped: boolean;
  tooLarge: boolean;
  rows: TrajectoryRow[];
};

export function rowOf(step: number, state: bigint, letter: "" | "O" | "E"): TrajectoryRow {
  return {
    step,
    state,
    letter,
    parity: state % 2n === 1n ? "odd" : "even",
    bits: bitLength(state),
  };
}

export function walkTrajectory(n: bigint, steps: number): TrajectoryView {
  if (n < 1n) {
    throw new Error("walkTrajectory requires n ≥ 1");
  }
  const cap = Math.min(Math.max(steps, 0), TRAJECTORY_STEPS_MAX);
  if (bitLength(n) > DISPLAY_BITS_MAX) {
    return {
      n,
      stepsAsked: cap,
      states: [n],
      word: "",
      reachedOne: n === 1n,
      bitCapped: true,
      tooLarge: true,
      rows: [rowOf(0, n, "")],
    };
  }
  const path: bigint[] = [n];
  const letters: Array<"O" | "E"> = [];
  let bitCapped = false;
  let current = n;
  for (let i = 0; i < cap; i += 1) {
    if (bitLength(current) > DISPLAY_BITS_MAX) {
      bitCapped = true;
      break;
    }
    const letter = letterOf(current);
    const next = floorPower(current);
    if (bitLength(next) > DISPLAY_BITS_MAX) {
      bitCapped = true;
      letters.push(letter);
      path.push(next);
      break;
    }
    letters.push(letter);
    path.push(next);
    current = next;
    if (current === 1n) break;
  }
  const rows = path.map((state, index) =>
    rowOf(index, state, letters[index] ?? ""),
  );
  return {
    n,
    stepsAsked: cap,
    states: path,
    word: letters.join(""),
    reachedOne: path[path.length - 1] === 1n,
    bitCapped,
    tooLarge: false,
    rows,
  };
}

export function trajectoryFromStates(
  n: bigint,
  states: bigint[],
  word: string,
): TrajectoryView {
  const rows = states.map((state, index) =>
    rowOf(index, state, (word[index] as "O" | "E") ?? ""),
  );
  return {
    n,
    stepsAsked: Math.max(states.length - 1, 0),
    states,
    word,
    reachedOne: states[states.length - 1] === 1n,
    bitCapped: false,
    tooLarge: false,
    rows,
  };
}

export function tryCycleWord(
  n: bigint,
  word: string,
): {
  follows: boolean;
  image: bigint | null;
  returned: boolean;
  failIndex: number | null;
  failState: bigint | null;
  bitCapped: boolean;
} {
  let current = n;
  for (let index = 0; index < word.length; index += 1) {
    if (bitLength(current) > DISPLAY_BITS_MAX) {
      return {
        follows: false,
        image: null,
        returned: false,
        failIndex: index,
        failState: current,
        bitCapped: true,
      };
    }
    if (word[index] !== letterOf(current)) {
      return {
        follows: false,
        image: null,
        returned: false,
        failIndex: index,
        failState: current,
        bitCapped: false,
      };
    }
    current = floorPower(current);
  }
  return {
    follows: true,
    image: current,
    returned: current === n,
    failIndex: null,
    failState: null,
    bitCapped: bitLength(current) > DISPLAY_BITS_MAX,
  };
}
