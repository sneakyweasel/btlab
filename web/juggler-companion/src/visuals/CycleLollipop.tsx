import { formatInt } from "../juggler/format";
import { letterOf } from "../juggler/map";
import type { STRING_TOUR_PRESETS } from "../juggler/constants";

export type StringTourExample = (typeof STRING_TOUR_PRESETS)[number];

export function CycleLollipop({ example }: { example: StringTourExample }) {
  const stringStates = example.states.slice(0, -1);
  const word = stringStates.map((state) => letterOf(state)).join("");
  const offCycle = stringStates[stringStates.length - 1];
  const peak = stringStates.reduce((best, state) => (state > best ? state : best));
  const oddRuns = [...word].filter(
    (letter, index) => letter === "O" && (index === 0 || word[index - 1] !== "O"),
  ).length;

  return (
    <div className="rounded-xl border border-line bg-paper/70 px-3 py-3">
      <p className="text-xs uppercase tracking-wide text-muted">
        String — itinerary before the first visit to a cycle
      </p>
      <p className="mt-1 text-sm text-muted">{example.hint}</p>
      <div
        className="mt-3 flex flex-wrap items-end gap-1.5"
        aria-label={`String ${word} onto 1`}
      >
        {stringStates.map((state, index) => {
          const letter = letterOf(state);
          const odd = letter === "O";
          const last = index === stringStates.length - 1;
          return (
            <span key={`${index}-${state.toString()}`} className="grid justify-items-center gap-0.5">
              <span
                className={`inline-flex min-w-8 items-center justify-center rounded-md px-1.5 py-1 font-mono text-xs text-card ${
                  last ? "ring-2 ring-ink ring-offset-2 ring-offset-paper" : ""
                }`}
                style={{ background: odd ? "#c45c26" : "#1f6f6a" }}
                title={state.toString()}
              >
                {formatInt(state)}
              </span>
              <span
                className="font-mono text-xs"
                style={{ color: odd ? "#c45c26" : "#1f6f6a" }}
              >
                {letter}
              </span>
              <span className="h-3 text-[10px] uppercase tracking-wide text-muted">
                {last ? "t" : ""}
              </span>
            </span>
          );
        })}
        <span className="mb-3 text-muted">→</span>
        <span className="grid justify-items-center gap-0.5">
          <span className="inline-flex h-10 min-w-10 items-center justify-center rounded-full border-2 border-ink bg-odd font-mono text-sm text-card">
            1
          </span>
          <span className="font-mono text-xs text-odd">O</span>
          <span className="h-3 text-[10px] uppercase tracking-wide text-muted">
            balloon
          </span>
        </span>
      </div>
      <p className="mt-1 font-mono text-sm text-ink">
        {word}
        <span className="ml-2 font-sans text-muted">
          · {oddRuns === 1 ? "1 odd-run" : `${oddRuns} odd-runs`} · peak{" "}
          {formatInt(peak)}
        </span>
      </p>
      <p className="mt-2 text-sm text-muted">
        Join {offCycle === undefined ? "—" : formatInt(offCycle)} → 1 ← 1. The
        string is not a cycle itinerary. CycleMin is a cut on the balloon, not
        where the stem attaches. Hitting 1 here is one trajectory, not a halt
        theorem.
      </p>
    </div>
  );
}
