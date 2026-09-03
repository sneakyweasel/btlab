import { formatInt } from "../juggler/format";
import { oddCount } from "../juggler/itinerary";
import { bitLength, letterOf } from "../juggler/map";
import { IdealExponent } from "./IdealExponent";

const WINDOW = 7;

type LinkedWalkProps = {
  states: readonly bigint[];
  itinerary: string;
  active: number;
  note?: string | null;
  onSeek?: (index: number) => void;
};

function letterAt(itinerary: string, states: readonly bigint[], index: number): "" | "O" | "E" {
  const fromWord = itinerary[index];
  if (fromWord === "O" || fromWord === "E") return fromWord;
  if (index >= states.length - 1) return "";
  const state = states[index];
  return state === undefined ? "" : letterOf(state);
}

function windowRange(length: number, active: number, size: number): { start: number; end: number } {
  if (length <= size) return { start: 0, end: length };
  const half = Math.floor(size / 2);
  let start = active - half;
  let end = start + size;
  if (start < 0) {
    start = 0;
    end = size;
  }
  if (end > length) {
    end = length;
    start = length - size;
  }
  return { start, end };
}

function shortInt(value: bigint): string {
  const bits = bitLength(value);
  if (bits > 24) {
    const exp = Math.round((bits - 1) * Math.LOG10E * Math.LN2);
    return `~10^${exp}`;
  }
  const text = value.toString();
  if (text.length <= 6) return text;
  return `${text.slice(0, 3)}…`;
}

export function LinkedWalk({
  states,
  itinerary,
  active,
  note,
  onSeek,
}: LinkedWalkProps) {
  const cursor = Math.max(0, Math.min(active, Math.max(states.length - 1, 0)));
  const realized = Math.max(0, Math.min(cursor, itinerary.length));
  const { start, end } = windowRange(states.length, cursor, WINDOW);
  const visible = states.slice(start, end);
  const hiddenBefore = start > 0;
  const hiddenAfter = end < states.length;

  return (
    <div className="min-w-0 overflow-hidden rounded-2xl border border-line bg-paper/70 px-4 py-3">
      <div className="flex flex-wrap items-baseline justify-between gap-x-6 gap-y-1">
        <p className="text-xs uppercase tracking-wide text-muted">
          Trajectory and itinerary
        </p>
        <p className="text-sm text-muted">
          Numbers are the trajectory. The colored word is the itinerary.
        </p>
      </div>
      {states.length === 0 ? (
        <p className="mt-3 text-sm text-muted">No walk to show yet.</p>
      ) : (
        <div className="mt-3 min-w-0">
          <div className="flex items-stretch">
            <div className="flex shrink-0 flex-col justify-between border-r border-line py-1 pr-3">
              <p className="flex h-10 items-center text-xs font-semibold uppercase tracking-wide text-ink">
                Trajectory
              </p>
              <p className="flex h-9 items-center text-xs font-semibold uppercase tracking-wide text-ink">
                Itinerary
              </p>
            </div>
            {hiddenBefore ? (
              <button
                type="button"
                className="flex w-7 shrink-0 items-center justify-center text-muted disabled:opacity-30"
                aria-label="Earlier steps"
                disabled={!onSeek}
                onClick={() => onSeek?.(start - 1)}
              >
                ‹
              </button>
            ) : null}
            <ol className="flex min-w-0 flex-1 list-none justify-center p-0">
              {visible.map((state, offset) => {
                const index = start + offset;
                const letter = letterAt(itinerary, states, index);
                const odd = (letter || letterOf(state)) === "O";
                const isActive = index === cursor;
                const visited = index <= cursor;
                const shown = shortInt(state);
                const full = formatInt(state);
                const letterState =
                  letter === ""
                    ? "end"
                    : index < cursor
                      ? "taken"
                      : index === cursor
                        ? "now"
                        : "later";
                return (
                  <li key={`${index}-${state.toString()}`} className="relative min-w-0 flex-1">
                    <button
                      type="button"
                      title={full}
                      disabled={!onSeek}
                      aria-current={isActive ? "step" : undefined}
                      aria-label={
                        letter
                          ? `Step ${index}, trajectory ${full}, itinerary ${letter}`
                          : `Step ${index}, trajectory ${full}, end of this prefix`
                      }
                      onClick={() => onSeek?.(index)}
                      className={`grid w-full justify-items-center px-1 py-1 ${
                        onSeek ? "cursor-pointer" : "cursor-default"
                      } ${visited ? "" : "opacity-35"}`}
                    >
                      <span
                        className={`flex h-10 w-full max-w-[5.5rem] items-center justify-center font-mono text-sm leading-none text-ink ${
                          isActive ? "border-b-2 border-ink" : "border-b-2 border-transparent"
                        }`}
                      >
                        {shown}
                      </span>
                      <span
                        className={`flex h-9 items-center font-mono text-xl leading-none tracking-wide ${
                          letterState === "later"
                            ? "text-line"
                            : letterState === "end"
                              ? "text-muted"
                              : odd
                                ? "text-odd"
                                : "text-even"
                        } ${isActive && letterState === "now" ? "underline decoration-2 underline-offset-4" : ""}`}
                      >
                        {letterState === "later" ? "·" : letter || "—"}
                      </span>
                    </button>
                    {index < end - 1 ? (
                      <span
                        className="pointer-events-none absolute top-[0.95rem] right-0 z-0 translate-x-1/2 text-sm text-muted"
                        aria-hidden
                      >
                        →
                      </span>
                    ) : null}
                  </li>
                );
              })}
            </ol>
            {hiddenAfter ? (
              <button
                type="button"
                className="flex w-7 shrink-0 items-center justify-center text-muted disabled:opacity-30"
                aria-label="Later steps"
                disabled={!onSeek}
                onClick={() => onSeek?.(end)}
              >
                ›
              </button>
            ) : null}
          </div>
        </div>
      )}
      <p className="mt-3 text-sm text-muted">
        {states.length === 0
          ? "The browser did not write a walk for this start."
          : realized === 0
            ? "The underlined value is the start. Its letter is the branch this step will take. Play or step to write the word."
            : realized < itinerary.length
              ? `${realized} of ${itinerary.length} letters in the word.`
              : `${itinerary.length} letters in the word.`}
        {note ? ` ${note}` : ""}
      </p>
      {realized > 0 ? (
        <div className="mt-4 border-t border-line pt-3">
          <IdealExponent
            odds={oddCount(itinerary.slice(0, realized))}
            length={realized}
            start={states[0]}
          />
        </div>
      ) : null}
    </div>
  );
}
