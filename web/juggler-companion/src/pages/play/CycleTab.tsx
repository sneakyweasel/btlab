import { Metric } from "../../components/Metric";
import { StartControl } from "../../components/StartControl";
import { CycleNecklace } from "../../visuals/CycleNecklace";
import { usePlayState } from "../../context/PlayState";
import { CYCLE_PRESETS } from "../../juggler/constants";
import { formatInt, parsePositiveInt } from "../../juggler/format";
import { tryCycleWord } from "../../juggler/orbit";
import {
  evenCount,
  expanding,
  oddCount,
  parseCycleWord,
  rotateWord,
} from "../../juggler/word";

export function CycleTab() {
  const { nText, cycleWord, setCycleWord, cycleShift, setCycleShift } =
    usePlayState();
  const parsed = parseCycleWord(cycleWord);
  const n = parsePositiveInt(nText);
  const current = parsed ? rotateWord(parsed, cycleShift) : "";
  const trial = n !== null && current ? tryCycleWord(n, current) : null;
  return (
    <div className="space-y-5">
      <StartControl />
      <div className="flex flex-wrap items-end gap-3">
        <label className="text-sm text-muted">
          Cycle word
          <input
            className="ml-2 rounded border border-line bg-card px-2 py-1 font-mono uppercase"
            value={cycleWord}
            onChange={(event) => {
              setCycleWord(event.target.value.toUpperCase());
              setCycleShift(0);
            }}
          />
        </label>
        <select
          className="rounded border border-line bg-card px-2 py-1 font-mono text-sm"
          value=""
          onChange={(event) => {
            if (event.target.value) {
              setCycleWord(event.target.value);
              setCycleShift(0);
            }
          }}
        >
          <option value="">Presets</option>
          {CYCLE_PRESETS.map((preset) => (
            <option key={preset} value={preset}>
              {preset}
            </option>
          ))}
        </select>
        <button
          type="button"
          className="rounded-full bg-deep px-3 py-1 text-sm text-card"
          disabled={!parsed}
          onClick={() => {
            if (parsed) setCycleShift((cycleShift + 1) % parsed.length);
          }}
        >
          Rotate left
        </button>
        <button
          type="button"
          className="rounded-full border border-line px-3 py-1 text-sm"
          disabled={!parsed}
          onClick={() => {
            if (parsed) {
              setCycleShift((cycleShift - 1 + parsed.length) % parsed.length);
            }
          }}
        >
          Rotate right
        </button>
      </div>
      {parsed === null ? (
        <p className="text-sm text-warn">Use only O and E, length at most 16.</p>
      ) : (
        <>
          <div className="grid gap-6 lg:grid-cols-[16rem_1fr] lg:items-center">
            <CycleNecklace word={parsed} shift={cycleShift} />
            <div className="grid gap-3 sm:grid-cols-2">
              <Metric label="This spelling" value={current || "—"} />
              <Metric
                label="Odds / evens"
                value={`${oddCount(parsed)} / ${evenCount(parsed)}`}
              />
              <Metric label="Expanding?" value={expanding(parsed) ? "yes" : "no"} />
              <Metric
                label="Legal CycleMin shape?"
                value={current.startsWith("O") && current.endsWith("E") ? "maybe" : "no"}
                hint="a minimum is odd, so a CycleMin spelling starts O and ends E"
              />
            </div>
          </div>
          {!expanding(parsed) ? (
            <p className="text-sm text-warn">
              A contracting word cannot close a nontrivial cycle (Theorem 3.2).
            </p>
          ) : (
            <p className="text-sm text-muted">
              Expanding is necessary, not sufficient. Period 11 is already
              forced by four evens; Theorem 4.6 then excludes every period
              ≤ 25,780.
            </p>
          )}
          {trial ? (
            <div className="grid gap-3 sm:grid-cols-3">
              <Metric label="Followed the word?" value={trial.follows ? "yes" : "no"} />
              <Metric
                label="Image"
                value={trial.image === null ? "—" : formatInt(trial.image)}
              />
              <Metric
                label="Returned to n?"
                value={trial.returned ? "yes" : "no"}
                hint="a miss here is only a witness at this n"
              />
            </div>
          ) : null}
          {trial?.bitCapped ? (
            <p className="text-sm text-warn">A value exceeded the display cap.</p>
          ) : null}
          {trial && !trial.follows && trial.failIndex !== null ? (
            <p className="text-sm text-muted">
              Letter {trial.failIndex} fails at{" "}
              {trial.failState === null ? "—" : formatInt(trial.failState)}.
            </p>
          ) : null}
        </>
      )}
    </div>
  );
}
