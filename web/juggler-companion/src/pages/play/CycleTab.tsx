import { Metric } from "../../components/Metric";
import { StartControl } from "../../components/StartControl";
import { CycleNecklace } from "../../visuals/CycleNecklace";
import { usePlayState } from "../../context/PlayState";
import { CYCLE_PRESETS } from "../../juggler/constants";
import { formatInt, parsePositiveInt } from "../../juggler/format";
import { tryCycleItinerary } from "../../juggler/trajectory";
import {
  assembleFillCounts,
  cycleMinShape,
  expanding,
  formatNecklaceFill,
  necklaceFillToRuns,
  oddEvenRuns,
  parseCycleItinerary,
  rotateItinerary,
  tryAssembleFill,
} from "../../juggler/itinerary";

export function CycleTab() {
  const { nText, cycleItinerary, setCycleItinerary, cycleShift, setCycleShift } =
    usePlayState();
  const parsed = parseCycleItinerary(cycleItinerary);
  const n = parsePositiveInt(nText);
  const current = parsed ? rotateItinerary(parsed, cycleShift) : "";
  const shape = current ? cycleMinShape(current) : null;
  const fill = current ? tryAssembleFill(current) : null;
  const fillCounts = fill ? assembleFillCounts(fill) : null;
  const runs = current ? oddEvenRuns(current) : null;
  const trial = n !== null && current ? tryCycleItinerary(n, current) : null;
  return (
    <div className="space-y-5">
      <StartControl />
      <div className="flex flex-wrap items-end gap-3">
        <label className="text-sm text-muted">
          Cycle itinerary
          <input
            className="ml-2 rounded border border-line bg-card px-2 py-1 font-mono uppercase"
            value={cycleItinerary}
            onChange={(event) => {
              setCycleItinerary(event.target.value.toUpperCase());
              setCycleShift(0);
            }}
          />
        </label>
        <select
          className="rounded border border-line bg-card px-2 py-1 font-mono text-sm"
          value=""
          onChange={(event) => {
            if (event.target.value) {
              setCycleItinerary(event.target.value);
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
            <CycleNecklace
              word={parsed}
              shift={cycleShift}
              minIndex={cycleMinShape(parsed).cycleMinShaped ? 0 : undefined}
              onSelectIndex={setCycleShift}
            />
            <div className="grid gap-3 sm:grid-cols-2">
              <Metric label="This spelling" value={current || "—"} />
              <Metric
                label="Odds / evens"
                value={`${shape?.oddCount ?? 0} / ${shape?.evenCount ?? 0}`}
                hint={
                  shape
                    ? `unplaced odds ${shape.unplacedOdds}, extra evens ${shape.extraEvens}`
                    : undefined
                }
              />
              <Metric label="Expanding?" value={expanding(parsed) ? "yes" : "no"} />
              <Metric
                label="CycleMin shape?"
                value={shape?.cycleMinShaped ? "yes" : "no"}
                hint={
                  shape?.cycleMinShaped
                    ? `${shape.seam.replace("|", " | n | ")} seam. Necessary, not a cycle (CycleMinShape_not_of_CycleMin).`
                    : "needs OO…E, four evens, seven odds, expanding, last odd-run a ≤ 1"
                }
              />
              <Metric
                label="odd-even runs"
                value={runs ? `[${runs.join(", ")}]` : "needs terminal E"}
                hint={
                  fill
                    ? `bead projection ${JSON.stringify(necklaceFillToRuns(fill))}`
                    : runs
                      ? "full run list; not a four-slot fill"
                      : undefined
                }
              />
              <Metric
                label="assembleFill?"
                value={fill ? formatNecklaceFill(fill) : "no"}
                hint={
                  fillCounts
                    ? `#O=${fillCounts.oddCount}, #E=${fillCounts.evenCount}, L=${fillCounts.length}`
                    : "four-slot candidate; not a CycleMin reconstruction"
                }
              />
            </div>
          </div>
          {!expanding(parsed) ? (
            <p className="text-sm text-warn">
              A contracting itinerary cannot close a nontrivial cycle (Theorem 3.2).
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
              <Metric label="Followed the itinerary?" value={trial.follows ? "yes" : "no"} />
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
