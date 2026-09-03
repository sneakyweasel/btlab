import { useMemo } from "react";
import { usePlayState } from "../context/PlayState";
import { NECKLACE_PRESETS, NECKLACE_WORD_MAX } from "../juggler/constants";
import { formatInt, parsePositiveInt } from "../juggler/format";
import { cycleMinShape, parseItinerary } from "../juggler/itinerary";
import { necklaceView } from "../juggler/necklace";
import { ExcursionTiles, ExcursionWave } from "../visuals/ExcursionWave";
import { Metric } from "./Metric";

type NecklaceExplorerProps = {
  /** Tour-sized: presets only, no free inputs, no verdict cards. */
  compact?: boolean;
};

function verdict(value: boolean | null): string {
  if (value === null) return "—";
  return value ? "yes" : "no";
}

/**
 * Movement 1: a realized walk read as a necklace of excursions. The
 * start and the word are shared PlayState, so the playground and the
 * tour show the same wave.
 */
export function NecklaceExplorer({ compact = false }: NecklaceExplorerProps) {
  const { necklaceNText, setNecklaceNText, necklaceWord, setNecklaceWord } = usePlayState();
  const n = parsePositiveInt(necklaceNText);
  const word = parseItinerary(necklaceWord, NECKLACE_WORD_MAX);
  const view = useMemo(
    () => (n === null || word === null || word.length === 0 ? null : necklaceView(n, word)),
    [n, word],
  );
  const shape = word ? cycleMinShape(word) : null;
  const activePreset = NECKLACE_PRESETS.find(
    (preset) => preset.n.toString() === necklaceNText.trim() && preset.word === word,
  );

  return (
    <div className="space-y-3">
      <div className="flex flex-wrap items-center gap-1.5">
        {NECKLACE_PRESETS.map((preset) => {
          const active = preset.id === activePreset?.id;
          return (
            <button
              key={preset.id}
              type="button"
              title={preset.hint}
              className={`rounded-full border px-2.5 py-0.5 text-xs ${
                active ? "border-deep bg-deep text-card" : "border-line bg-card text-muted hover:bg-paper"
              }`}
              onClick={() => {
                setNecklaceNText(preset.n.toString());
                setNecklaceWord(preset.word);
              }}
            >
              {preset.label}
            </button>
          );
        })}
      </div>
      {compact ? null : (
        <div className="flex flex-wrap items-end gap-3">
          <label className="text-sm text-muted">
            Start n
            <input
              className="ml-2 w-32 rounded border border-line bg-card px-2 py-1 font-mono"
              value={necklaceNText}
              onChange={(event) => setNecklaceNText(event.target.value)}
              inputMode="numeric"
            />
          </label>
          <label className="text-sm text-muted">
            Word to walk
            <input
              className="ml-2 w-64 rounded border border-line bg-card px-2 py-1 font-mono"
              value={necklaceWord}
              onChange={(event) => setNecklaceWord(event.target.value)}
              spellCheck={false}
            />
          </label>
          {n === null ? <span className="text-sm text-warn">Enter a positive integer.</span> : null}
          {word === null ? (
            <span className="text-sm text-warn">Only O and E, at most {NECKLACE_WORD_MAX} letters.</span>
          ) : null}
        </div>
      )}
      {view ? (
        <>
          <ExcursionWave view={view} compact={compact} />
          <ExcursionTiles view={view} />
          {activePreset ? <p className="text-sm text-muted">{activePreset.hint}</p> : null}
          {compact ? null : (
            <div className="grid gap-3 sm:grid-cols-2 lg:grid-cols-5">
              <Metric
                label="follows the word?"
                value={view.follows ? "yes" : view.failIndex === null ? "stopped" : `no, at letter ${view.failIndex + 1}`}
                hint={`realized ${view.realized || "—"}`}
              />
              <Metric
                label="stays ≥ n?"
                value={view.belowMinimumIndex === null ? "yes" : `no, step ${view.belowMinimumIndex}`}
                hint="a cycle minimum never dips"
              />
              <Metric
                label="first peak ≥ (n+1)²?"
                value={verdict(view.firstPeakOvershoots)}
                hint={view.firstPeak === null ? "no peak yet" : `p₀ = ${formatInt(view.firstPeak)}`}
              />
              <Metric
                label="last peak lands?"
                value={verdict(view.lastPeakLands)}
                hint={
                  view.lastPeak === null
                    ? "no peak yet"
                    : `needs ${formatInt(view.nSquared + 1n)} ≤ p < ${formatInt(view.nPlusOneSquared)}`
                }
              />
              <Metric
                label="returns to n?"
                value={view.image === null ? "—" : view.returns ? "yes" : "no"}
                hint={shape?.cycleMinShaped ? "word is CycleMin-shaped" : "word is not CycleMin-shaped"}
              />
            </div>
          )}
        </>
      ) : (
        <p className="text-sm text-muted">Choose a start and a nonempty O/E word.</p>
      )}
    </div>
  );
}
