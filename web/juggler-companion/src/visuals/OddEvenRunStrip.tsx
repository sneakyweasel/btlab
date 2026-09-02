import {
  formatNecklaceFill,
  formatOddEvenRuns,
  necklaceFillToRuns,
  oddEvenRuns,
  runsEqual,
  type NecklaceFill,
} from "../juggler/itinerary";

const ODD = "#c45c26";
const EVEN = "#1f6f6a";

function Tile({ letter }: { letter: "O" | "E" }) {
  return (
    <span
      className="inline-flex h-7 min-w-7 items-center justify-center rounded-md font-mono text-sm text-card"
      style={{ background: letter === "O" ? ODD : EVEN }}
    >
      {letter}
    </span>
  );
}

function runLabel(index: number, last: boolean, odds: number): string {
  if (index === 0) return odds >= 2 ? "a1 >= 2" : "a1";
  if (last) return odds <= 1 ? "ae <= 1" : "ae";
  return `a${index + 1}`;
}

type OddEvenRunStripProps = {
  word: string;
  fill?: NecklaceFill | null;
  onSelect?: () => void;
};

export function OddEvenRunStrip({ word, fill = null, onSelect }: OddEvenRunStripProps) {
  const runs = oddEvenRuns(word);
  const projected = fill ? necklaceFillToRuns(fill) : null;
  const matchesFill = Boolean(runs && projected && runsEqual(runs, projected));

  return (
    <div className="space-y-2">
      <button
        type="button"
        data-keep-focus
        className="block w-full rounded-xl border border-line bg-paper/70 px-3 py-2 text-left"
        onClick={onSelect}
      >
        <p className="text-xs uppercase tracking-wide text-muted">
          odd-even runs — cycleMin_has_full_odd_even_run_form
        </p>
        {runs ? (
          <div className="mt-2 flex flex-wrap items-end gap-2">
            {runs.map((odds, index) => {
              const last = index === runs.length - 1;
              return (
                <span
                  key={`${index}-${odds}`}
                  className="grid justify-items-center gap-1 rounded-lg border border-line bg-card px-1.5 py-1"
                >
                  <span className="flex items-center gap-0.5">
                    {odds === 0 ? (
                      <span className="inline-flex h-7 w-4 items-center justify-center font-mono text-xs text-muted">
                        ·
                      </span>
                    ) : (
                      Array.from({ length: odds }, (_, letter) => (
                        <Tile key={letter} letter="O" />
                      ))
                    )}
                    <Tile letter="E" />
                  </span>
                  <span className="text-[10px] uppercase tracking-wide text-muted">
                    {runLabel(index, last, odds)}
                  </span>
                </span>
              );
            })}
          </div>
        ) : (
          <p className="mt-2 text-sm text-muted">Needs a terminal E to split.</p>
        )}
        <p className="mt-2 font-mono text-sm text-ink">
          {runs ? formatOddEvenRuns(runs) : "—"}
        </p>
        <p className="mt-1 text-xs text-muted">
          {runs && projected && matchesFill
            ? `equals NecklaceFill.toRuns of ${formatNecklaceFill(fill!)} — bead projection, not a cycle`
            : runs && projected
              ? `bead projection ${formatOddEvenRuns(projected)} bunches extra evens; this list is finer`
              : runs
                ? "not a four-slot fill — the bead schema forgets interior run structure"
                : "a CycleMin word ends E, so it has this unique run list"}
        </p>
      </button>
    </div>
  );
}
