import { Tex } from "../components/Tex";
import { formatGrouped } from "../juggler/format";
import { EVEN_COUNT_LADDER, RECOVERIES, type Recovery } from "../juggler/runSuffix";

type RunSuffixTableProps = {
  selected: string;
  onSelect: (row: Recovery) => void;
  compact?: boolean;
};

/** Corollary 3.27: eleven statements, ten suffixes. Click a row to load it. */
export function RunSuffixTable({ selected, onSelect, compact = false }: RunSuffixTableProps) {
  return (
    <div className="space-y-4">
      <div className="overflow-x-auto">
        <table className="w-full min-w-[36rem] text-left text-sm">
          <thead className="border-b border-line text-xs uppercase tracking-wide text-muted">
            <tr>
              <th className="py-2 pr-3 font-medium">suffix u</th>
              <th className="py-2 pr-3 font-medium">T(u)</th>
              <th className="py-2 pr-3 font-medium">least a</th>
              <th className="py-2 pr-3 font-medium">n_u crude</th>
              <th className="py-2 pr-3 font-medium">n_u sharp</th>
              <th className="py-2 font-medium">printed in</th>
            </tr>
          </thead>
          <tbody className="font-mono text-xs">
            {RECOVERIES.map((row) => {
              const active = row.suffix === selected;
              const strengthen = row.suffix === "E";
              return (
                <tr key={row.suffix} className="border-b border-line/50">
                  <td className="py-1.5 pr-3">
                    <button
                      type="button"
                      className={`rounded-full px-2 py-0.5 ${
                        active ? "bg-deep text-card" : "border border-line text-ink hover:bg-paper"
                      }`}
                      onClick={() => onSelect(row)}
                    >
                      {row.suffix}
                    </button>
                  </td>
                  <td className="py-1.5 pr-3">{formatTLabel(row.suffix)}</td>
                  <td className="py-1.5 pr-3">
                    {row.lawA}
                    {strengthen ? (
                      <span className="ml-1 text-muted">paper {row.printedA}</span>
                    ) : null}
                  </td>
                  <td className="py-1.5 pr-3">{formatGrouped(row.nCrude)}</td>
                  <td className="py-1.5 pr-3">{formatGrouped(row.nSharp)}</td>
                  <td className="py-1.5 font-sans text-muted">{row.source}</td>
                </tr>
              );
            })}
          </tbody>
        </table>
      </div>
      <p className="text-sm text-muted">
        Nine least-a values are the ones the theorems print. The tenth is a
        strengthening: for u = E the law excludes a ≥ 2, so OOE needs no appeal
        to the census of Theorem 3.6. Every crude threshold sits four orders
        below the certified floor.
      </p>
      {compact ? null : <EvenCountLadder />}
    </div>
  );
}

function formatTLabel(suffix: string): string {
  const odds = [...suffix].filter((letter) => letter === "O").length;
  const numer = 2 ** suffix.length;
  if (odds === 0) return String(numer);
  return `${numer}/${3 ** odds}`;
}

function EvenCountLadder() {
  return (
    <section className="space-y-2 rounded-xl border border-line bg-paper/50 p-3">
      <header className="space-y-1">
        <h3 className="font-serif text-lg">Even-count ladder</h3>
        <p className="text-sm text-muted">
          Theorem 3.31 applies the sharp law at every run of an e-even word.
          The form counts are shipped, not enumerated here. A cycle minimum is
          at least 300, so the last rung n ≥ 64 is free. The interactive
          CycleMin checker stays on Theorem 3.22.
        </p>
      </header>
      <div className="overflow-x-auto">
        <table className="w-full text-sm">
          <thead className="border-b border-line text-xs uppercase tracking-wide text-muted">
            <tr>
              <th className="py-1.5 pr-3 text-left font-medium">e</th>
              <th className="py-1.5 pr-3 text-left font-medium">run bounds</th>
              <th className="py-1.5 pr-3 text-left font-medium">forms</th>
              <th className="py-1.5 text-left font-medium">closed at</th>
            </tr>
          </thead>
          <tbody className="font-mono text-xs">
            {EVEN_COUNT_LADDER.map((row) => (
              <tr key={row.e} className="border-b border-line/50">
                <td className="py-1 pr-3">{row.e}</td>
                <td className="py-1 pr-3">({row.bounds.join(", ")})</td>
                <td className="py-1 pr-3">{formatGrouped(row.forms)}</td>
                <td className="py-1">{row.closedAt}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <p className="text-xs text-muted">
        Given e ≥ 8, formal expansion 2<sup>L</sup> &lt; 3<sup>L−8</sup> first
        holds at L = 22. That is the floor-free period the sharp law reaches;
        it is not Lean.
      </p>
    </section>
  );
}

const RUNGS = [
  {
    name: "Lemma 3.24",
    tex: String.raw`J^a(n)\ge 4\bigl(n/4\bigr)^{(3/2)^a}`,
    lean: "odd-run envelope, closed form",
    status: "prose",
    note: "Factor 4 paid once. The orange curve.",
  },
  {
    name: "Lemma 3.25",
    tex: String.raw`B(\varepsilon)=n+1,\quad B(Eu)=B(u)^2,\quad B(Ou)=\min\{c:c^3\ge B(u)^2\}`,
    lean: "exact backward envelope",
    status: "prose",
    note: "The blue curve. Excess over (n+1)^{T(u)} is rounding.",
  },
  {
    name: "Theorem 3.26",
    tex: String.raw`4(n/4)^{(3/2)^a}<B(u)`,
    lean: "run-suffix law, crude",
    status: "human proof",
    note: "Costs a margin log 4 / log n.",
  },
  {
    name: "Theorem 3.29",
    tex: String.raw`n^{X_a}<(n+1)^{Y_a}B(u)^{2^a}`,
    lean: "O7EEEEGap.lean at a = 7",
    status: "Lean + census",
    note: "Costs a margin of order 1/(n log n). Theorem 3.31 is the census.",
  },
] as const;

export function RunSuffixHierarchy() {
  return (
    <ol className="grid gap-2 sm:grid-cols-2 lg:grid-cols-4">
      {RUNGS.map((rung, index) => (
        <li key={rung.name} className="rounded-lg border border-line bg-card px-3 py-2">
          <div className="flex items-baseline justify-between gap-2">
            <span className="font-serif text-sm">
              <span className="mr-1 text-muted">{index + 1}.</span>
              {rung.name}
            </span>
            <span className="rounded-full border border-line px-1.5 text-[10px] uppercase tracking-wide text-muted">
              {rung.status}
            </span>
          </div>
          <div className="mt-1 overflow-x-auto text-sm">
            <Tex>{rung.tex}</Tex>
          </div>
          <div className="mt-1 font-mono text-[11px] text-deep">{rung.lean}</div>
          <div className="text-xs text-muted">{rung.note}</div>
        </li>
      ))}
    </ol>
  );
}
