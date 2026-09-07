import { Tex } from "../components/Tex";
import { formatGrouped } from "../juggler/format";
import {
  FLOOR_COMPARISONS,
  SURVIVOR_EXPONENTS,
  type FloorComparison,
} from "../juggler/gapTransfer";

type GapFloorTableProps = {
  selectedN: number;
  onSelect: (row: FloorComparison) => void;
};

export function GapFloorTable({ selectedN, onSelect }: GapFloorTableProps) {
  return (
    <div className="overflow-x-auto">
      <table className="w-full min-w-[36rem] text-left text-sm">
        <thead className="border-b border-line text-xs uppercase tracking-wide text-muted">
          <tr>
            <th className="py-2 pr-3 font-medium">floor</th>
            <th className="py-2 pr-3 font-medium">N₀</th>
            <th className="py-2 pr-3 font-medium">Rhin L</th>
            <th className="py-2 pr-3 font-medium">printed L</th>
            <th className="py-2 font-medium">source</th>
          </tr>
        </thead>
        <tbody className="font-mono text-xs">
          {FLOOR_COMPARISONS.map((row) => {
            const active = row.n0 === selectedN;
            return (
              <tr key={row.name} className="border-b border-line/50">
                <td className="py-1.5 pr-3">
                  <button
                    type="button"
                    className={`rounded-full px-2 py-0.5 ${
                      active ? "bg-deep text-card" : "border border-line text-ink hover:bg-paper"
                    }`}
                    onClick={() => onSelect(row)}
                  >
                    {row.name}
                  </button>
                </td>
                <td className="py-1.5 pr-3">{formatGrouped(row.n0)}</td>
                <td className="py-1.5 pr-3">≥ {row.rhinL}</td>
                <td className="py-1.5 pr-3">≥ {formatGrouped(row.printedL)}</td>
                <td className="py-1.5 font-sans text-muted">{row.theorem}</td>
              </tr>
            );
          })}
        </tbody>
      </table>
    </div>
  );
}

export function SurvivorExponentTable() {
  return (
    <section className="space-y-2 rounded-xl border border-line bg-paper/50 p-3">
      <header className="space-y-1">
        <h3 className="font-serif text-lg">Where the survivors live</h3>
        <p className="text-sm text-muted">
          The paper’s measured exponent log L / log n_max. They sit at L ≈ n
          <sup>0.59</sup>, far inside the long regime. No refinement of the
          defect upper bound moves them into the short one.
        </p>
      </header>
      <div className="overflow-x-auto">
        <table className="w-full text-sm">
          <thead className="border-b border-line text-xs uppercase tracking-wide text-muted">
            <tr>
              <th className="py-1.5 pr-3 text-left font-medium">L</th>
              <th className="py-1.5 pr-3 text-left font-medium">n_max</th>
              <th className="py-1.5 text-left font-medium">log L / log n_max</th>
            </tr>
          </thead>
          <tbody className="font-mono text-xs">
            {SURVIVOR_EXPONENTS.map((row) => (
              <tr key={row.L} className="border-b border-line/50">
                <td className="py-1 pr-3">{formatGrouped(row.L)}</td>
                <td className="py-1 pr-3">{formatGrouped(row.nMax)}</td>
                <td className="py-1">{row.exponent.toFixed(3)}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </section>
  );
}

const RUNGS = [
  {
    name: "Theorem 4.4",
    tex: String.raw`n\log n\,(3^o-2^L)\le L\,3^o`,
    lean: "cycleMin_finance",
    status: "Lean",
    note: "The surplus must be paid. Needs a floor to become a kill.",
  },
  {
    name: "Theorem 4.10",
    tex: String.raw`n\log n\cdot\min(\Lambda,1)\le 2L`,
    lean: "cycleMin_gap_transfer",
    status: "Lean",
    note: "The surplus becomes a linear form. Still floor-free.",
  },
  {
    name: "Corollary 4.11",
    tex: String.raw`L^{14.3}\le n\log n/915\ \Rightarrow\ \text{no cycle}`,
    lean: "Rhin 1987 as hypothesis",
    status: "human proof",
    note: "Short cycles die. Weaker than the table at every certified floor.",
  },
  {
    name: "Open",
    tex: String.raw`L>(n\log n/915)^{1/14.3}`,
    lean: "not claimed",
    status: "open",
    note: "The finance survivors live here. No halt theorem.",
  },
] as const;

export function GapHierarchy() {
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
