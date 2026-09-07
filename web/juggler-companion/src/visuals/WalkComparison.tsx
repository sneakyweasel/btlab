import { Tex } from "../components/Tex";
import { formatGrouped } from "../juggler/format";
import {
  WALK_FLOOR_COMPARISONS,
  type WalkFloorComparison,
} from "../juggler/walkCharge";

type WalkFloorTableProps = {
  selectedN: number;
  onSelect: (row: WalkFloorComparison) => void;
};

export function WalkFloorTable({ selectedN, onSelect }: WalkFloorTableProps) {
  return (
    <div className="overflow-x-auto">
      <table className="w-full min-w-[32rem] text-left text-sm">
        <thead className="border-b border-line text-xs uppercase tracking-wide text-muted">
          <tr>
            <th className="py-2 pr-3 font-medium">floor</th>
            <th className="py-2 pr-3 font-medium">N₀</th>
            <th className="py-2 pr-3 font-medium">printed L</th>
            <th className="py-2 font-medium">source</th>
          </tr>
        </thead>
        <tbody className="font-mono text-xs">
          {WALK_FLOOR_COMPARISONS.map((row) => {
            const active = row.n0 === selectedN;
            const main = row.name === "Corollary 5.11";
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
                <td className="py-1.5 pr-3">
                  {formatGrouped(row.n0)}
                  {main ? <span className="ml-1 font-sans text-muted">main</span> : null}
                </td>
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

const RUNGS = [
  {
    name: "Theorem 5.3",
    tex: String.raw`D=\frac{1.05\,e}{n}+\frac{0.7\,o}{n^{3/2}}`,
    lean: "cycleMin_transport",
    status: "Lean",
    note: "Transport. Finance then runs at the reduced base n′.",
  },
  {
    name: "Theorem 5.4",
    tex: String.raw`\text{hug: }E\text{ iff }u\ge 1`,
    lean: "hug_charge_maximal",
    status: "Lean",
    note: "The worst word. budgetedWord_eq_hugWord.",
  },
  {
    name: "Theorem 5.8",
    tex: String.raw`[50508,\,16785921)`,
    lean: "human proof",
    status: "human proof",
    note: "Census-free window: charge, not kill.",
  },
  {
    name: "Open",
    tex: String.raw`\text{fan exhaustion}`,
    lean: "not claimed",
    status: "open",
    note: "A 10¹²-scale floor. Not a halt theorem.",
  },
] as const;

export function WalkHierarchy() {
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
