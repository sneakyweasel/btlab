import { Tex } from "../components/Tex";
import { formatGrouped } from "../juggler/format";
import {
  FAN_CHIPS,
  FAN_ROWS,
  type FanView,
  type FanWalkStatus,
} from "../juggler/fan";
import { WALK_FLOOR_COMPARISONS, type WalkFloorComparison } from "../juggler/walkCharge";

function sci(value: number): string {
  const exp = Math.floor(Math.log10(value));
  return `${(value / 10 ** exp).toFixed(2)}·10^${exp}`;
}

function statusTone(status: FanWalkStatus): string {
  if (status === "excluded") return "text-deep";
  if (status === "current") return "text-odd";
  return "text-muted";
}

type FanFloorChipsProps = {
  selectedK: number;
  onSelect: (row: WalkFloorComparison) => void;
};

export function FanFloorChips({ selectedK, onSelect }: FanFloorChipsProps) {
  return (
    <div className="flex flex-wrap gap-2">
      {WALK_FLOOR_COMPARISONS.map((row, index) => {
        const active = selectedK === index;
        return (
          <button
            key={row.name}
            type="button"
            className={`rounded-full px-3 py-1 text-sm ${
              active ? "bg-deep text-card" : "border border-line text-ink hover:bg-paper"
            }`}
            onClick={() => onSelect(row)}
          >
            {row.name}
          </button>
        );
      })}
    </div>
  );
}

type FanMemberTableProps = {
  view: FanView;
  onSelect: (k: number) => void;
};

export function FanMemberTable({ view, onSelect }: FanMemberTableProps) {
  const rows = FAN_CHIPS.map((k) => FAN_ROWS[k]).filter(Boolean);
  return (
    <div className="overflow-x-auto">
      <table className="w-full min-w-[32rem] text-left text-sm">
        <thead className="border-b border-line text-xs uppercase tracking-wide text-muted">
          <tr>
            <th className="py-2 pr-3 font-medium">k</th>
            <th className="py-2 pr-3 font-medium">L_k</th>
            <th className="py-2 pr-3 font-medium">Λ_k</th>
            <th className="py-2 pr-3 font-medium">finance n_max</th>
            <th className="py-2 font-medium">walk status</th>
          </tr>
        </thead>
        <tbody className="font-mono text-xs">
          {rows.map((row) => {
            const active = row.k === view.k;
            const status: FanWalkStatus =
              row.k < view.frontierK ? "excluded" : row.k === view.frontierK ? "current" : "open";
            return (
              <tr key={row.k} className="border-b border-line/50">
                <td className="py-1.5 pr-3">
                  <button
                    type="button"
                    className={`rounded-full px-2 py-0.5 ${
                      active ? "bg-deep text-card" : "border border-line text-ink hover:bg-paper"
                    }`}
                    onClick={() => onSelect(row.k)}
                  >
                    {row.k}
                  </button>
                </td>
                <td className="py-1.5 pr-3">{formatGrouped(row.L)}</td>
                <td className="py-1.5 pr-3">{row.lam.toExponential(3)}</td>
                <td className="py-1.5 pr-3">{sci(row.nmax)}</td>
                <td className={`py-1.5 font-sans ${statusTone(status)}`}>
                  {status === "excluded"
                    ? "excluded"
                    : status === "current"
                      ? "current frontier"
                      : "open"}
                </td>
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
    name: "Theorem 5.8",
    tex: String.raw`[50508,\,16785921)`,
    lean: "human proof",
    status: "human proof",
    note: "Census-free window: charge, not kill.",
  },
  {
    name: "Corollary 5.11",
    tex: String.raw`L\ge 780239`,
    lean: "printed bound",
    status: "computational",
    note: "Walk charge at N₀ = 3.5·10⁸.",
  },
  {
    name: "Proposition 5.12",
    tex: String.raw`L_k=176251+301994k`,
    lean: "FanLaw.lean",
    status: "Lean",
    note: "fanLambda_55_pos / fanLambda_56_neg.",
  },
  {
    name: "Open",
    tex: String.raw`N_0\sim 10^{12}`,
    lean: "not claimed",
    status: "open",
    note: "Fans recur. Not a halt theorem.",
  },
] as const;

export function FanHierarchy() {
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
