import type { ReactNode } from "react";
import { Link } from "react-router-dom";
import { Metric } from "./Metric";
import { Tex } from "./Tex";
import { usePlayState } from "../context/PlayState";
import { formatGrouped } from "../juggler/format";
import {
  FAN_CHIPS,
  FAN_EXHAUST_NMAX,
  FAN_K_MAX,
  FAN_K_MIN,
  FAN_Q14_NMAX,
  fanView,
  printedWalkK,
  walkChargeFactor,
} from "../juggler/fan";
import { MAIN_FLOOR } from "../juggler/constants";
import type { WalkFloorComparison } from "../juggler/walkCharge";
import { FanFloorChips, FanHierarchy, FanMemberTable } from "../visuals/FanComparison";
import { FanLambda, FanStaircase, statusLabel } from "../visuals/FanStaircase";

function Movement({
  number,
  title,
  question,
  children,
}: {
  number: number;
  title: string;
  question: string;
  children: ReactNode;
}) {
  return (
    <section className="space-y-4 rounded-2xl border border-line bg-card p-4 sm:p-5">
      <header className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
        <span className="font-mono text-xs uppercase tracking-[0.18em] text-muted">
          Movement {number}
        </span>
        <h2 className="font-serif text-2xl">{title}</h2>
        <span className="text-sm text-muted">{question}</span>
      </header>
      {children}
    </section>
  );
}

type FanExplorerProps = {
  compact?: boolean;
};

export function FanExplorer({ compact = false }: FanExplorerProps) {
  const { fanK, setFanK } = usePlayState();
  const view = fanView(fanK) ?? fanView(2);
  if (view === null) return null;
  const factor = walkChargeFactor(MAIN_FLOOR);

  function loadFloor(row: WalkFloorComparison) {
    const next = printedWalkK(row.n0);
    if (next !== null) setFanK(next);
  }

  return (
    <div className="space-y-6">
      <Movement number={1} title="The progression" question="why is the leftover one arithmetic progression?">
        <Tex display>
          {String.raw`L_k=176251+301994k,\qquad o_k=111202+190537k,\qquad 0\le k\le 55.`}
        </Tex>
        <div className="flex flex-wrap items-end gap-3">
          <label className="text-sm text-muted">
            Index k
            <input
              className="ml-2 w-20 rounded border border-line bg-card px-2 py-1 font-mono"
              type="number"
              min={FAN_K_MIN}
              max={FAN_K_MAX}
              value={view.k}
              onChange={(event) => {
                const value = Number(event.target.value);
                if (Number.isInteger(value) && value >= FAN_K_MIN && value <= FAN_K_MAX) {
                  setFanK(value);
                }
              }}
            />
          </label>
        </div>
        <div className="flex flex-wrap gap-2">
          {FAN_CHIPS.map((k) => (
            <button
              key={k}
              type="button"
              className={`rounded-full px-3 py-1 font-mono text-sm ${
                view.k === k ? "bg-deep text-card" : "border border-line text-ink hover:bg-paper"
              }`}
              onClick={() => setFanK(k)}
            >
              {k}
            </button>
          ))}
        </div>
        <FanLambda selectedK={view.k} onSelect={setFanK} compact={compact} />
        <div className="grid gap-3 sm:grid-cols-2 lg:grid-cols-4">
          <Metric label="k" value={String(view.k)} hint="0 … 55" />
          <Metric label="L_k" value={formatGrouped(view.L)} hint="q₁₂ + k q₁₃" />
          <Metric label="o_k" value={formatGrouped(view.o)} hint="p₁₂ + k p₁₃ = o_min" />
          <Metric label="Λ_k" value={view.lam.toExponential(3)} hint="affine in k" />
        </div>
        <p className="text-sm text-muted">
          Λ is affine, so the last positive index is k = 55 because Λ₀/|Λ′| =
          55.81. L₅₅ = 16,785,921 = q₁₄. Lean{" "}
          <code className="font-mono text-[0.92em] text-deep">fanLambda_55_pos</code>
          {" / "}
          <code className="font-mono text-[0.92em] text-deep">fanLambda_56_neg</code>,{" "}
          <code className="font-mono text-[0.92em] text-deep">FanLaw.lean</code>.
        </p>
      </Movement>

      <Movement number={2} title="The price" question="what does the next step cost?">
        <FanFloorChips selectedK={view.k} onSelect={loadFloor} />
        <FanStaircase
          selectedK={view.k}
          frontierK={view.frontierK}
          onSelect={setFanK}
          compact={compact}
        />
        {compact ? null : <FanMemberTable view={view} onSelect={setFanK} />}
        <div className="grid gap-3 sm:grid-cols-2 lg:grid-cols-3">
          <Metric
            label="finance n_max"
            value={formatSci(view.nmax)}
            hint="shipped; finance alone"
          />
          <Metric
            label="walk status"
            value={statusLabel(view.status)}
            hint={view.financePassed ? "finance has also passed it" : "finance has not passed it"}
          />
          <Metric
            label="walk-charge factor"
            value={factor.toFixed(1)}
            hint="n_max(L_1) / 3.5·10⁸ at the present frontier"
          />
        </div>
      </Movement>

      <Movement number={3} title="What it does not buy" question="why can this never become a halt theorem?">
        <FanHierarchy />
        <p className="text-sm text-muted">
          Finance n_max at L₅₄ is {formatSci(FAN_EXHAUST_NMAX)}; the last member
          L₅₅ = q₁₄ needs {formatSci(FAN_Q14_NMAX)}. Corollary 5.14 is conditional
          on a floor nobody has certified. The mechanism is on{" "}
          <Link to="/play/walk">Walk charge</Link>; the method ceiling is on{" "}
          <Link to="/play/ceiling">Ceiling</Link>.
        </p>
        {compact ? null : (
          <p className="text-sm text-muted">
            The fans recur at every convergent and the required floor grows
            quadratically in the length, so a period bound obtained this way can
            never become a proof that no cycle exists. That gap is not
            computational.
          </p>
        )}
      </Movement>
    </div>
  );
}

function formatSci(value: number): string {
  if (!Number.isFinite(value) || value <= 0) return "—";
  const exp = Math.floor(Math.log10(value));
  return `${(value / 10 ** exp).toFixed(2)}·10^${exp}`;
}
