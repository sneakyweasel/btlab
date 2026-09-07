import type { ReactNode } from "react";
import { Metric } from "./Metric";
import { ProseInline } from "./Prose";
import { Tex } from "./Tex";
import { usePlayState } from "../context/PlayState";
import { formatGrouped } from "../juggler/format";
import {
  FLOOR_COMPARISONS,
  GAP_L_MAX,
  GAP_L_MIN,
  GAP_LENGTH_CHIPS,
  GAP_N_MAX,
  GAP_N_MIN,
  gapTransferView,
  type FloorComparison,
  type GapCase,
} from "../juggler/gapTransfer";
import { GapBalance } from "../visuals/GapBalance";
import { GapFloorTable, GapHierarchy, SurvivorExponentTable } from "../visuals/GapComparison";
import { GapPlane } from "../visuals/GapPlane";

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

const CASE_LABEL: Record<GapCase, string> = {
  nonpositive: "Λ ≤ 0",
  large: "A ≥ 2B",
  thin: "B < A < 2B",
};

const CASE_HINT: Record<GapCase, string> = {
  nonpositive: "contracting: the left side is nonpositive",
  large: "Λ ≥ log 2, so min(Λ, 1) ≤ P ≤ 2L",
  thin: "Λ ≤ (A−B)/B, and A/B < 2",
};

type GapTransferExplorerProps = {
  compact?: boolean;
};

export function GapTransferExplorer({ compact = false }: GapTransferExplorerProps) {
  const { gapN, setGapN, gapL, setGapL, gapO, setGapO } = usePlayState();
  const view = gapTransferView(gapN, gapL, gapO);

  function loadFloor(row: FloorComparison) {
    setGapN(row.n0);
    setGapL(row.printedL);
    setGapO(null);
  }

  return (
    <div className="space-y-6">
      <Movement number={1} title="The linear form" question="how does the surplus become a bound on n?">
        <Tex display>{String.raw`\Lambda=o\log 3-L\log 2=-\log(1-\theta)\qquad n\log n\cdot\min(\Lambda,1)\le 2L`}</Tex>
        <div className="flex flex-wrap items-end gap-3">
          <label className="text-sm text-muted">
            Period L
            <input
              className="ml-2 w-28 rounded border border-line bg-card px-2 py-1 font-mono"
              type="number"
              min={GAP_L_MIN}
              max={GAP_L_MAX}
              value={gapL}
              onChange={(event) => {
                const value = Number(event.target.value);
                if (Number.isInteger(value) && value >= GAP_L_MIN && value <= GAP_L_MAX) {
                  setGapL(value);
                }
              }}
            />
          </label>
          <label className="text-sm text-muted">
            Odd count o
            <input
              className="ml-2 w-24 rounded border border-line bg-card px-2 py-1 font-mono"
              type="number"
              min={1}
              max={GAP_L_MAX}
              placeholder={String(view.o)}
              value={gapO ?? ""}
              onChange={(event) => {
                const raw = event.target.value.trim();
                if (!raw) {
                  setGapO(null);
                  return;
                }
                const value = Number(raw);
                if (Number.isInteger(value) && value >= 1 && value <= GAP_L_MAX) {
                  setGapO(value);
                }
              }}
            />
          </label>
          <span className="text-xs text-muted">
            {view.oIsDefault ? "o_min(L)" : "custom o"}
          </span>
        </div>
        <div className="flex flex-wrap gap-2">
          {GAP_LENGTH_CHIPS.map((length) => (
            <button
              key={length}
              type="button"
              className={`rounded-full px-3 py-1 font-mono text-sm ${
                gapL === length ? "bg-deep text-card" : "border border-line text-ink hover:bg-paper"
              }`}
              onClick={() => {
                setGapL(length);
                setGapO(null);
              }}
            >
              {formatGrouped(length)}
            </button>
          ))}
        </div>
        <div className="flex flex-wrap gap-2">
          {(["nonpositive", "large", "thin"] as const).map((kind) => (
            <span
              key={kind}
              className={`rounded-full px-3 py-1 text-sm ${
                view.caseKind === kind ? "bg-deep text-card" : "border border-line text-muted"
              }`}
            >
              {CASE_LABEL[kind]}
              {view.caseKind === kind ? (
                <span className="ml-1 text-xs text-card/70">{CASE_HINT[kind]}</span>
              ) : null}
            </span>
          ))}
        </div>
        <GapBalance view={view} />
        <div className="grid gap-3 sm:grid-cols-2 lg:grid-cols-4">
          <Metric
            label="θ = 1 − 2^L / 3^o"
            value={formatSmall(view.theta)}
            hint={view.expanding ? "formally expanding" : "contracting — not a cycle"}
          />
          <Metric label="Λ" value={formatSmall(view.lambda)} hint="o log 3 − L log 2" />
          <Metric
            label="min(Λ, 1)"
            value={formatSmall(view.minLambda)}
            hint="the factor Theorem 4.10 carries"
          />
          <Metric
            label="formally expanding"
            value={view.expanding ? "yes" : "no"}
            hint={view.holds ? "n log n · min(Λ, 1) ≤ 2L holds" : "the transfer fails — not a cycle minimum"}
          />
        </div>
        <p className="text-sm text-muted">
          <ProseInline text="The only new input is $\\log\\frac{1}{1-\\theta}\\le\\frac{\\theta}{1-\\theta}$. Lean name `cycleMin_gap_transfer`. A contracting pair is not a cycle; the inequality is then free." />
        </p>
      </Movement>

      <Movement number={2} title="The plane" question="which (n, L) are short?">
        <div className="flex flex-wrap items-end gap-3">
          <label className="text-sm text-muted">
            Cycle minimum n
            <input
              className="ml-2 w-36 rounded border border-line bg-card px-2 py-1 font-mono"
              type="number"
              min={GAP_N_MIN}
              max={GAP_N_MAX}
              value={gapN}
              onChange={(event) => {
                const value = Number(event.target.value);
                if (Number.isInteger(value) && value >= GAP_N_MIN && value <= GAP_N_MAX) {
                  setGapN(value);
                }
              }}
            />
          </label>
          <label className="min-w-48 flex-1 text-sm text-muted">
            log n
            <input
              className="mt-1 w-full"
              style={{ accentColor: "#1f3d34" }}
              type="range"
              min={Math.log10(GAP_N_MIN)}
              max={Math.log10(GAP_N_MAX)}
              step={0.01}
              value={Math.log10(gapN)}
              onChange={(event) => {
                setGapN(Math.max(GAP_N_MIN, Math.round(10 ** Number(event.target.value))));
              }}
            />
          </label>
        </div>
        <GapPlane
          view={view}
          compact={compact}
          onSelectPoint={(point) => {
            setGapL(point.L);
            setGapO(null);
          }}
        />
        <div className="grid gap-3 sm:grid-cols-2 lg:grid-cols-4">
          <Metric
            label="Rhin lower bound on L"
            value={`≥ ${view.rhinL}`}
            hint="least L > (n log n / 915)^{1/14.3}"
          />
          <Metric
            label="this L"
            value={view.short ? "short" : "long"}
            hint={view.short ? "excluded for every n ≥ 2" : "the open regime"}
          />
          <Metric
            label="at N₀ = 3.5·10⁸"
            value="L ≥ 4"
            hint="toothless next to Corollary 5.11"
          />
          <Metric
            label="o used"
            value={formatGrouped(view.o)}
            hint={view.oIsDefault ? "o_min" : "custom"}
          />
        </div>
      </Movement>

      <Movement number={3} title="The comparison" question="why is the reduction toothless at floors?">
        <GapFloorTable selectedN={nearestFloor(gapN)} onSelect={loadFloor} />
        {compact ? null : <SurvivorExponentTable />}
        <GapHierarchy />
        <p className="text-sm text-muted">
          Corollary 4.11 is a floor-free reduction, not a kill. It is weaker
          than the finance table at every certified floor and does not kill
          the long survivors. Baker/Rhin as a leftover killer is closed. The
          no-cycle problem is exactly the exclusion of long cycles.
        </p>
      </Movement>
    </div>
  );
}

function nearestFloor(n: number): number {
  let best = FLOOR_COMPARISONS[0].n0;
  for (const row of FLOOR_COMPARISONS) {
    if (Math.abs(row.n0 - n) < Math.abs(best - n)) best = row.n0;
  }
  return best;
}

function formatSmall(value: number): string {
  if (!Number.isFinite(value)) return "—";
  const abs = Math.abs(value);
  if (abs !== 0 && (abs < 1e-3 || abs >= 1e4)) return value.toExponential(3);
  return value.toFixed(4);
}
