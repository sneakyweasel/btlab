import type { ReactNode } from "react";
import { Link } from "react-router-dom";
import { Metric } from "./Metric";
import { Tex } from "./Tex";
import { usePlayState } from "../context/PlayState";
import { formatGrouped } from "../juggler/format";
import {
  WALK_FLOOR_COMPARISONS,
  WALK_L_MAX,
  WALK_L_MIN,
  WALK_LENGTH_CHIPS,
  WALK_N_MAX,
  WALK_N_MIN,
  walkChargeView,
  type WalkFloorComparison,
} from "../juggler/walkCharge";
import { HugLetterStrip } from "../visuals/HugLetterStrip";
import { TransportShrink } from "../visuals/TransportShrink";
import { WalkFloorTable, WalkHierarchy } from "../visuals/WalkComparison";
import { WalkChargePipeline } from "../visuals/WalkChargePipeline";
import { WalkWindowLine } from "../visuals/WalkWindowLine";

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

type WalkChargeExplorerProps = {
  compact?: boolean;
};

export function WalkChargeExplorer({ compact = false }: WalkChargeExplorerProps) {
  const { walkN, setWalkN, walkL, setWalkL, walkO, setWalkO } = usePlayState();
  const view = walkChargeView(walkN, walkL, walkO);

  function loadFloor(row: WalkFloorComparison) {
    setWalkN(row.n0);
    setWalkL(row.printedL);
    setWalkO(null);
  }

  return (
    <div className="space-y-6">
      <Movement number={1} title="Transport" question="how do the crumbs become one number?">
        <Tex display>
          {String.raw`D=\frac{1.05\,e}{n}+\frac{0.7\,o}{n^{3/2}},\qquad n'=ne^{-D}.`}
        </Tex>
        <div className="flex flex-wrap items-end gap-3">
          <label className="text-sm text-muted">
            Cycle minimum n
            <input
              className="ml-2 w-36 rounded border border-line bg-card px-2 py-1 font-mono"
              type="number"
              min={WALK_N_MIN}
              max={WALK_N_MAX}
              value={walkN}
              onChange={(event) => {
                const value = Number(event.target.value);
                if (Number.isInteger(value) && value >= WALK_N_MIN && value <= WALK_N_MAX) {
                  setWalkN(value);
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
              min={Math.log10(WALK_N_MIN)}
              max={Math.log10(WALK_N_MAX)}
              step={0.01}
              value={Math.log10(walkN)}
              onChange={(event) => {
                setWalkN(
                  Math.max(WALK_N_MIN, Math.min(WALK_N_MAX, Math.round(10 ** Number(event.target.value)))),
                );
              }}
            />
          </label>
        </div>
        <div className="flex flex-wrap items-end gap-3">
          <label className="text-sm text-muted">
            Period L
            <input
              className="ml-2 w-28 rounded border border-line bg-card px-2 py-1 font-mono"
              type="number"
              min={WALK_L_MIN}
              max={WALK_L_MAX}
              value={walkL}
              onChange={(event) => {
                const value = Number(event.target.value);
                if (Number.isInteger(value) && value >= WALK_L_MIN && value <= WALK_L_MAX) {
                  setWalkL(value);
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
              max={WALK_L_MAX}
              placeholder={String(view.o)}
              value={walkO ?? ""}
              onChange={(event) => {
                const raw = event.target.value.trim();
                if (!raw) {
                  setWalkO(null);
                  return;
                }
                const value = Number(raw);
                if (Number.isInteger(value) && value >= 1 && value <= WALK_L_MAX) {
                  setWalkO(value);
                }
              }}
            />
          </label>
          <span className="text-xs text-muted">
            {view.oIsDefault ? "o_min(L)" : "custom o"}
          </span>
        </div>
        <div className="flex flex-wrap gap-2">
          {WALK_LENGTH_CHIPS.map((length) => (
            <button
              key={length}
              type="button"
              className={`rounded-full px-3 py-1 font-mono text-sm ${
                walkL === length ? "bg-deep text-card" : "border border-line text-ink hover:bg-paper"
              }`}
              onClick={() => {
                setWalkL(length);
                setWalkO(null);
              }}
            >
              {formatGrouped(length)}
            </button>
          ))}
        </div>
        <TransportShrink view={view} />
        <div className="grid gap-3 sm:grid-cols-2 lg:grid-cols-4">
          <Metric label="e = L − o" value={formatGrouped(view.e)} hint="even letters" />
          <Metric
            label="D"
            value={formatSmall(view.D)}
            hint="at the laboratory floor a window length has D ≤ 4.6·10⁻³"
          />
          <Metric label="n′" value={formatSci(view.nPrime)} hint="reduced base" />
          <Metric label="ln n′" value={formatSmall(view.lnNPrime)} hint="finance currency" />
        </div>
        <p className="text-sm text-muted">
          Finance at the reduced base. Lean name{" "}
          <code className="font-mono text-[0.92em] text-deep">cycleMin_transport</code>.
          Hypothesis n ≥ 400.
        </p>
      </Movement>

      <Movement number={2} title="The adversary" question="which word is worst?">
        <Tex display>{String.raw`u=(1+\mu)a-k,\qquad \mu=\log_2(3/2)`}</Tex>
        <p className="text-sm text-muted">
          Take E where u ≥ 1 and an even remains; otherwise O. Height after each
          letter; no charge integral.
        </p>
        <HugLetterStrip word={view.hug?.word ?? null} />
        <div className="grid gap-3 sm:grid-cols-2 lg:grid-cols-4">
          <Metric
            label="prefix-minimal"
            value={view.prefixMinimal ? "yes" : "—"}
            hint={view.prefixMinimal ? "E at the first legal time" : "word not shipped"}
          />
          <Metric
            label="Lean"
            value="hug_charge_maximal"
            hint="budgetedWord_eq_hugWord"
          />
          <Metric
            label="shipped words"
            value="(11, 7) · (19, 12)"
            hint="hardcoded hug_word pairs"
          />
          <Metric
            label="this (L, o)"
            value={view.hug ? `${view.L}, ${view.o}` : "not shipped"}
            hint={view.oIsDefault ? "o_min" : "custom"}
          />
        </div>
        <p className="text-sm text-muted">
          A picture of Theorem 5.4, not a calculator. The site does not recompute
          hug charge.
        </p>
      </Movement>

      <Movement number={3} title="Charge versus kill" question="why is the window census-free if the bound is not?">
        <WalkChargePipeline />
        <WalkWindowLine selectedL={view.L} compact={compact} />
        <WalkFloorTable selectedN={nearestFloor(walkN)} onSelect={loadFloor} />
        <WalkHierarchy />
        <p className="text-sm text-muted">
          Theorem 5.7 is the Ostrowski / Denjoy–Koksma envelope
          |C_L − C_*| ≤ 2s(L)/L. Theorem 5.8 bounds the charge, not the kill;
          780,239 still survives. Exhausting the fan is a 10¹²-scale floor, not
          a halt theorem. The staircase lives on{" "}
          <Link to="/play/fan">the Fan tab</Link>.
        </p>
      </Movement>
    </div>
  );
}

function nearestFloor(n: number): number {
  let best = WALK_FLOOR_COMPARISONS[0].n0;
  for (const row of WALK_FLOOR_COMPARISONS) {
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

function formatSci(value: number): string {
  if (!Number.isFinite(value)) return "—";
  if (value >= 1e7 || (value > 0 && value < 0.01)) return value.toExponential(3);
  return value.toFixed(2);
}
