import type { ReactNode } from "react";
import { Metric } from "./Metric";
import { Tex } from "./Tex";
import { usePlayState } from "../context/PlayState";
import { formatGrouped } from "../juggler/format";
import {
  RECOVERIES,
  RUN_A_MAX,
  RUN_A_MIN,
  RUN_N_MAX,
  RUN_N_MIN,
  parseSuffix,
  runSuffixView,
  sharpExponents,
  type Recovery,
} from "../juggler/runSuffix";
import { RunSplitStrip } from "../visuals/RunSplitStrip";
import { RunSuffixCrossing } from "../visuals/RunSuffixCrossing";
import { RunSuffixHierarchy, RunSuffixTable } from "../visuals/RunSuffixTable";

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

type RunSuffixExplorerProps = {
  compact?: boolean;
};

export function RunSuffixExplorer({ compact = false }: RunSuffixExplorerProps) {
  const {
    suffix,
    setSuffix,
    runA,
    setRunA,
    runN,
    setRunN,
    envelopeMode,
    setEnvelopeMode,
  } = usePlayState();
  const parsed = parseSuffix(suffix);
  const view = parsed === null ? null : runSuffixView(parsed, runA, runN, envelopeMode);

  function loadRecovery(row: Recovery) {
    setSuffix(row.suffix);
    setRunA(row.lawA);
  }

  return (
    <div className="space-y-6">
      <Movement number={1} title="The split" question="where does the odd run meet the suffix?">
        <Tex display>{String.raw`w=v\,O^a\,u`}</Tex>
        {view ? <RunSplitStrip a={view.a} suffix={view.suffix} /> : null}
        <div className="flex flex-wrap items-end gap-3">
          <label className="text-sm text-muted">
            Suffix u
            <input
              className="ml-2 w-36 rounded border border-line bg-card px-2 py-1 font-mono uppercase"
              value={suffix}
              onChange={(event) => setSuffix(event.target.value.toUpperCase())}
              spellCheck={false}
            />
          </label>
          <label className="text-sm text-muted">
            Odd run a
            <input
              className="ml-2 w-20 rounded border border-line bg-card px-2 py-1 font-mono"
              type="number"
              min={RUN_A_MIN}
              max={RUN_A_MAX}
              value={runA}
              onChange={(event) => {
                const value = Number(event.target.value);
                if (Number.isInteger(value) && value >= RUN_A_MIN && value <= RUN_A_MAX) {
                  setRunA(value);
                }
              }}
            />
          </label>
        </div>
        <div className="flex flex-wrap gap-2">
          {RECOVERIES.map((row) => (
            <button
              key={row.suffix}
              type="button"
              className={`rounded-full px-3 py-1 font-mono text-sm ${
                parsed === row.suffix
                  ? "bg-deep text-card"
                  : "border border-line text-ink hover:bg-paper"
              }`}
              onClick={() => loadRecovery(row)}
            >
              {row.suffix}
            </button>
          ))}
        </div>
        {parsed === null ? (
          <p className="text-sm text-warn">
            Use only O and E, length at most 8, and start with E — or leave the
            field empty to see why the whole word is finance, not this law.
          </p>
        ) : view ? (
          <>
            <div className="grid gap-3 sm:grid-cols-2 lg:grid-cols-4">
              <Metric
                label="T(u) = 2^s / 3^ℓ"
                value={view.TLabel}
                hint={view.wholeWord ? "empty suffix: T = 1" : "backward exponent"}
              />
              <Metric
                label="(3/2)^a"
                value={formatPower(view.P)}
                hint={
                  view.leastA === null
                    ? "no crossing at this a-cap"
                    : `least a with (3/2)^a > T is ${view.leastA}`
                }
              />
              <Metric
                label="tail O^a u expanding?"
                value={view.tailExpanding ? "yes" : "no"}
                hint="3^{#O} vs 2^{length} on the tail"
              />
              <Metric
                label="margin θ = 1 − T/P"
                value={Number.isFinite(view.margin) ? view.margin.toFixed(3) : "—"}
                hint={`crude cost log 4 / log n = ${view.floorCost.toFixed(3)}`}
              />
            </div>
            <p className="text-sm text-muted">
              Theorem 3.2(i) forces the whole word to expand. The leading-order
              test (3/2)^a {">"} T(u) flags shapes that die once n is large
              enough; it does not assert that every proper tail is formally
              contracting. Movement 2 prices the constant.
            </p>
          </>
        ) : null}
      </Movement>

      <Movement number={2} title="The crossing" question="when do the two envelopes collide?">
        <div className="flex flex-wrap items-end gap-3">
          <label className="text-sm text-muted">
            Cycle minimum n
            <input
              className="ml-2 w-28 rounded border border-line bg-card px-2 py-1 font-mono"
              type="number"
              min={RUN_N_MIN}
              max={RUN_N_MAX}
              value={runN}
              onChange={(event) => {
                const value = Number(event.target.value);
                if (Number.isInteger(value) && value >= RUN_N_MIN && value <= RUN_N_MAX) {
                  setRunN(value);
                }
              }}
            />
          </label>
          <label className="min-w-[12rem] flex-1 text-sm text-muted">
            log n
            <input
              className="mt-1 w-full"
              style={{ accentColor: "#1f3d34" }}
              type="range"
              min={Math.log10(RUN_N_MIN)}
              max={Math.log10(RUN_N_MAX)}
              step={0.01}
              value={Math.log10(runN)}
              onChange={(event) => {
                setRunN(Math.max(RUN_N_MIN, Math.round(10 ** Number(event.target.value))));
              }}
            />
          </label>
          <div className="flex gap-2">
            <ModeButton
              active={envelopeMode === "crude"}
              onClick={() => setEnvelopeMode("crude")}
              label="crude"
              hint="Theorem 3.26"
            />
            <ModeButton
              active={envelopeMode === "sharp"}
              onClick={() => setEnvelopeMode("sharp")}
              label="sharp"
              hint="Theorem 3.29"
            />
          </div>
        </div>
        {view ? <RunSuffixCrossing view={view} compact={compact} /> : null}
        {view && !view.wholeWord ? (
          <div className="grid gap-3 sm:grid-cols-2 lg:grid-cols-4">
            <Metric
              label="law at this n"
              value={view.fires ? "fires" : "silent"}
              hint={view.mode === "crude" ? "4 (n/4)^P ≥ B(u)" : "n^{X_a} vs (n+1)^{Y_a} B^{2^a}"}
            />
            <Metric
              label="n_u crude"
              value={view.nCrude === null ? "never" : formatGrouped(view.nCrude)}
              hint="least n for Theorem 3.26"
            />
            <Metric
              label="n_u sharp"
              value={view.nSharp === null ? "never" : formatGrouped(view.nSharp)}
              hint="least n for Theorem 3.29"
            />
            <Metric
              label="X_a , Y_a"
              value={sharpPair(view.a)}
              hint="Lemma 3.28; a = 7 is 6177, 3990"
            />
          </div>
        ) : null}
        <RunSuffixHierarchy />
        <p className="text-sm text-muted">
          Theorem 3.31 is a computational strengthening once the cycle minimum
          is at least 300. The interactive CycleMin checker implements Theorem
          3.22: four evens, every n ≥ 2, Lean.
        </p>
      </Movement>

      <Movement number={3} title="The table" question="eleven statements, one inequality?">
        <RunSuffixTable
          selected={parsed ?? ""}
          onSelect={loadRecovery}
          compact={compact}
        />
        <p className="text-sm text-muted">
          Firing the law is not a cycle and not a halt theorem. Below n_u the
          law says nothing; those windows close by census in Appendix D. A
          leftover word such as O<sup>7</sup>EEEE inhabits CycleMin shape and
          still never returns.
        </p>
      </Movement>
    </div>
  );
}

function ModeButton({
  active,
  onClick,
  label,
  hint,
}: {
  active: boolean;
  onClick: () => void;
  label: string;
  hint: string;
}) {
  return (
    <button
      type="button"
      className={`rounded-full px-3 py-1 text-sm ${
        active ? "bg-deep text-card" : "border border-line text-ink hover:bg-paper"
      }`}
      onClick={onClick}
    >
      {label}
      <span className={`ml-1 text-xs ${active ? "text-card/70" : "text-muted"}`}>{hint}</span>
    </button>
  );
}

function formatPower(value: number): string {
  if (!Number.isFinite(value)) return "—";
  if (value >= 100) return value.toFixed(1);
  return value.toFixed(3);
}

function sharpPair(a: number): string {
  const [ex, wye] = sharpExponents(a);
  return `${ex.toLocaleString("en-US")}, ${wye.toLocaleString("en-US")}`;
}
