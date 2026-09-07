import { PAPER_FLOOR } from "../juggler/constants";
import { formatGrouped } from "../juggler/format";
import {
  backwardLn,
  excludedCrude,
  excludedSharp,
  forwardBoundLn,
  sharpExponents,
  type RunSuffixView,
} from "../juggler/runSuffix";

const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const INK = "#1d1914";
const MUTED = "#5e574c";
const DEEP = "#1f3d34";
const OK = "#2d6a4f";

const WIDTH = 640;
const LEFT = 64;
const RIGHT = 596;

function finiteTicks(lo: number, hi: number, stride: number, cap = 48): number[] {
  if (!Number.isFinite(lo) || !Number.isFinite(hi) || !Number.isFinite(stride) || stride <= 0) {
    return [];
  }
  const out: number[] = [];
  for (let exp = Math.ceil(lo); exp <= Math.floor(hi) && out.length < cap; exp += stride) {
    out.push(exp);
  }
  return out;
}

function TenPow({ exp }: { exp: number }) {
  return (
    <>
      10
      <tspan dy="-4" fontSize="7">
        {Math.round(exp)}
      </tspan>
    </>
  );
}

function sampleN(log10n: number): number {
  return Math.max(2, Math.round(10 ** log10n));
}

function crudeLogs(n: number, a: number, suffix: string): { fwd: number; back: number } {
  return {
    fwd: forwardBoundLn(n, a) / Math.LN10,
    back: backwardLn(suffix, n) / Math.LN10,
  };
}

function sharpLogs(n: number, a: number, suffix: string): { fwd: number; back: number } {
  const [ex, wye] = sharpExponents(a);
  return {
    fwd: (ex * Math.log(n)) / Math.LN10,
    back: (wye * Math.log(n + 1) + 2 ** a * backwardLn(suffix, n)) / Math.LN10,
  };
}

type RunSuffixCrossingProps = {
  view: RunSuffixView;
  compact?: boolean;
};

/**
 * Theorem 3.26 / 3.29 as a crossing. x is the cycle minimum; y is log10 of
 * the two sides. Right of n_u the law fires.
 */
export function RunSuffixCrossing({ view, compact = false }: RunSuffixCrossingProps) {
  if (view.wholeWord) {
    return (
      <p className="rounded-xl border border-line bg-paper/60 px-3 py-3 text-sm text-muted">
        An empty suffix is the whole word as a tail. Remark 3.32: the backward
        envelope then sits at n itself and the law degenerates to the finance
        inequality of Theorem 4.4. That is a different picture, on the finance
        page.
      </p>
    );
  }

  const height = compact ? 230 : 290;
  const top = 26;
  const bottom = compact ? 176 : 236;
  const logs = view.mode === "crude" ? crudeLogs : sharpLogs;
  const threshold = view.nThreshold;
  const never = threshold === null && view.P <= view.T + 1e-15;

  const xLo = 0.3;
  const rawXHi =
    Math.max(
      threshold === null ? 0 : Math.log10(threshold),
      Math.log10(PAPER_FLOOR),
      Math.log10(view.n),
    ) + 0.6;
  const xHi = Number.isFinite(rawXHi) ? Math.min(Math.max(rawXHi, 3.2), 12) : 7;

  const probe: number[] = [];
  for (let index = 0; index <= 80; index += 1) {
    const n = sampleN(xLo + ((xHi - xLo) * index) / 80);
    const pair = logs(n, view.a, view.suffix);
    if (Number.isFinite(pair.fwd)) probe.push(pair.fwd);
    if (Number.isFinite(pair.back)) probe.push(pair.back);
  }
  const yMin = Math.min(...probe);
  const yMax = Math.max(...probe);
  const pad = Math.max(0.35, (yMax - yMin) * 0.12);
  const yLo = yMin - pad;
  const yHi = yMax + pad;

  const xOf = (log10n: number) => LEFT + ((log10n - xLo) / (xHi - xLo)) * (RIGHT - LEFT);
  const yOf = (log10v: number) => bottom - ((log10v - yLo) / (yHi - yLo)) * (bottom - top);

  const fwdParts: string[] = [];
  const backParts: string[] = [];
  for (let index = 0; index <= 80; index += 1) {
    const log10n = xLo + ((xHi - xLo) * index) / 80;
    const pair = logs(sampleN(log10n), view.a, view.suffix);
    const x = xOf(log10n).toFixed(1);
    fwdParts.push(`${index === 0 ? "M" : "L"}${x},${yOf(pair.fwd).toFixed(1)}`);
    backParts.push(`${index === 0 ? "M" : "L"}${x},${yOf(pair.back).toFixed(1)}`);
  }

  const xCross = threshold === null ? null : xOf(Math.log10(threshold));
  const xFloor = xOf(Math.log10(PAPER_FLOOR));
  const xNow = xOf(Math.log10(view.n));
  const firesNow =
    view.mode === "crude"
      ? excludedCrude(view.a, view.suffix, view.n)
      : excludedSharp(view.a, view.suffix, view.n);

  const xTicks = finiteTicks(xLo, xHi, xHi - xLo > 8 ? 2 : 1);
  const yStride = yHi - yLo > 12 ? 3 : yHi - yLo > 6 ? 2 : 1;
  const yTicks = finiteTicks(yLo, yHi, yStride);

  const fwdLabel =
    view.mode === "crude" ? "forward 4 (n/4)^{(3/2)^a} — Lemma 3.24" : "n^{X_a} — Lemma 3.28";
  const backLabel =
    view.mode === "crude" ? "backward B(u) — Lemma 3.25" : "(n+1)^{Y_a} B(u)^{2^a} — Theorem 3.29";

  return (
    <div className="space-y-3">
      <svg viewBox={`0 0 ${WIDTH} ${height}`} role="img" className="h-auto w-full">
        <title>Run-suffix envelopes against the cycle minimum</title>
        {yTicks.map((exp) => (
          <g key={`y${exp}`}>
            <line x1={LEFT} y1={yOf(exp)} x2={RIGHT} y2={yOf(exp)} stroke="#e8e2d4" strokeWidth="0.75" />
            <text
              x={LEFT - 8}
              y={yOf(exp) + 3}
              textAnchor="end"
              fill={MUTED}
              fontFamily="IBM Plex Mono, monospace"
              fontSize="10"
            >
              <TenPow exp={exp} />
            </text>
          </g>
        ))}
        {xTicks.map((exp) => (
          <text
            key={`x${exp}`}
            x={xOf(exp)}
            y={bottom + 16}
            textAnchor="middle"
            fill={MUTED}
            fontFamily="IBM Plex Mono, monospace"
            fontSize="10"
          >
            <TenPow exp={exp} />
          </text>
        ))}
        <text x={RIGHT} y={bottom + 32} textAnchor="end" fill={MUTED} fontSize="11">
          cycle minimum n
        </text>

        {xCross !== null ? (
          <rect
            x={Math.min(xCross, RIGHT)}
            y={top}
            width={Math.max(0, RIGHT - Math.min(xCross, RIGHT))}
            height={bottom - top}
            fill={OK}
            opacity="0.07"
          />
        ) : null}

        <line x1={LEFT} y1={top} x2={LEFT} y2={bottom} stroke="#d4cbb8" />
        <line x1={LEFT} y1={bottom} x2={RIGHT} y2={bottom} stroke="#d4cbb8" />

        <path d={fwdParts.join(" ")} fill="none" stroke={ODD} strokeWidth="2.5" />
        <path d={backParts.join(" ")} fill="none" stroke={EVEN} strokeWidth="2.5" />

        <text x={LEFT + 8} y={top + 14} fill={ODD} fontSize="11" fontFamily="Source Sans 3, sans-serif">
          {fwdLabel}
        </text>
        <text x={LEFT + 8} y={top + 28} fill={EVEN} fontSize="11" fontFamily="Source Sans 3, sans-serif">
          {backLabel}
        </text>

        <line x1={xFloor} y1={top} x2={xFloor} y2={bottom} stroke={INK} strokeWidth="1.2" strokeDasharray="4 3" />
        <text x={xFloor} y={top - 8} textAnchor="middle" fill={INK} fontSize="11">
          N₀ = 10⁶
        </text>

        <line
          x1={xNow}
          y1={top}
          x2={xNow}
          y2={bottom}
          stroke={DEEP}
          strokeWidth="1.2"
          strokeDasharray="2 3"
        />

        {xCross !== null ? (
          <>
            <circle cx={Math.min(xCross, RIGHT)} cy={yOf(logs(threshold!, view.a, view.suffix).fwd)} r="5" fill="#fffdf7" stroke={INK} strokeWidth="1.6" />
            <text
              x={Math.min(xCross, RIGHT - 28)}
              y={yOf(logs(threshold!, view.a, view.suffix).fwd) - 12}
              textAnchor="middle"
              fill={INK}
              fontSize="10"
              fontFamily="Source Sans 3, sans-serif"
            >
              n_u = {formatGrouped(threshold!)}
            </text>
          </>
        ) : null}

        <text x={LEFT} y={height - 6} fill={MUTED} fontSize="11">
          {never
            ? "(3/2)^a does not beat T(u): the envelopes never cross"
            : firesNow
              ? "at this n the forward bound is already above B(u): the law fires"
              : "left of n_u the law is silent; Appendix D closes those windows by census"}
        </text>
        <text x={RIGHT} y={height - 6} textAnchor="end" fill={firesNow ? OK : MUTED} fontSize="11">
          {view.mode === "crude" ? "Theorem 3.26" : "Theorem 3.29"}
        </text>
      </svg>
    </div>
  );
}
