import { Tex } from "../components/Tex";
import { LIVE_FINANCE_L_MAX, PAPER_FLOOR } from "../juggler/constants";
import { financeView, resolveLedger, shippedNMax } from "../juggler/finance";
import { formatGrouped } from "../juggler/format";
import { oMinForLength } from "../juggler/itinerary";
import { financeBudgetConstantOne } from "../juggler/necklace";

const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const INK = "#1d1914";
const MUTED = "#5e574c";
const DEEP = "#1f3d34";
const OK = "#2d6a4f";

const WIDTH = 640;
const HEIGHT = 290;
const LEFT = 64;
const RIGHT = 596;
const TOP = 26;
const BOTTOM = 236;

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

type FinanceBalanceProps = {
  length: number;
  /** Hide the metrics row for a tour-sized figure. */
  compact?: boolean;
};

/**
 * Theorem 4.4 as a balance. Through LIVE_FINANCE_L_MAX the surplus is
 * exact in the browser. Larger lengths look up finance.json. The budget
 * curve is L/(n ln n) in ordinary floats. n_max is always shipped.
 */
export function FinanceBalance({ length, compact = false }: FinanceBalanceProps) {
  const ledger = resolveLedger(length);
  const o = ledger?.o ?? financeView(length).oMin ?? oMinForLength(length) ?? 1;
  const ready = ledger !== null;
  const theta = ledger?.theta ?? Math.max(1e-18, -Math.expm1(length * Math.LN2 - o * Math.log(3)));
  const crossing = ledger?.crossing ?? Number.NaN;
  const nMax = shippedNMax(length);
  const sourceLabel = ledger?.source === "live" ? "live" : ledger?.source === "shipped" ? "shipped" : "preset only";

  const xLo = 0.3;
  const rawXHi =
    Math.max(
      Number.isFinite(crossing) ? Math.log10(crossing) : 0,
      Math.log10(PAPER_FLOOR),
      nMax === null ? 0 : Math.log10(nMax),
    ) + 0.6;
  const xHi = Number.isFinite(rawXHi) ? Math.min(rawXHi, 40) : 8;
  const budgetAtLeft = financeBudgetConstantOne(length, 10 ** xLo);
  const yHi = Math.log10(Math.max(budgetAtLeft, theta * 10));
  const yLo = Math.log10(theta) - 1.2;

  const xOf = (log10n: number) => LEFT + ((log10n - xLo) / (xHi - xLo)) * (RIGHT - LEFT);
  const yOf = (log10v: number) => BOTTOM - ((log10v - yLo) / (yHi - yLo)) * (BOTTOM - TOP);

  const budgetParts: string[] = [];
  for (let index = 0; index <= 120; index += 1) {
    const log10n = xLo + ((xHi - xLo) * index) / 120;
    const value = financeBudgetConstantOne(length, 10 ** log10n);
    const y = Math.max(TOP, Math.min(BOTTOM, yOf(Math.log10(value))));
    budgetParts.push(`${index === 0 ? "M" : "L"}${xOf(log10n).toFixed(1)},${y.toFixed(1)}`);
  }
  const budgetPath = budgetParts.join(" ");

  const yTheta = yOf(Math.log10(theta));
  const xCross = Number.isFinite(crossing) ? xOf(Math.log10(crossing)) : RIGHT;
  const xFloor = xOf(Math.log10(PAPER_FLOOR));
  const xNMax = nMax === null ? null : xOf(Math.log10(nMax));
  const dead = nMax !== null && nMax <= PAPER_FLOOR;

  const xTicks = finiteTicks(xLo, xHi, xHi - xLo > 12 ? 2 : 1);
  const yStride = !Number.isFinite(yHi - yLo) ? 1 : yHi - yLo > 12 ? 3 : yHi - yLo > 6 ? 2 : 1;
  const yTicks = finiteTicks(yLo, yHi, yStride);

  return (
    <div className="space-y-3">
      <svg viewBox={`0 0 ${WIDTH} ${HEIGHT}`} role="img" className="h-auto w-full">
        <title>Theorem 4.4 as a balance: surplus against the floor-crumb budget</title>
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
            y={BOTTOM + 16}
            textAnchor="middle"
            fill={MUTED}
            fontFamily="IBM Plex Mono, monospace"
            fontSize="10"
          >
            <TenPow exp={exp} />
          </text>
        ))}
        <text x={RIGHT} y={BOTTOM + 32} textAnchor="end" fill={MUTED} fontSize="11">
          cycle minimum n
        </text>

        {ready ? (
          <rect
            x={Math.min(xCross, RIGHT)}
            y={TOP}
            width={Math.max(0, RIGHT - Math.min(xCross, RIGHT))}
            height={BOTTOM - TOP}
            fill={OK}
            opacity="0.07"
          />
        ) : null}

        <line x1={LEFT} y1={TOP} x2={LEFT} y2={BOTTOM} stroke="#d4cbb8" />
        <line x1={LEFT} y1={BOTTOM} x2={RIGHT} y2={BOTTOM} stroke="#d4cbb8" />

        <path d={budgetPath} fill="none" stroke={EVEN} strokeWidth="2.5" />
        <line x1={LEFT} y1={yTheta} x2={RIGHT} y2={yTheta} stroke={ODD} strokeWidth="2.5" />

        <text x={LEFT + 8} y={yTheta - 8} fill={ODD} fontSize="11" fontFamily="Source Sans 3, sans-serif">
          surplus θ(L) = 1 − 2^L / 3^o — {sourceLabel}
        </text>
        <text x={LEFT + 8} y={TOP + 14} fill={EVEN} fontSize="11" fontFamily="Source Sans 3, sans-serif">
          budget L / (n ln n) — Theorem 4.4, constant 1
        </text>

        {ready ? (
          <>
            <circle cx={Math.min(xCross, RIGHT)} cy={yTheta} r="5" fill="#fffdf7" stroke={INK} strokeWidth="1.6" />
            <text
              x={Math.min(xCross, RIGHT - 40)}
              y={yTheta - 12}
              textAnchor="middle"
              fill={INK}
              fontSize="10"
              fontFamily="Source Sans 3, sans-serif"
            >
              budget = surplus
            </text>
          </>
        ) : null}

        <line x1={xFloor} y1={TOP} x2={xFloor} y2={BOTTOM} stroke={INK} strokeWidth="1.2" strokeDasharray="4 3" />
        <text x={xFloor} y={TOP - 8} textAnchor="middle" fill={INK} fontSize="11">
          N₀ = 10⁶
        </text>

        {xNMax !== null ? (
          <g>
            <path
              d={`M${xNMax},${yTheta - 9} L${xNMax + 8},${yTheta} L${xNMax},${yTheta + 9} L${xNMax - 8},${yTheta} Z`}
              fill={DEEP}
              stroke="#fffdf7"
              strokeWidth="1.5"
            />
            <text
              x={Math.max(xNMax, LEFT + 70)}
              y={yTheta + 24}
              textAnchor="middle"
              fill={DEEP}
              fontSize="10"
              fontFamily="IBM Plex Mono, monospace"
            >
              n_max = {formatGrouped(nMax!)}
            </text>
          </g>
        ) : null}

        <text x={LEFT} y={HEIGHT - 6} fill={MUTED} fontSize="11">
          {ready
            ? "right of the crossing the budget cannot pay: no cycle minimum lives there"
            : `θ is live through ${formatGrouped(LIVE_FINANCE_L_MAX)}; larger lengths need a shipped row`}
        </text>
        <text x={RIGHT} y={HEIGHT - 6} textAnchor="end" fill={dead ? OK : MUTED} fontSize="11">
          {nMax === null
            ? "no shipped n_max for this length"
            : dead
              ? "n_max ≤ N₀: length dead at the floor"
              : "n_max > N₀: finance survivor, not a cycle"}
        </text>
      </svg>

      {compact ? null : (
        <div className="grid gap-2 sm:grid-cols-4">
          <Cell label="L" value={formatGrouped(length)} hint={`o_min = ${formatGrouped(o)}`} />
          <Cell
            label="θ(L)"
            value={
              ready
                ? ledger.thetaDecimal.replace(/0+$/, "").replace(/\.$/, ".0")
                : "—"
            }
            hint={
              ledger?.source === "live"
                ? "1 − 2^L / 3^o, exact in the browser"
                : ledger?.source === "shipped"
                  ? "1 − 2^L / 3^o, shipped"
                  : `live through ${formatGrouped(LIVE_FINANCE_L_MAX)}`
            }
          />
          <Cell
            label="constant-1 crossing"
            value={
              !ready
                ? "—"
                : crossing >= 1e15
                  ? crossing.toExponential(2)
                  : `≈ ${formatGrouped(Math.round(crossing))}`
            }
            hint="n log n = L/θ · Theorem 4.4 alone"
          />
          <Cell
            label="parity n_max(L)"
            value={nMax === null ? "—" : formatGrouped(nMax)}
            hint={nMax === null ? "not in the shipped table" : "Theorem 4.6, 6/5 form, shipped"}
          />
        </div>
      )}
    </div>
  );
}

function Cell({ label, value, hint }: { label: string; value: string; hint?: string }) {
  return (
    <div className="min-w-0 rounded-lg border border-line bg-card px-3 py-2">
      <div className="text-[10px] uppercase tracking-wide text-muted">{label}</div>
      <div className="mt-0.5 font-mono text-base break-all text-ink">{value}</div>
      {hint ? <div className="mt-0.5 text-xs text-muted">{hint}</div> : null}
    </div>
  );
}

const RUNGS = [
  {
    name: "Theorem 4.4",
    tex: String.raw`n\log n\,(3^o-2^L)\le L\,3^o`,
    lean: "cycleMin_finance",
    status: "Lean",
    note: "Constant 1. The picture above.",
  },
  {
    name: "Corollary 4.4c",
    tex: String.raw`(3^o-2^L)\log n\le 3^o\sum_i \tfrac{1}{x_i}`,
    lean: "cycleMin_finance_inv_sum",
    status: "Lean",
    note: "Each one-step defect kept at its own state.",
  },
  {
    name: "Corollary 4.5",
    tex: String.raw`n_{\max}(L)\le N_0\ \Rightarrow\ \text{no cycle of length } L`,
    lean: "statewise parity charge",
    status: "prose",
    note: "A floor plus a per-length threshold.",
  },
  {
    name: "Theorem 4.6",
    tex: String.raw`1-\tfrac{2^L}{3^o}\le \tfrac65\sum_i \tfrac{1}{x_i\log x_i}`,
    lean: "cycleMin_defect_finance (n ≥ 400)",
    status: "Lean + table",
    note: "The 6/5 majorant; the shipped n_max marker.",
  },
] as const;

/** The four rungs the paper says must not be conflated. */
export function FinanceHierarchy() {
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
