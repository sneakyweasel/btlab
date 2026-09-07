import { MAIN_FLOOR } from "../juggler/constants";
import { formatGrouped } from "../juggler/format";
import {
  type GapTransferView,
  namedSurvivorPoints,
  rhinMinLength,
} from "../juggler/gapTransfer";

const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const INK = "#1d1914";
const MUTED = "#5e574c";
const DEEP = "#1f3d34";
const OK = "#2d6a4f";

const WIDTH = 640;
const LEFT = 64;
const RIGHT = 596;

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

function finiteTicks(lo: number, hi: number, stride: number): number[] {
  const out: number[] = [];
  for (let exp = Math.ceil(lo); exp <= Math.floor(hi) && out.length < 16; exp += stride) {
    out.push(exp);
  }
  return out;
}

type GapPlaneProps = {
  view: GapTransferView;
  compact?: boolean;
};

/**
 * Corollary 4.11 as a plane. Below the Rhin frontier the pair is short
 * and excluded for every n ≥ 2. Finance survivors sit far above it.
 */
export function GapPlane({ view, compact = false }: GapPlaneProps) {
  const height = compact ? 250 : 310;
  const top = 28;
  const bottom = compact ? 196 : 246;
  const points = namedSurvivorPoints();

  const xLo = 0.3;
  const xHi = Math.min(
    12,
    Math.max(
      Math.log10(view.n),
      Math.log10(MAIN_FLOOR),
      ...points.map((row) => Math.log10(row.nMax)),
    ) + 0.4,
  );
  const yLo = 0;
  const yHi = Math.min(
    7.2,
    Math.max(Math.log10(Math.max(view.L, 4)), ...points.map((row) => Math.log10(row.L))) + 0.35,
  );

  const xOf = (log10n: number) => LEFT + ((log10n - xLo) / (xHi - xLo)) * (RIGHT - LEFT);
  const yOf = (log10L: number) => bottom - ((log10L - yLo) / (yHi - yLo)) * (bottom - top);

  const frontier: string[] = [];
  const shade: string[] = [`M${LEFT},${bottom}`];
  for (let index = 0; index <= 80; index += 1) {
    const log10n = xLo + ((xHi - xLo) * index) / 80;
    const n = 10 ** log10n;
    const L = rhinMinLength(Math.max(n, 2));
    const x = xOf(log10n);
    const y = yOf(Math.log10(Math.max(L, 1)));
    frontier.push(`${index === 0 ? "M" : "L"}${x.toFixed(1)},${y.toFixed(1)}`);
    shade.push(`L${x.toFixed(1)},${y.toFixed(1)}`);
  }
  shade.push(`L${RIGHT},${bottom}`, "Z");

  const xNow = xOf(Math.log10(view.n));
  const yNow = yOf(Math.log10(Math.max(view.L, 1)));
  const xFloor = xOf(Math.log10(MAIN_FLOOR));

  return (
    <div className="space-y-2">
      <svg viewBox={`0 0 ${WIDTH} ${height}`} role="img" className="h-auto w-full">
        <title>Rhin short-cycle region against finance survivors</title>
        {finiteTicks(yLo, yHi, yHi - yLo > 4 ? 2 : 1).map((exp) => (
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
        {finiteTicks(xLo, xHi, xHi - xLo > 8 ? 2 : 1).map((exp) => (
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
        <text x={LEFT - 8} y={top - 10} textAnchor="end" fill={MUTED} fontSize="11">
          L
        </text>

        <path d={shade.join(" ")} fill={OK} opacity="0.08" />
        <path d={frontier.join(" ")} fill="none" stroke={EVEN} strokeWidth="2.5" />

        <line x1={LEFT} y1={top} x2={LEFT} y2={bottom} stroke="#d4cbb8" />
        <line x1={LEFT} y1={bottom} x2={RIGHT} y2={bottom} stroke="#d4cbb8" />

        <line x1={xFloor} y1={top} x2={xFloor} y2={bottom} stroke={INK} strokeWidth="1.1" strokeDasharray="4 3" />
        <text x={xFloor} y={top - 8} textAnchor="middle" fill={INK} fontSize="11">
          N₀ = 3.5·10⁸
        </text>

        <line x1={xNow} y1={top} x2={xNow} y2={bottom} stroke={DEEP} strokeWidth="1.1" strokeDasharray="2 3" />
        <line x1={LEFT} y1={yNow} x2={RIGHT} y2={yNow} stroke={ODD} strokeWidth="1.1" strokeDasharray="2 3" />

        {points.map((row) => {
          const cx = xOf(Math.log10(row.nMax));
          const cy = yOf(Math.log10(row.L));
          return (
            <g key={row.L}>
              <circle cx={cx} cy={cy} r="4.5" fill={ODD} stroke="#fffdf7" strokeWidth="1.4" />
            </g>
          );
        })}

        <circle cx={xNow} cy={yNow} r="6" fill="#fffdf7" stroke={INK} strokeWidth="1.8" />

        <text x={LEFT + 8} y={top + 14} fill={EVEN} fontSize="11" fontFamily="Source Sans 3, sans-serif">
          Rhin frontier L = (n log n / 915)^{1/14.3}
        </text>
        <text x={LEFT + 8} y={top + 28} fill={OK} fontSize="11" fontFamily="Source Sans 3, sans-serif">
          below: short, excluded for every n ≥ 2
        </text>
        <text x={LEFT + 8} y={top + 42} fill={ODD} fontSize="11" fontFamily="Source Sans 3, sans-serif">
          dots: finance survivors at (n_max, L) — the long regime
        </text>

        <text x={LEFT} y={height - 6} fill={view.short ? OK : MUTED} fontSize="11">
          {view.short
            ? `this L is short at n = ${formatGrouped(view.n)}: Corollary 4.11 excludes it`
            : `this L is long at n = ${formatGrouped(view.n)}: the reduction does not kill it`}
        </text>
        <text x={RIGHT} y={height - 6} textAnchor="end" fill={MUTED} fontSize="11">
          Corollary 4.11
        </text>
      </svg>
    </div>
  );
}
