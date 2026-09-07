import type { GapTransferView } from "../juggler/gapTransfer";

const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const INK = "#1d1914";
const MUTED = "#5e574c";
const OK = "#2d6a4f";

const WIDTH = 640;
const HEIGHT = 168;
const LEFT = 56;
const RIGHT = 584;
const TOP = 28;
const BOTTOM = 118;

type GapBalanceProps = {
  view: GapTransferView;
};

/**
 * Theorem 4.10 as a balance: n log n · min(Λ, 1) against 2L.
 */
export function GapBalance({ view }: GapBalanceProps) {
  const left = Math.max(view.left, 0);
  const right = view.right;
  const max = Math.max(left, right, 1);
  const xLeft = LEFT + (left / max) * (RIGHT - LEFT);
  const xRight = LEFT + (right / max) * (RIGHT - LEFT);
  const yLeft = 58;
  const yRight = 96;

  return (
    <svg viewBox={`0 0 ${WIDTH} ${HEIGHT}`} role="img" className="h-auto w-full">
      <title>Theorem 4.10: n log n times min(Λ, 1) against 2L</title>
      <line x1={LEFT} y1={TOP} x2={LEFT} y2={BOTTOM} stroke="#d4cbb8" />
      <line x1={LEFT} y1={BOTTOM} x2={RIGHT} y2={BOTTOM} stroke="#d4cbb8" />

      <line x1={LEFT} y1={yLeft} x2={xLeft} y2={yLeft} stroke={ODD} strokeWidth="8" strokeLinecap="round" />
      <text x={LEFT + 8} y={yLeft - 12} fill={ODD} fontSize="12" fontFamily="Source Sans 3, sans-serif">
        n log n · min(Λ, 1)
      </text>
      <text
        x={Math.min(xLeft + 8, RIGHT)}
        y={yLeft + 4}
        fill={INK}
        fontSize="11"
        fontFamily="IBM Plex Mono, monospace"
      >
        {formatSci(left)}
      </text>

      <line x1={LEFT} y1={yRight} x2={xRight} y2={yRight} stroke={EVEN} strokeWidth="8" strokeLinecap="round" />
      <text x={LEFT + 8} y={yRight - 12} fill={EVEN} fontSize="12" fontFamily="Source Sans 3, sans-serif">
        2L
      </text>
      <text
        x={Math.min(xRight + 8, RIGHT)}
        y={yRight + 4}
        fill={INK}
        fontSize="11"
        fontFamily="IBM Plex Mono, monospace"
      >
        {formatSci(right)}
      </text>

      <text x={LEFT} y={HEIGHT - 8} fill={view.holds ? OK : MUTED} fontSize="11">
        {view.holds
          ? "the gap transfer holds at this (n, L, o)"
          : "left side exceeds 2L — this pair is not a cycle minimum"}
      </text>
      <text x={RIGHT} y={HEIGHT - 8} textAnchor="end" fill={MUTED} fontSize="11">
        cycleMin_gap_transfer
      </text>
    </svg>
  );
}

function formatSci(value: number): string {
  if (!Number.isFinite(value)) return "—";
  if (value >= 1e5 || (value > 0 && value < 0.01)) return value.toExponential(2);
  return value.toFixed(2);
}
