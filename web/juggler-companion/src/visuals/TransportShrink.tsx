import type { WalkChargeView } from "../juggler/walkCharge";

const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const INK = "#1d1914";
const MUTED = "#5e574c";

const WIDTH = 640;
const HEIGHT = 168;
const LEFT = 56;
const RIGHT = 584;
const TOP = 28;
const BOTTOM = 118;

type TransportShrinkProps = {
  view: WalkChargeView;
};

/**
 * Theorem 5.3 as a shrink: n against the reduced base n' = n e^{-D}.
 */
export function TransportShrink({ view }: TransportShrinkProps) {
  const n = Math.max(view.n, 1);
  const nPrime = Math.max(view.nPrime, 0);
  const max = Math.max(n, nPrime, 1);
  const xN = LEFT + (n / max) * (RIGHT - LEFT);
  const xPrime = LEFT + (nPrime / max) * (RIGHT - LEFT);
  const yN = 58;
  const yPrime = 96;

  return (
    <svg viewBox={`0 0 ${WIDTH} ${HEIGHT}`} role="img" className="h-auto w-full">
      <title>Theorem 5.3: cycle minimum n against the reduced base n prime</title>
      <line x1={LEFT} y1={TOP} x2={LEFT} y2={BOTTOM} stroke="#d4cbb8" />
      <line x1={LEFT} y1={BOTTOM} x2={RIGHT} y2={BOTTOM} stroke="#d4cbb8" />

      <line x1={LEFT} y1={yN} x2={xN} y2={yN} stroke={ODD} strokeWidth="8" strokeLinecap="round" />
      <text x={LEFT + 8} y={yN - 12} fill={ODD} fontSize="12" fontFamily="Source Sans 3, sans-serif">
        n
      </text>
      <text
        x={Math.min(xN + 8, RIGHT)}
        y={yN + 4}
        fill={INK}
        fontSize="11"
        fontFamily="IBM Plex Mono, monospace"
      >
        {formatSci(n)}
      </text>

      <line
        x1={LEFT}
        y1={yPrime}
        x2={xPrime}
        y2={yPrime}
        stroke={EVEN}
        strokeWidth="8"
        strokeLinecap="round"
      />
      <text x={LEFT + 8} y={yPrime - 12} fill={EVEN} fontSize="12" fontFamily="Source Sans 3, sans-serif">
        n′
      </text>
      <text
        x={Math.min(xPrime + 8, RIGHT)}
        y={yPrime + 4}
        fill={INK}
        fontSize="11"
        fontFamily="IBM Plex Mono, monospace"
      >
        {formatSci(nPrime)}
      </text>

      <text x={LEFT} y={HEIGHT - 8} fill={MUTED} fontSize="11">
        finance at the reduced base · hypothesis n ≥ 400
      </text>
      <text x={RIGHT} y={HEIGHT - 8} textAnchor="end" fill={MUTED} fontSize="11">
        cycleMin_transport
      </text>
    </svg>
  );
}

function formatSci(value: number): string {
  if (!Number.isFinite(value)) return "—";
  if (value >= 1e5 || (value > 0 && value < 0.01)) return value.toExponential(2);
  return value.toFixed(2);
}
