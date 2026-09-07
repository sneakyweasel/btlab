import {
  FAN_CERTIFIED_FLOORS,
  FAN_K_MAX,
  FAN_ROWS,
  type FanWalkStatus,
} from "../juggler/fan";

const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const INK = "#1d1914";
const MUTED = "#5e574c";
const DEEP = "#1f3d34";
const OK = "#2d6a4f";

const WIDTH = 720;

type FanPlotProps = {
  selectedK: number;
  onSelect: (k: number) => void;
  compact?: boolean;
};

function nearestK(clientX: number, svg: SVGSVGElement, padL: number, inner: number): number {
  const box = svg.getBoundingClientRect();
  const x = ((clientX - box.left) / box.width) * WIDTH;
  const t = (x - padL) / inner;
  return Math.max(0, Math.min(FAN_K_MAX, Math.round(t * FAN_K_MAX)));
}

/**
 * Λ_k is affine and hits zero just past k = 55 — which is why the fan is 56 long.
 */
export function FanLambda({ selectedK, onSelect, compact = false }: FanPlotProps) {
  const height = 150;
  const padL = 52;
  const padB = 28;
  const padT = 10;
  const inner = WIDTH - padL - 12;
  const max = FAN_ROWS[0].lam;
  const xOf = (k: number) => padL + (k / FAN_K_MAX) * inner;
  const yOf = (lam: number) => padT + (1 - lam / max) * (height - padT - padB);
  const step = FAN_ROWS[0].lam - FAN_ROWS[1].lam;
  const zero = FAN_ROWS[0].lam / step;
  const selected = FAN_ROWS[selectedK] ?? FAN_ROWS[2];

  return (
    <figure className="space-y-2">
      <svg
        viewBox={`0 0 ${WIDTH} ${height}`}
        className="h-auto w-full cursor-pointer"
        role="img"
        aria-label="The linear form Lambda is affine in k and changes sign just past k = 55"
        onClick={(event) => onSelect(nearestK(event.clientX, event.currentTarget, padL, inner))}
      >
        <title>Proposition 5.12: Lambda affine in k</title>
        <line x1={padL} x2={WIDTH - 12} y1={yOf(0)} y2={yOf(0)} stroke="#d4cbb8" />
        <path
          d={FAN_ROWS.map((row, index) => `${index ? "L" : "M"}${xOf(row.k)},${yOf(row.lam)}`).join(" ")}
          fill="none"
          stroke={EVEN}
          strokeWidth="2"
        />
        <line
          x1={xOf(zero)}
          x2={xOf(zero)}
          y1={padT}
          y2={height - padB}
          stroke={ODD}
          strokeDasharray="4 3"
        />
        <text x={xOf(zero) + 6} y={padT + 12} fill={ODD} fontSize="10" fontFamily="IBM Plex Mono, monospace">
          Λ = 0 at k = {zero.toFixed(2)}
        </text>
        <circle cx={xOf(selected.k)} cy={yOf(selected.lam)} r="5" fill={DEEP} />
        <text x={padL - 6} y={yOf(0) + 3} textAnchor="end" fill={MUTED} fontSize="10">
          0
        </text>
      </svg>
      {compact ? null : (
        <figcaption className="text-xs text-muted">
          Λ_k = o_k log 3 − L_k log 2 is exactly affine in k, so the fan ends
          where it crosses zero: Λ₀/|Λ′| = 55.81, giving 56 members. The last
          one is L₅₅ = 16,785,921 = q₁₄.
        </figcaption>
      )}
    </figure>
  );
}

type FanStaircaseProps = FanPlotProps & {
  frontierK: number;
};

/**
 * Finance n_max against k. The walk-frontier marker is the printed bound,
 * not finance-only reachedAt.
 */
export function FanStaircase({ selectedK, frontierK, onSelect, compact = false }: FanStaircaseProps) {
  const height = 220;
  const padL = 56;
  const padB = 36;
  const padT = 12;
  const inner = WIDTH - padL - 12;
  const lo = Math.log10(FAN_ROWS[0].nmax);
  const hi = Math.log10(FAN_ROWS[FAN_ROWS.length - 1].nmax);
  const xOf = (k: number) => padL + (k / FAN_K_MAX) * inner;
  const yOf = (nmax: number) =>
    padT + (1 - (Math.log10(nmax) - lo) / (hi - lo)) * (height - padT - padB);
  const selected = FAN_ROWS[selectedK] ?? FAN_ROWS[2];

  return (
    <figure className="space-y-2">
      <svg
        viewBox={`0 0 ${WIDTH} ${height}`}
        className="h-auto w-full cursor-pointer"
        role="img"
        aria-label="Descent floor required for each member of the semiconvergent fan"
        onClick={(event) => onSelect(nearestK(event.clientX, event.currentTarget, padL, inner))}
      >
        <title>Section 5.8: finance n_max of each fan member</title>
        <rect
          x={padL}
          y={padT}
          width={Math.max(xOf(frontierK) - padL, 0)}
          height={height - padT - padB}
          fill={OK}
          opacity="0.08"
        />
        <line
          x1={xOf(frontierK)}
          x2={xOf(frontierK)}
          y1={padT}
          y2={height - padB}
          stroke={OK}
          strokeDasharray="4 3"
          strokeWidth="1.5"
        />

        {FAN_CERTIFIED_FLOORS.map((floor) => (
          <g key={floor.n0}>
            <line
              x1={padL}
              x2={WIDTH - 12}
              y1={yOf(floor.n0)}
              y2={yOf(floor.n0)}
              stroke="#d4cbb8"
              strokeDasharray="2 4"
            />
            <text
              x={padL - 6}
              y={yOf(floor.n0) + 3}
              textAnchor="end"
              fill={MUTED}
              fontSize="9"
              fontFamily="IBM Plex Mono, monospace"
            >
              {floor.label}
            </text>
          </g>
        ))}

        <path
          d={FAN_ROWS.map((row, index) => `${index ? "L" : "M"}${xOf(row.k)},${yOf(row.nmax)}`).join(" ")}
          fill="none"
          stroke={EVEN}
          strokeWidth="2"
        />
        {FAN_ROWS.filter((row) => row.k % 5 === 0 || row.k === FAN_K_MAX).map((row) => (
          <circle
            key={row.k}
            cx={xOf(row.k)}
            cy={yOf(row.nmax)}
            r="2.5"
            fill={row.k < frontierK ? OK : EVEN}
          />
        ))}
        <circle cx={xOf(selected.k)} cy={yOf(selected.nmax)} r="5" fill={DEEP} />

        <text x={xOf(0)} y={height - 20} textAnchor="middle" fill={MUTED} fontSize="10">
          k=0
        </text>
        <text x={xOf(FAN_K_MAX)} y={height - 20} textAnchor="middle" fill={MUTED} fontSize="10">
          k=55
        </text>
        <text x={xOf(frontierK)} y={height - 8} textAnchor="middle" fill={OK} fontSize="10">
          printed L_{frontierK}
        </text>
        <text x={WIDTH - 12} y={14} textAnchor="end" fill={INK} fontSize="10">
          n_max
        </text>
      </svg>
      {compact ? null : (
        <figcaption className="text-xs text-muted">
          Height is the shipped finance n_max(L_k), the descent floor at which
          finance alone passes that member. The dashed vertical is the printed
          walk-charge bound, not a finance-only reach. Horizontal dashes are
          the four certified floors.
        </figcaption>
      )}
    </figure>
  );
}

export function statusLabel(status: FanWalkStatus): string {
  if (status === "excluded") return "excluded by walk charge";
  if (status === "current") return "printed frontier";
  return "open";
}
