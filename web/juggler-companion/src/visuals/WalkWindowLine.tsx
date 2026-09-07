import { WALK_WINDOW_HI, WALK_WINDOW_LO } from "../juggler/constants";
import { formatGrouped } from "../juggler/format";
import { WALK_WINDOW_MARKS } from "../juggler/walkCharge";

const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const INK = "#1d1914";
const DEEP = "#1f3d34";

const WIDTH = 640;
const HEIGHT = 132;
const LEFT = 28;
const RIGHT = 612;
const AXIS = 58;

type WalkWindowLineProps = {
  selectedL: number;
  compact?: boolean;
};

/**
 * Number line on the census-free window [50,508, 16,785,921).
 * Charge envelope uniform; θ(L) comparison still per length.
 */
export function WalkWindowLine({ selectedL, compact = false }: WalkWindowLineProps) {
  const logLo = Math.log10(WALK_WINDOW_LO);
  const logHi = Math.log10(WALK_WINDOW_HI);
  const xOf = (length: number) => {
    const t = (Math.log10(length) - logLo) / (logHi - logLo);
    return LEFT + t * (RIGHT - LEFT);
  };
  const inWindow = selectedL >= WALK_WINDOW_LO && selectedL < WALK_WINDOW_HI;
  const xSelected = inWindow ? xOf(selectedL) : null;

  return (
    <div className="space-y-2">
      <svg viewBox={`0 0 ${WIDTH} ${HEIGHT}`} role="img" className="h-auto w-full">
        <title>Walk-charge window from 50508 to 16785921</title>
        <line x1={LEFT} y1={AXIS} x2={RIGHT} y2={AXIS} stroke={DEEP} strokeWidth="3" />
        {WALK_WINDOW_MARKS.map((mark) => {
          const x = xOf(mark.L);
          const bound = mark.role === "bound";
          return (
            <g key={mark.L}>
              <line
                x1={x}
                y1={AXIS - (bound ? 14 : 10)}
                x2={x}
                y2={AXIS + (bound ? 14 : 10)}
                stroke={bound ? ODD : EVEN}
                strokeWidth={bound ? 2 : 1.5}
              />
              <text
                x={x}
                y={bound ? 22 : 118}
                textAnchor="middle"
                fill={INK}
                fontSize="10"
                fontFamily="IBM Plex Mono, monospace"
              >
                {mark.label}
              </text>
            </g>
          );
        })}
        {xSelected !== null ? (
          <circle cx={xSelected} cy={AXIS} r="5" fill={DEEP} />
        ) : null}
      </svg>
      {compact ? null : (
        <p className="text-sm text-muted">
          Charge envelope uniform on [{formatGrouped(WALK_WINDOW_LO)},{" "}
          {formatGrouped(WALK_WINDOW_HI)}). The comparison against θ(L) is still
          per length, so the kill tables are not census-free.
        </p>
      )}
    </div>
  );
}
