import { EMBER, SEA } from "../juggler/palette";
import { formatInt } from "../juggler/format";
import type { FiberView } from "../juggler/productions";

type OeFiberStripProps = {
  view: FiberView;
  selected?: number | null;
  onSelect?: (n: number) => void;
};

const LEFT = 36;
const RIGHT = 604;
const WIDTH = 640;

function xOf(n: number, lo: number, hi: number): number {
  const span = Math.max(hi - lo, 1);
  return LEFT + ((n - lo) / span) * (RIGHT - LEFT);
}

export function OeFiberStrip({ view, selected = null, onSelect }: OeFiberStripProps) {
  const { m, lo, hi, points, listed } = view;
  const labelPoints = points.length <= 8;
  const last = points[points.length - 1]?.n ?? hi - 1;
  return (
    <svg viewBox={`0 0 ${WIDTH} 118`} role="img" className="h-auto w-full">
      <title>{`OE fiber of ${m}: odd n with floor(n^{3/4}) = ${m}`}</title>
      <rect
        x={xOf(lo, lo, hi)}
        y="40"
        width={Math.max(xOf(hi, lo, hi) - xOf(lo, lo, hi), 4)}
        height="20"
        fill={SEA}
        opacity="0.12"
      />
      <line x1={LEFT} y1="50" x2={RIGHT} y2="50" stroke="#1d1914" strokeWidth="2" />
      <text x={LEFT} y="88" fill="#5e574c" fontSize="12" fontFamily="IBM Plex Mono, monospace">
        {formatInt(lo)}
      </text>
      <text
        x={RIGHT}
        y="88"
        textAnchor="end"
        fill="#5e574c"
        fontSize="12"
        fontFamily="IBM Plex Mono, monospace"
      >
        {formatInt(last + 2)}
      </text>
      {listed
        ? points.map((point) => {
            const active = selected === point.n;
            const color = point.imageEven ? SEA : EMBER;
            return (
              <g key={point.n}>
                <circle
                  cx={xOf(point.n, lo, hi)}
                  cy="50"
                  r={active ? 8 : 6}
                  fill={color}
                  stroke={active ? "#1d1914" : "none"}
                  strokeWidth={active ? 2 : 0}
                  style={{ cursor: onSelect ? "pointer" : undefined }}
                  onClick={() => onSelect?.(point.n)}
                >
                  <title>
                    {point.imageEven
                      ? `${point.n} odd, even image → J(J(${point.n})) = ${m}`
                      : `${point.n} odd, odd image — not this production`}
                  </title>
                </circle>
                {labelPoints ? (
                  <text
                    x={xOf(point.n, lo, hi)}
                    y="28"
                    textAnchor="middle"
                    fill={color}
                    fontSize="11"
                    fontFamily="IBM Plex Mono, monospace"
                  >
                    {point.n}
                  </text>
                ) : null}
              </g>
            );
          })
        : (
          <text
            x={WIDTH / 2}
            y="54"
            textAnchor="middle"
            fill="#5e574c"
            fontSize="12"
            fontFamily="IBM Plex Mono, monospace"
          >
            fiber longer than the display cap
          </text>
        )}
      <text
        x={WIDTH / 2}
        y="110"
        textAnchor="middle"
        fill="#5e574c"
        fontSize="12"
      >
        sea = even image, joins A · ember = odd image
      </text>
    </svg>
  );
}
