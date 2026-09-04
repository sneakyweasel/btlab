import { EMBER, SEA } from "../juggler/palette";
import { formatInt } from "../juggler/format";
import type { FiberView } from "../juggler/productions";
import { BeadMark } from "./BeadMark";

type OeFiberStripProps = {
  view: FiberView;
  selected?: number | null;
  onSelect?: (n: number) => void;
  onHover?: (n: number | null) => void;
};

const LEFT = 36;
const RIGHT = 604;
const WIDTH = 640;

function xOf(n: number, lo: number, hi: number): number {
  const span = Math.max(hi - lo, 1);
  return LEFT + ((n - lo) / span) * (RIGHT - LEFT);
}

export function OeFiberStrip({
  view,
  selected = null,
  onSelect,
  onHover,
}: OeFiberStripProps) {
  const { m, lo, hi, points, listed } = view;
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
      {listed ? (
        points.map((point) => (
          <BeadMark
            key={point.n}
            x={xOf(point.n, lo, hi)}
            n={point.n}
            color={point.imageEven ? SEA : EMBER}
            active={selected === point.n}
            onSelect={onSelect}
            onHover={onHover}
          />
        ))
      ) : (
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
