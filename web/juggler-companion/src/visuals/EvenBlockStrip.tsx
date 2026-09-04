import { SEA } from "../juggler/palette";
import { formatInt } from "../juggler/format";
import type { EvenBlockView } from "../juggler/productions";
import { BeadMark } from "./BeadMark";

type EvenBlockStripProps = {
  view: EvenBlockView;
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

export function EvenBlockStrip({
  view,
  selected = null,
  onSelect,
  onHover,
}: EvenBlockStripProps) {
  const { m, lo, hi, evens, listed, count } = view;
  const odds: number[] = [];
  if (listed) {
    for (let n = lo; n < hi; n += 1) {
      if (n % 2 !== 0) odds.push(n);
    }
  }
  return (
    <svg viewBox={`0 0 ${WIDTH} 132`} role="img" className="h-auto w-full">
      <title>{`Even block of ${m}: ${count} evens in [${lo}, ${hi}) map to ${m}`}</title>
      <rect
        x={xOf(lo, lo, hi)}
        y="40"
        width={Math.max(xOf(hi, lo, hi) - xOf(lo, lo, hi), 4)}
        height="20"
        fill={SEA}
        opacity="0.16"
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
        {formatInt(hi)}
      </text>
      {listed
        ? odds.map((n) => (
            <BeadMark
              key={`o-${n}`}
              x={xOf(n, lo, hi)}
              n={n}
              color="#cfc6b4"
              radius={3.5}
            />
          ))
        : null}
      {listed
        ? evens.map((n) => (
            <BeadMark
              key={`e-${n}`}
              x={xOf(n, lo, hi)}
              n={n}
              color={SEA}
              active={selected === n}
              onSelect={onSelect}
              onHover={onHover}
            />
          ))
        : null}
      <path d={`M ${WIDTH / 2} 96 L ${WIDTH / 2} 112`} stroke={SEA} strokeWidth="1.5" />
      <path
        d={`M ${WIDTH / 2 - 5} 108 L ${WIDTH / 2} 114 L ${WIDTH / 2 + 5} 108`}
        fill="none"
        stroke={SEA}
        strokeWidth="1.5"
      />
      <text
        x={WIDTH / 2}
        y="128"
        textAnchor="middle"
        fill={SEA}
        fontSize="12"
        fontFamily="IBM Plex Mono, monospace"
      >
        {listed
          ? `every sea bead → ${m}`
          : `${count.toLocaleString("en-US")} evens → ${m}`}
      </text>
    </svg>
  );
}
