import { EMBER, SEA } from "../juggler/palette";
import type { FiberPoint } from "../juggler/productions";
import { BeadMark } from "./BeadMark";

type SweepLaneProps = {
  points: FiberPoint[];
  selected?: number | null;
  onSelect?: (n: number) => void;
  onHover?: (n: number | null) => void;
};

const LEFT = 36;
const RIGHT = 604;
const WIDTH = 640;
const Y = 50;

function xOf(phase: number): number {
  return LEFT + Math.min(Math.max(phase, 0), 0.999) * (RIGHT - LEFT);
}

export function SweepLane({
  points,
  selected = null,
  onSelect,
  onHover,
}: SweepLaneProps) {
  const mid = xOf(0.5);
  return (
    <svg viewBox={`0 0 ${WIDTH} 118`} role="img" className="h-auto w-full">
      <title>Sweep of floor(n^{3/2}) parity on the unit interval</title>
      <rect x={LEFT} y="38" width={mid - LEFT} height="24" fill={SEA} opacity="0.18" />
      <rect x={mid} y="38" width={RIGHT - mid} height="24" fill={EMBER} opacity="0.18" />
      <line x1={LEFT} y1={Y} x2={RIGHT} y2={Y} stroke="#1d1914" strokeWidth="2" />
      <line x1={mid} y1="34" x2={mid} y2="66" stroke="#1d1914" strokeWidth="1" />
      <text x={LEFT} y="88" fill="#5e574c" fontSize="12" fontFamily="IBM Plex Mono, monospace">
        0
      </text>
      <text
        x={mid}
        y="88"
        textAnchor="middle"
        fill="#5e574c"
        fontSize="12"
        fontFamily="IBM Plex Mono, monospace"
      >
        1/2
      </text>
      <text
        x={RIGHT}
        y="88"
        textAnchor="end"
        fill="#5e574c"
        fontSize="12"
        fontFamily="IBM Plex Mono, monospace"
      >
        1
      </text>
      {points.map((point) => (
        <BeadMark
          key={point.n}
          x={xOf(point.sweep)}
          y={Y}
          n={point.n}
          color={point.imageEven ? SEA : EMBER}
          radius={5.5}
          active={selected === point.n}
          onSelect={onSelect}
          onHover={onHover}
        />
      ))}
      <text x={LEFT + 8} y="28" fill={SEA} fontSize="11">
        even image
      </text>
      <text x={mid + 8} y="28" fill={EMBER} fontSize="11">
        odd image
      </text>
      <text
        x={WIDTH / 2}
        y="110"
        textAnchor="middle"
        fill="#5e574c"
        fontSize="12"
      >
        {`{n^{3/2}/2} walks a nearly constant step — both halves appear`}
      </text>
    </svg>
  );
}
