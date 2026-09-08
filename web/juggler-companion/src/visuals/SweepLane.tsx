import { Tex } from "../components/Tex";
import { EVEN, ODD, beadColor } from "../juggler/palette";
import type { FiberPoint } from "../juggler/productions";
import { BeadMark } from "./BeadMark";

type SweepLaneProps = {
  points: FiberPoint[];
  selected?: number | null;
  onSelect?: (n: number) => void;
  onHover?: (n: number | null) => void;
};

const WIDTH = 640;
const HEIGHT = 312;
const CX = 320;
const CY = 156;
const R = 92;
const WASH = 30;

/** 0 at the top; phase increases clockwise. Even = left, odd = right. */
function thetaOf(phase: number): number {
  const t = Math.min(Math.max(phase, 0), 0.999999);
  return -Math.PI / 2 - 2 * Math.PI * t;
}

function xyOf(phase: number, radius = R): { x: number; y: number } {
  const t = thetaOf(phase === 1 ? 0 : phase);
  return { x: CX + radius * Math.cos(t), y: CY + radius * Math.sin(t) };
}

function semicircle(from: number, to: number, radius: number): string {
  const start = xyOf(from, radius);
  const end = xyOf(to, radius);
  return `M ${start.x} ${start.y} A ${radius} ${radius} 0 0 1 ${end.x} ${end.y}`;
}

function radialTick(phase: number, inner: number, outer: number): string {
  const a = xyOf(phase, inner);
  const b = xyOf(phase, outer);
  return `M ${a.x} ${a.y} L ${b.x} ${b.y}`;
}

export function SweepLane({
  points,
  selected = null,
  onSelect,
  onHover,
}: SweepLaneProps) {
  const evenN = points.filter((point) => point.imageEven).length;
  const occupation =
    evenN === 0
      ? "This fiber sits in the odd half."
      : evenN === points.length
        ? "This fiber sits in the even half."
        : "Both halves appear.";
  return (
    <div>
      <svg viewBox={`0 0 ${WIDTH} ${HEIGHT}`} role="img" className="h-auto w-full">
        <title>
          Sweep of the fractional part of n to the three-halves over 2, on the
          circle with 0 glued to 1
        </title>
        <path
          d={semicircle(0, 0.5, R)}
          fill="none"
          stroke={EVEN}
          strokeWidth={WASH}
          opacity="0.18"
        />
        <path
          d={semicircle(0.5, 1, R)}
          fill="none"
          stroke={ODD}
          strokeWidth={WASH}
          opacity="0.18"
        />
        <circle
          cx={CX}
          cy={CY}
          r={R}
          fill="none"
          stroke="#1d1914"
          strokeWidth="2"
        />
        <path
          d={`${radialTick(0, R - 11, R + 11)} ${radialTick(0.5, R - 11, R + 11)}`}
          fill="none"
          stroke="#1d1914"
          strokeWidth="1.4"
        />
        <text
          x={CX}
          y={CY - R + 26}
          textAnchor="middle"
          fill="#5e574c"
          fontSize="12"
          fontFamily="IBM Plex Mono, monospace"
        >
          0 = 1
        </text>
        <text
          x={CX}
          y={CY + R - 16}
          textAnchor="middle"
          fill="#5e574c"
          fontSize="12"
          fontFamily="IBM Plex Mono, monospace"
        >
          1/2
        </text>
        <text
          x={CX - 44}
          y={CY + 4}
          textAnchor="middle"
          fill={EVEN}
          fontSize="11"
        >
          even image
        </text>
        <text
          x={CX + 44}
          y={CY + 4}
          textAnchor="middle"
          fill={ODD}
          fontSize="11"
        >
          odd image
        </text>
        {points.map((point) => {
          const { x, y } = xyOf(point.sweep);
          return (
            <BeadMark
              key={point.n}
              x={x}
              y={y}
              n={point.n}
              color={beadColor(point.n)}
              radius={5.5}
              active={selected === point.n}
              labelBelow={y > CY}
              onSelect={onSelect}
              onHover={onHover}
            />
          );
        })}
      </svg>
      <p className="text-center text-sm text-muted">
        <Tex>{String.raw`\{n^{3/2}/2\}`}</Tex> on the circle{" "}
        <Tex>{String.raw`\mathbb{R}/\mathbb{Z}`}</Tex> — 0 and 1 are the same
        point. {occupation}
      </p>
    </div>
  );
}
