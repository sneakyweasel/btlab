import { Tex } from "../components/Tex";
import { EVEN, ODD, beadColor } from "../juggler/palette";
import type { FiberPoint, SweepLemmaView } from "../juggler/productions";
import { BeadMark } from "./BeadMark";

type SweepLaneProps = {
  points: FiberPoint[];
  lemma?: SweepLemmaView | null;
  selected?: number | null;
  onSelect?: (n: number) => void;
  onHover?: (n: number | null) => void;
};

const WARN = "#8b3a2a";

const WIDTH = 640;
const HEIGHT = 312;
const CX = 320;
const CY = 156;
const R = 92;

/**
 * 0 at the top; phase increases toward the left (12 → 9 → 6).
 * Even images occupy [0, 1/2) — the left half. SVG sweep-flag 0 follows that.
 */
function thetaOf(phase: number): number {
  const t = Math.min(Math.max(phase, 0), 0.999999);
  return -Math.PI / 2 - 2 * Math.PI * t;
}

function xyOf(phase: number, radius = R): { x: number; y: number } {
  const t = thetaOf(phase === 1 ? 0 : phase);
  return { x: CX + radius * Math.cos(t), y: CY + radius * Math.sin(t) };
}

function halfDisk(from: number, to: number, radius: number): string {
  const start = xyOf(from, radius);
  const end = xyOf(to, radius);
  return `M ${CX} ${CY} L ${start.x} ${start.y} A ${radius} ${radius} 0 0 0 ${end.x} ${end.y} Z`;
}

function radialTick(phase: number, inner: number, outer: number): string {
  const a = xyOf(phase, inner);
  const b = xyOf(phase, outer);
  return `M ${a.x} ${a.y} L ${b.x} ${b.y}`;
}

function phaseArc(from: number, to: number, radius: number): string {
  const start = xyOf(from, radius);
  const end = xyOf(to, radius);
  const delta = ((to - from) % 1 + 1) % 1;
  if (delta < 1e-9 || delta > 0.45) return "";
  return `M ${start.x} ${start.y} A ${radius} ${radius} 0 0 0 ${end.x} ${end.y}`;
}

function mod1(phase: number): number {
  return ((phase % 1) + 1) % 1;
}

/** Edges of a Lemma 4.2 window. Skip once it is no longer a local neighborhood. */
function windowEdges(center: number, width: number): number[] {
  if (!Number.isFinite(width) || width <= 0 || width >= 0.25) return [];
  return [mod1(center - width), mod1(center + width)];
}

function windowBand(center: number, width: number, radius: number): string {
  if (width <= 0 || width > 0.15) return "";
  return phaseArc(mod1(center - width), mod1(center + width), radius);
}

/** Mark the thin pole, not whichever window happens to be small enough to draw. */
function lemmaWindows(
  lemma: SweepLemmaView,
): { center: number; width: number }[] {
  if (lemma.verdict === "empty") return [];
  if (lemma.verdict === "thin-zero") return [{ center: 0, width: lemma.needZero }];
  if (lemma.verdict === "thin-half") {
    return [{ center: 0.5, width: lemma.needHalf }];
  }
  return [
    { center: 0, width: lemma.needZero },
    { center: 0.5, width: lemma.needHalf },
  ];
}

export function SweepLane({
  points,
  lemma = null,
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
  const origin =
    selected === null
      ? null
      : (points.find((point) => point.n === selected)?.sweep ?? null);
  const stepArc =
    lemma && origin !== null && lemma.reduced !== null && lemma.reduced > 1e-6
      ? phaseArc(origin, origin + lemma.reduced, R)
      : "";
  return (
    <div>
      <svg viewBox={`0 0 ${WIDTH} ${HEIGHT}`} role="img" className="h-auto w-full">
        <title>
          Sweep of the fractional part of n to the three-halves over 2, on the
          circle with 0 glued to 1
        </title>
        <path d={halfDisk(0, 0.5, R)} fill={EVEN} opacity="0.14" stroke="none" />
        <path d={halfDisk(0.5, 1, R)} fill={ODD} opacity="0.14" stroke="none" />
        <circle
          cx={CX}
          cy={CY}
          r={R}
          fill="none"
          stroke="#1d1914"
          strokeWidth="2"
        />
        {stepArc ? (
          <path
            d={stepArc}
            fill="none"
            stroke="#1d1914"
            strokeWidth="2"
            opacity="0.45"
          />
        ) : null}
        <path
          d={`${radialTick(0, R - 11, R + 11)} ${radialTick(0.5, R - 11, R + 11)}`}
          fill="none"
          stroke="#1d1914"
          strokeWidth="1.4"
        />
        {lemma
          ? lemmaWindows(lemma).flatMap(({ center, width }) => {
              const band = windowBand(center, width, R);
              const ticks = windowEdges(center, width);
              const pole =
                ticks.length === 0 && width > 0
                  ? [radialTick(center, R - 12, R + 14)]
                  : [];
              return [
                band ? (
                  <path
                    key={`window-band-${center}`}
                    d={band}
                    fill="none"
                    stroke={WARN}
                    strokeWidth="6"
                    opacity="0.4"
                  />
                ) : null,
                ...ticks.map((phase) => (
                  <path
                    key={`window-tick-${center}-${phase}`}
                    d={radialTick(phase, R - 12, R + 12)}
                    fill="none"
                    stroke={WARN}
                    strokeWidth="2"
                  />
                )),
                ...pole.map((d) => (
                  <path
                    key={`window-pole-${center}`}
                    d={d}
                    fill="none"
                    stroke={WARN}
                    strokeWidth="2.4"
                  />
                )),
              ];
            })
          : null}
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
