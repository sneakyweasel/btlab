import { useId } from "react";
import { EVEN_BLOCK_BEAD_MAX } from "../juggler/constants";
import { formatInt } from "../juggler/format";
import { EMBER, SEA, beadColor } from "../juggler/palette";
import { evenPreimageInterval, type FiberView } from "../juggler/productions";
import { BeadMark } from "./BeadMark";

const WIDTH = 640;
const HEIGHT = 308;
const LEFT = 36;
const RIGHT = 604;
const O_Y = 52;
const E_Y = 164;
const M_Y = 276;
const TARGET_X = WIDTH / 2;
const TARGET_R = 16;
const WASH_H = 16;
const TICK = 10;
const PAD = 5;
const GREY = "#cfc6b4";

function EndCaption({
  x,
  lineY,
  side,
  lines,
}: {
  x: number;
  lineY: number;
  side: "above" | "below";
  lines: readonly string[];
}) {
  const stack = lines.filter((line) => line.length > 0);
  if (stack.length === 0) return null;
  const shown = side === "above" ? [...stack].reverse() : stack;
  const startY =
    side === "above" ? lineY - 14 - 12 * (shown.length - 1) : lineY + 20;
  return (
    <text
      x={x}
      y={startY}
      textAnchor="middle"
      fill="#5e574c"
      fontSize="10"
      fontFamily="IBM Plex Mono, monospace"
      paintOrder="stroke"
      stroke="#fffdf7"
      strokeWidth="4"
    >
      {shown.map((line, index) => (
        <tspan key={line} x={x} dy={index === 0 ? 0 : 12}>
          {line}
        </tspan>
      ))}
    </text>
  );
}

type OeFiberStripProps = {
  view: FiberView;
  selected?: number | null;
  onSelect?: (n: number) => void;
  onHover?: (n: number | null) => void;
};

function xOf(n: number, lo: number, hi: number): number {
  const span = Math.max(hi - lo, 1);
  return LEFT + ((n - lo) / span) * (RIGHT - LEFT);
}

/** Place an E-value on the O axis so n and ⌊n^{3/2}⌋ share an x. */
function eAxis(y: number): number {
  return Math.cbrt(y * y);
}

function clampX(x: number): number {
  return Math.min(RIGHT, Math.max(LEFT, x));
}

function integersOn(lo: number, hi: number): number[] {
  const out: number[] = [];
  for (let n = Math.max(0, Math.ceil(lo)); n < hi; n += 1) out.push(n);
  return out;
}

function tipToward(
  fromX: number,
  fromY: number,
  toX: number,
  toY: number,
  gap: number,
): { x: number; y: number } {
  const dx = toX - fromX;
  const dy = toY - fromY;
  const len = Math.hypot(dx, dy) || 1;
  return { x: toX - (dx / len) * gap, y: toY - (dy / len) * gap };
}

export function OeFiberStrip({
  view,
  selected = null,
  onSelect,
  onHover,
}: OeFiberStripProps) {
  const uid = useId().replace(/:/g, "");
  const oddMarker = `oe-fiber-o-${uid}`;
  const evenMarker = `oe-fiber-e-${uid}`;
  const { m, lo, hi, points, H, listed } = view;
  const block = evenPreimageInterval(m);
  const sea = points.filter((point) => point.imageEven);
  const oLo = Math.max(0, lo - PAD);
  const oHi = hi + PAD;
  const eLo = Math.max(0, block.lo - PAD);
  const eHi = block.hi + PAD;
  const rail = listed ? integersOn(oLo, oHi) : points.map((point) => point.n);
  const eListed = block.hi - block.lo <= EVEN_BLOCK_BEAD_MAX + 2 * PAD;
  const seaByImage = new Map(sea.map((point) => [point.image, point]));
  const eRail = eListed ? integersOn(eLo, eHi) : sea.map((point) => point.image);
  const targetFill = beadColor(m);
  const share =
    view.proportion === null ? "empty" : `OE ${view.proportion.toFixed(2)}`;
  const washLo = xOf(lo, oLo, oHi);
  const washHi = xOf(hi, oLo, oHi);
  const eWashLo = clampX(xOf(eAxis(block.lo), oLo, oHi));
  const eWashHi = clampX(xOf(eAxis(block.hi), oLo, oHi));

  return (
    <div>
      {listed ? null : (
        <p className="text-center text-sm text-muted">
          Too many to draw one bead each. First {points.length} of {H}:
        </p>
      )}
      <svg
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        role="img"
        className="h-auto w-full"
      >
        <title>{`OE fiber of ${m}: odd n on O, even images on E, arrows to m`}</title>
        <defs>
          <marker
            id={oddMarker}
            markerWidth="6"
            markerHeight="6"
            refX="5"
            refY="3"
            orient="auto"
          >
            <path d="M0 0 L6 3 L0 6 Z" fill={EMBER} />
          </marker>
          <marker
            id={evenMarker}
            markerWidth="6"
            markerHeight="6"
            refX="5"
            refY="3"
            orient="auto"
          >
            <path d="M0 0 L6 3 L0 6 Z" fill={SEA} />
          </marker>
        </defs>
        <text
          x={LEFT}
          y={18}
          fill="#1d1914"
          fontSize="12"
          fontFamily="IBM Plex Mono, monospace"
        >
          {`Φ(${formatInt(m)})`}
        </text>
        <text
          x={RIGHT}
          y={18}
          textAnchor="end"
          fill="#1d1914"
          fontSize="12"
          fontFamily="IBM Plex Mono, monospace"
        >
          {`H = ${H} · ${share}`}
        </text>

        <text
          x={8}
          y={O_Y + 4}
          fill={EMBER}
          fontSize="13"
          fontFamily="IBM Plex Mono, monospace"
        >
          O
        </text>
        <rect
          x={washLo}
          y={O_Y - WASH_H / 2}
          width={Math.max(washHi - washLo, 4)}
          height={WASH_H}
          fill={EMBER}
          opacity="0.34"
        />
        <line
          x1={LEFT}
          y1={O_Y}
          x2={RIGHT}
          y2={O_Y}
          stroke="#1d1914"
          strokeWidth="2"
        />
        <line
          x1={washLo}
          y1={O_Y - TICK}
          x2={washLo}
          y2={O_Y + TICK}
          stroke={EMBER}
          strokeWidth="1.5"
        />
        <line
          x1={washHi}
          y1={O_Y - TICK}
          x2={washHi}
          y2={O_Y + TICK}
          stroke={EMBER}
          strokeWidth="1.5"
        />
        {rail.map((n) => {
          const inside = n >= lo && n < hi;
          const fiber = inside && n % 2 === 1;
          const active = selected === n;
          return (
            <BeadMark
              key={`o-${n}`}
              n={n}
              x={xOf(n, oLo, oHi)}
              y={O_Y}
              color={inside ? beadColor(n) : GREY}
              radius={3.5}
              active={active}
              hideLabel={!active}
              onSelect={fiber ? onSelect : undefined}
              onHover={onHover}
            />
          );
        })}
        <EndCaption
          x={washHi - washLo < 56 ? (washLo + washHi) / 2 - 28 : washLo}
          lineY={O_Y}
          side="below"
          lines={[formatInt(lo), `∛(${formatInt(m)}⁴)`]}
        />
        <EndCaption
          x={washHi - washLo < 56 ? (washLo + washHi) / 2 + 28 : washHi}
          lineY={O_Y}
          side="below"
          lines={[formatInt(hi), `∛(${formatInt(m + 1)}⁴)`]}
        />

        <text
          x={8}
          y={E_Y + 4}
          fill={SEA}
          fontSize="13"
          fontFamily="IBM Plex Mono, monospace"
        >
          E
        </text>
        <rect
          x={eWashLo}
          y={E_Y - WASH_H / 2}
          width={Math.max(eWashHi - eWashLo, 4)}
          height={WASH_H}
          fill={SEA}
          opacity="0.34"
        />
        <line
          x1={LEFT}
          y1={E_Y}
          x2={RIGHT}
          y2={E_Y}
          stroke="#1d1914"
          strokeWidth="2"
        />
        <line
          x1={eWashLo}
          y1={E_Y - TICK}
          x2={eWashLo}
          y2={E_Y + TICK}
          stroke={SEA}
          strokeWidth="1.5"
        />
        <line
          x1={eWashHi}
          y1={E_Y - TICK}
          x2={eWashHi}
          y2={E_Y + TICK}
          stroke={SEA}
          strokeWidth="1.5"
        />
        {sea.map((point) => {
          const x = xOf(point.n, oLo, oHi);
          const active = selected === point.n;
          return (
            <line
              key={`oe-${point.n}`}
              x1={x}
              y1={O_Y + 8}
              x2={x}
              y2={active ? E_Y - 9 : E_Y}
              stroke={EMBER}
              strokeWidth={active ? 1.6 : 0.7}
              opacity={active ? 0.95 : 0.55}
              markerEnd={active ? `url(#${oddMarker})` : undefined}
              pointerEvents="none"
            />
          );
        })}
        {eRail.map((n) => {
          const parent = seaByImage.get(n);
          const inside = n >= block.lo && n < block.hi;
          const active = parent != null && selected === parent.n;
          const x = parent
            ? xOf(parent.n, oLo, oHi)
            : clampX(xOf(eAxis(n), oLo, oHi));
          return (
            <BeadMark
              key={`e-${n}`}
              n={n}
              x={x}
              y={E_Y}
              color={inside ? beadColor(n) : GREY}
              radius={parent ? 5.5 : 3.5}
              active={active}
              hideLabel={!active}
              onSelect={
                parent ? () => onSelect?.(parent.n) : undefined
              }
              onHover={
                parent
                  ? (value) => onHover?.(value === null ? null : parent.n)
                  : onHover
              }
            />
          );
        })}
        {sea.map((point) => {
          const x = xOf(point.n, oLo, oHi);
          const active = selected === point.n;
          const tip = tipToward(x, E_Y, TARGET_X, M_Y, TARGET_R + 3);
          return (
            <line
              key={`em-${point.n}`}
              x1={x}
              y1={E_Y}
              x2={tip.x}
              y2={tip.y}
              stroke={SEA}
              strokeWidth={active ? 1.6 : 0.7}
              opacity={active ? 0.95 : 0.55}
              markerEnd={active ? `url(#${evenMarker})` : undefined}
              pointerEvents="none"
            />
          );
        })}
        <EndCaption
          x={eWashHi - eWashLo < 56 ? (eWashLo + eWashHi) / 2 - 28 : eWashLo}
          lineY={E_Y}
          side="below"
          lines={[formatInt(block.lo), `${formatInt(m)}²`]}
        />
        <EndCaption
          x={eWashHi - eWashLo < 56 ? (eWashLo + eWashHi) / 2 + 28 : eWashHi}
          lineY={E_Y}
          side="below"
          lines={[formatInt(block.hi), `${formatInt(m + 1)}²`]}
        />

        <text
          x={8}
          y={M_Y + 4}
          fill={targetFill}
          fontSize="13"
          fontFamily="IBM Plex Mono, monospace"
        >
          m
        </text>
        <line
          x1={LEFT}
          y1={M_Y}
          x2={RIGHT}
          y2={M_Y}
          stroke="#1d1914"
          strokeWidth="2"
        />
        <circle
          cx={TARGET_X}
          cy={M_Y}
          r={TARGET_R}
          fill={targetFill}
          stroke="#1d1914"
          strokeWidth="1.6"
        />
        <text
          x={TARGET_X}
          y={M_Y + 4}
          textAnchor="middle"
          fill="#fffdf7"
          fontSize="12"
          fontFamily="IBM Plex Mono, monospace"
        >
          m
        </text>
        <text
          x={TARGET_X}
          y={M_Y - TARGET_R - 8}
          textAnchor="middle"
          fill="#1d1914"
          fontSize="12"
          fontFamily="IBM Plex Mono, monospace"
          paintOrder="stroke"
          stroke="#fffdf7"
          strokeWidth="4"
        >
          {formatInt(m)}
        </text>
      </svg>
      <p className="text-center text-sm text-muted">
        Every integer on O. Orange and blue sit in Φ(m); grey is outside that
        range. Unselected OE paths are lines; the selected path draws arrows.
      </p>
    </div>
  );
}
