import { useId } from "react";
import { formatInt } from "../juggler/format";
import { EMBER, SEA, beadColor } from "../juggler/palette";
import { evenPreimageInterval, type FiberView } from "../juggler/productions";
import { BeadMark } from "./BeadMark";

const WIDTH = 640;
const HEIGHT = 328;
const LEFT = 36;
const RIGHT = 604;
const O_Y = 52;
const E_Y = 164;
const M_Y = 276;
const TARGET_X = WIDTH / 2;
const TARGET_R = 16;
const WASH_H = 16;
const PAD = 5;
const GREY = "#cfc6b4";

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
  const rail = listed ? integersOn(oLo, oHi) : points.map((point) => point.n);
  const targetFill = beadColor(m);
  const share =
    view.proportion === null ? "empty" : `OE ${view.proportion.toFixed(2)}`;
  const washLo = xOf(lo, oLo, oHi);
  const washHi = xOf(hi, oLo, oHi);

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
          opacity="0.22"
        />
        <line
          x1={LEFT}
          y1={O_Y}
          x2={RIGHT}
          y2={O_Y}
          stroke="#1d1914"
          strokeWidth="2"
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
        <text
          x={LEFT}
          y={O_Y + 28}
          fill="#5e574c"
          fontSize="11"
          fontFamily="IBM Plex Mono, monospace"
        >
          O(m)
        </text>
        <text
          x={RIGHT}
          y={O_Y + 28}
          textAnchor="end"
          fill="#5e574c"
          fontSize="11"
          fontFamily="IBM Plex Mono, monospace"
        >
          {`[${formatInt(lo)}, ${formatInt(hi)})`}
        </text>

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
          x={LEFT}
          y={E_Y - WASH_H / 2}
          width={RIGHT - LEFT}
          height={WASH_H}
          fill={SEA}
          opacity="0.22"
        />
        <line
          x1={LEFT}
          y1={E_Y}
          x2={RIGHT}
          y2={E_Y}
          stroke="#1d1914"
          strokeWidth="2"
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
              y2={active ? E_Y - 7 : E_Y}
              stroke={EMBER}
              strokeWidth={active ? 1.6 : 0.7}
              opacity={active ? 0.95 : 0.55}
              markerEnd={active ? `url(#${oddMarker})` : undefined}
              pointerEvents="none"
            />
          );
        })}
        {sea.map((point) => {
          const x = xOf(point.n, oLo, oHi);
          const active = selected === point.n;
          const tip = tipToward(x, E_Y, TARGET_X, M_Y, TARGET_R + 3);
          return (
            <g key={`e-${point.n}`}>
              <line
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
              <BeadMark
                n={point.image}
                x={x}
                y={E_Y}
                color={beadColor(point.image)}
                radius={3.5}
                active={active}
                hideLabel={!active}
                onSelect={() => onSelect?.(point.n)}
                onHover={(n) => onHover?.(n === null ? null : point.n)}
              />
            </g>
          );
        })}
        <text
          x={LEFT}
          y={E_Y + 28}
          fill="#5e574c"
          fontSize="11"
          fontFamily="IBM Plex Mono, monospace"
        >
          E(m)
        </text>
        <text
          x={RIGHT}
          y={E_Y + 28}
          textAnchor="end"
          fill="#5e574c"
          fontSize="11"
          fontFamily="IBM Plex Mono, monospace"
        >
          {`[${formatInt(block.lo)}, ${formatInt(block.hi)})`}
        </text>

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
          y={M_Y + TARGET_R + 16}
          textAnchor="middle"
          fill="#1d1914"
          fontSize="12"
          fontFamily="IBM Plex Mono, monospace"
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
