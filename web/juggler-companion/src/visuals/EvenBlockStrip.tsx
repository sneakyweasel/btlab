import { useState } from "react";
import { EMBER, SEA } from "../juggler/palette";
import { formatInt } from "../juggler/format";
import type { EvenBlockView } from "../juggler/productions";
import { BeadMark } from "./BeadMark";
import { FloorCut } from "./FloorCut";

type EvenBlockStripProps = {
  view: EvenBlockView;
  selected?: number | null;
  onSelect?: (n: number) => void;
  onHover?: (n: number | null) => void;
};

const LEFT = 36;
const RIGHT = 604;
const WIDTH = 640;
const LINE_Y = 44;
const TARGET_X = WIDTH / 2;
const TARGET_Y = 158;
const TARGET_R = 16;

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
  const targetColor = m % 2 === 1 ? EMBER : SEA;
  const [hover, setHover] = useState<number | null>(null);
  const handleHover = (n: number | null) => {
    setHover(n);
    onHover?.(n);
  };
  const candidate = hover ?? selected;
  const live =
    candidate != null && candidate % 2 === 0
      ? candidate
      : (evens[0] ?? (lo % 2 === 0 ? lo : lo + 1));
  const pad = 5;
  const padLo = Math.max(0, lo - pad);
  const padHi = hi + pad;
  const outside: number[] = [];
  const interiorOdds: number[] = [];
  if (listed) {
    for (let n = padLo; n < padHi; n += 1) {
      if (n < lo || n >= hi) outside.push(n);
      else if (n % 2 !== 0) interiorOdds.push(n);
    }
  }
  const cutLo = xOf(lo, padLo, padHi);
  const cutHi = xOf(hi, padLo, padHi);
  const markerId = `even-block-arrow-${m}`;
  const land = (index: number, total: number) => {
    const t = total <= 1 ? 0.5 : index / (total - 1);
    const angle = (2 / 3) * Math.PI - t * ((1 / 3) * Math.PI);
    return {
      x: TARGET_X + TARGET_R * Math.cos(angle),
      y: TARGET_Y - TARGET_R * Math.sin(angle),
    };
  };
  return (
    <div>
      <svg viewBox={`0 0 ${WIDTH} 182`} role="img" className="h-auto w-full">
      <title>{`Even block of ${m}: ${count} evens in [${lo}, ${hi}) map to ${m}`}</title>
      <defs>
        <marker
          id={markerId}
          markerWidth="5"
          markerHeight="5"
          refX="4"
          refY="2.5"
          orient="auto"
        >
          <path d="M0 0 L5 2.5 L0 5 Z" fill={SEA} />
        </marker>
      </defs>
      <rect
        x={cutLo}
        y={LINE_Y - 8}
        width={Math.max(cutHi - cutLo, 4)}
        height="16"
        fill={SEA}
        opacity="0.34"
      />
      <line x1={LEFT} y1={LINE_Y} x2={RIGHT} y2={LINE_Y} stroke="#1d1914" strokeWidth="2" />
      <line
        x1={cutLo}
        y1={LINE_Y - 10}
        x2={cutLo}
        y2={LINE_Y + 10}
        stroke={SEA}
        strokeWidth="1.5"
      />
      <line
        x1={cutHi}
        y1={LINE_Y - 10}
        x2={cutHi}
        y2={LINE_Y + 10}
        stroke={SEA}
        strokeWidth="1.5"
      />
      <text
        x={cutLo}
        y="18"
        textAnchor="middle"
        fill="#5e574c"
        fontSize="12"
        fontFamily="IBM Plex Mono, monospace"
      >
        {formatInt(lo)}
      </text>
      <text
        x={cutHi}
        y="18"
        textAnchor="middle"
        fill="#5e574c"
        fontSize="12"
        fontFamily="IBM Plex Mono, monospace"
      >
        {formatInt(hi)}
      </text>
      {listed
        ? outside.map((n) => (
            <BeadMark
              key={`f-${n}`}
              x={xOf(n, padLo, padHi)}
              y={LINE_Y}
              n={n}
              color="#cfc6b4"
              radius={3.5}
              active={live === n}
              onHover={handleHover}
            />
          ))
        : null}
      {listed
        ? interiorOdds.map((n) => (
            <BeadMark
              key={`o-${n}`}
              x={xOf(n, padLo, padHi)}
              y={LINE_Y}
              n={n}
              color={EMBER}
              radius={3.5}
            />
          ))
        : null}
      {listed
        ? evens.map((n) => (
            <BeadMark
              key={`e-${n}`}
              x={xOf(n, padLo, padHi)}
              y={LINE_Y}
              n={n}
              color={SEA}
              active={live === n}
              onSelect={onSelect}
              onHover={handleHover}
            />
          ))
        : null}
      {listed
        ? evens.map((n, index) => {
            const x = xOf(n, padLo, padHi);
            const tip = land(index, evens.length);
            const active = live === n;
            return (
              <line
                key={`a-${n}`}
                x1={x}
                y1={LINE_Y}
                x2={tip.x}
                y2={tip.y}
                stroke={SEA}
                strokeWidth={active ? 1.5 : 0.75}
                opacity={active ? 0.95 : 0.5}
                markerEnd={active ? `url(#${markerId})` : undefined}
                pointerEvents="none"
              />
            );
          })
        : (
          <path
            d={`M ${cutLo} ${LINE_Y} L ${cutHi} ${LINE_Y} L ${TARGET_X} ${TARGET_Y - TARGET_R} Z`}
            fill={SEA}
            opacity="0.28"
          />
        )}
      <circle cx={TARGET_X} cy={TARGET_Y} r={TARGET_R} fill={targetColor} />
      <text
        x={TARGET_X}
        y={TARGET_Y + 4}
        textAnchor="middle"
        fill="#fffdf7"
        fontSize="13"
        fontFamily="IBM Plex Mono, monospace"
      >
        {formatInt(m)}
      </text>
      {listed ? null : (
        <text
          x={TARGET_X + TARGET_R + 10}
          y={TARGET_Y + 4}
          fill={SEA}
          fontSize="12"
          fontFamily="IBM Plex Mono, monospace"
        >
          {`${formatInt(count)} evens`}
        </text>
      )}
      </svg>
      {listed ? null : (
        <p className="text-center text-sm text-muted">
          Too many to draw one bead each. One member:
        </p>
      )}
      <FloorCut compact n={BigInt(live)} />
    </div>
  );
}
