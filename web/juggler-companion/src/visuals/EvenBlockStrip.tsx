import { useState } from "react";
import { oddPreimages } from "../juggler/preimages";
import { EMBER, SEA } from "../juggler/palette";
import { formatInt } from "../juggler/format";
import { centerEvenInBlock, type EvenBlockView } from "../juggler/productions";
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
const LINE_Y = 48;
const TARGET_X = WIDTH / 2;
const ODD_Y = 248;
const TARGET_Y = (LINE_Y + ODD_Y) / 2;
const TARGET_R = 16;
const VIEW_H = 292;
const WASH_H = 16;
const TICK = 10;
const GREY = "#cfc6b4";

function xOf(n: number, lo: number, hi: number): number {
  const span = Math.max(hi - lo, 1);
  return LEFT + ((n - lo) / span) * (RIGHT - LEFT);
}

function integersOn(lo: number, hi: number): number[] {
  const out: number[] = [];
  for (let n = Math.max(0, Math.ceil(lo)); n < hi; n += 1) out.push(n);
  return out;
}

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

function tipToward(x: number, y: number) {
  const dx = TARGET_X - x;
  const dy = TARGET_Y - y;
  const len = Math.hypot(dx, dy) || 1;
  return {
    x: TARGET_X - (dx / len) * TARGET_R,
    y: TARGET_Y - (dy / len) * TARGET_R,
  };
}

type ParityLineProps = {
  y: number;
  winLo: number;
  winHi: number;
  washLo: number;
  washHi: number;
  members: readonly number[];
  memberColor: string;
  colorByParity: boolean;
  outward: "above" | "below";
  captions: readonly [readonly string[], readonly string[]];
  selected: number | null;
  hoverPads: boolean;
  showBeads: boolean;
  showWedge: boolean;
  markerId: string;
  insideColor?: string;
  hideActiveLabel?: boolean;
  onSelect?: (n: number) => void;
  onHover?: (n: number | null) => void;
};

function ParityLine({
  y,
  winLo,
  winHi,
  washLo,
  washHi,
  members,
  memberColor,
  colorByParity,
  outward,
  captions,
  selected,
  hoverPads,
  showBeads,
  showWedge,
  markerId,
  insideColor,
  hideActiveLabel = false,
  onSelect,
  onHover,
}: ParityLineProps) {
  const inward = outward === "above" ? "below" : "above";
  const cutLo = xOf(washLo, winLo, winHi);
  const cutHi = xOf(washHi, winLo, winHi);
  const memberSet = new Set(members);
  const ns = integersOn(winLo, winHi);
  const hasWash = washHi > washLo;
  return (
    <g>
      {hasWash ? (
        <rect
          x={cutLo}
          y={y - WASH_H / 2}
          width={Math.max(cutHi - cutLo, 4)}
          height={WASH_H}
          fill={memberColor}
          opacity="0.34"
        />
      ) : null}
      <line x1={LEFT} y1={y} x2={RIGHT} y2={y} stroke="#1d1914" strokeWidth="2" />
      {hasWash ? (
        <>
          <line
            x1={cutLo}
            y1={y - TICK}
            x2={cutLo}
            y2={y + TICK}
            stroke={memberColor}
            strokeWidth="1.5"
          />
          <line
            x1={cutHi}
            y1={y - TICK}
            x2={cutHi}
            y2={y + TICK}
            stroke={memberColor}
            strokeWidth="1.5"
          />
        </>
      ) : null}
      {showWedge ? (
        <path
          d={`M ${cutLo} ${y} L ${cutHi} ${y} L ${TARGET_X} ${TARGET_Y - TARGET_R} Z`}
          fill={memberColor}
          opacity="0.28"
        />
      ) : null}
      {showBeads
        ? members.map((n) => {
            const x = xOf(n, winLo, winHi);
            const tip = tipToward(x, y);
            const active = selected === n;
            return (
              <line
                key={`a-${y}-${n}`}
                x1={x}
                y1={y}
                x2={tip.x}
                y2={tip.y}
                stroke={memberColor}
                strokeWidth={active ? 1.5 : 0.75}
                opacity={active ? 0.95 : 0.5}
                markerEnd={active ? `url(#${markerId})` : undefined}
                pointerEvents="none"
              />
            );
          })
        : null}
      {showBeads
        ? ns.map((n) => {
            const member = memberSet.has(n);
            const inside = n >= washLo && n < washHi;
            if (member) {
              return (
                <BeadMark
                  key={`m-${y}-${n}`}
                  x={xOf(n, winLo, winHi)}
                  y={y}
                  n={n}
                  color={memberColor}
                  active={selected === n}
                  hideLabel={hideActiveLabel && selected === n}
                  labelBelow={outward === "below"}
                  onSelect={onSelect}
                  onHover={onHover}
                />
              );
            }
            if (inside && colorByParity) {
              return (
                <BeadMark
                  key={`i-${y}-${n}`}
                  x={xOf(n, winLo, winHi)}
                  y={y}
                  n={n}
                  color={n % 2 === 0 ? SEA : EMBER}
                  radius={3.5}
                  labelBelow={outward === "below"}
                />
              );
            }
            if (inside && insideColor) {
              return (
                <BeadMark
                  key={`i-${y}-${n}`}
                  x={xOf(n, winLo, winHi)}
                  y={y}
                  n={n}
                  color={n % 2 === 0 ? SEA : insideColor}
                  radius={3.5}
                  labelBelow={outward === "below"}
                />
              );
            }
            return (
              <BeadMark
                key={`p-${y}-${n}`}
                x={xOf(n, winLo, winHi)}
                y={y}
                n={n}
                color={GREY}
                radius={3.5}
                active={selected === n}
                hideLabel={hideActiveLabel && selected === n}
                labelBelow={outward === "below"}
                onHover={hoverPads ? onHover : undefined}
              />
            );
          })
        : null}
      <EndCaption
        x={
          cutHi - cutLo < 56
            ? (cutLo + cutHi) / 2 - 28
            : cutLo
        }
        lineY={y}
        side={inward}
        lines={captions[0]}
      />
      <EndCaption
        x={
          cutHi - cutLo < 56
            ? (cutLo + cutHi) / 2 + 28
            : cutHi
        }
        lineY={y}
        side={inward}
        lines={captions[1]}
      />
    </g>
  );
}

export function EvenBlockStrip({
  view,
  selected = null,
  onSelect,
  onHover,
}: EvenBlockStripProps) {
  const { m, lo, hi, evens, listed, count } = view;
  const targetColor = m % 2 === 1 ? EMBER : SEA;
  const oddParent = oddPreimages(m)[0] ?? null;
  const [evenHover, setEvenHover] = useState<number | null>(null);
  const handleEvenHover = (n: number | null) => {
    setEvenHover(n);
    onHover?.(n);
  };
  const handleOddHover = (n: number | null) => {
    onHover?.(n);
  };
  const liveEven =
    evenHover != null && evenHover % 2 === 0
      ? evenHover
      : selected != null && selected % 2 === 0
        ? selected
        : centerEvenInBlock(view);
  const pad = 5;
  const evenLo = Math.max(0, lo - pad);
  const evenHi = hi + pad;
  const oddWashLo = Math.cbrt(lo);
  const oddWashHi = Math.cbrt(hi);
  const oddPad = 2;
  const oddSpan = Math.max(
    Math.ceil(oddWashHi) + oddPad - (Math.floor(oddWashLo) - oddPad),
    1,
  );
  const oddAnchor = oddParent ?? (oddWashLo + oddWashHi) / 2;
  const oddLo = oddAnchor - oddSpan / 2;
  const oddHi = oddAnchor + oddSpan / 2;
  const evenMarkerId = `even-block-arrow-${m}`;
  const oddMarkerId = `odd-precursor-arrow-${m}`;
  return (
    <div>
      {listed ? null : (
        <p className="text-center text-sm text-muted">
          Too many to draw one bead each. One member:
        </p>
      )}
      <div className="relative">
      <svg viewBox={`0 0 ${WIDTH} ${VIEW_H}`} role="img" className="h-auto w-full">
        <title>{`Even block of ${m}: ${count} evens in [${lo}, ${hi}) map to ${m}`}</title>
        <defs>
          <marker
            id={evenMarkerId}
            markerWidth="5"
            markerHeight="5"
            refX="4"
            refY="2.5"
            orient="auto"
          >
            <path d="M0 0 L5 2.5 L0 5 Z" fill={SEA} />
          </marker>
          <marker
            id={oddMarkerId}
            markerWidth="5"
            markerHeight="5"
            refX="4"
            refY="2.5"
            orient="auto"
          >
            <path d="M0 0 L5 2.5 L0 5 Z" fill={EMBER} />
          </marker>
        </defs>
        <ParityLine
          y={LINE_Y}
          winLo={evenLo}
          winHi={evenHi}
          washLo={lo}
          washHi={hi}
          members={listed ? evens : []}
          memberColor={SEA}
          colorByParity
          outward="above"
          captions={[
            [formatInt(lo), `${formatInt(m)}²`],
            [formatInt(hi), `${formatInt(m + 1)}²`],
          ]}
          selected={liveEven}
          hideActiveLabel
          hoverPads
          showBeads={listed}
          showWedge={!listed}
          markerId={evenMarkerId}
          onSelect={onSelect}
          onHover={handleEvenHover}
        />
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
        <ParityLine
          y={ODD_Y}
          winLo={oddLo}
          winHi={oddHi}
          washLo={oddWashLo}
          washHi={oddWashHi}
          members={oddParent === null ? [] : [oddParent]}
          memberColor={EMBER}
          colorByParity={false}
          outward="below"
          captions={[
            [oddWashLo.toFixed(2), `∛(${formatInt(m)}²)`],
            [oddWashHi.toFixed(2), `∛(${formatInt(m + 1)}²)`],
          ]}
          selected={oddParent}
          hideActiveLabel
          hoverPads={false}
          showBeads
          showWedge={false}
          markerId={oddMarkerId}
          insideColor={EMBER}
          onHover={handleOddHover}
        />
        <text
          x={TARGET_X}
          y={(LINE_Y + TARGET_Y) / 2}
          textAnchor="middle"
          dominantBaseline="middle"
          fill={SEA}
          fontSize="12"
          fontFamily="IBM Plex Mono, monospace"
          paintOrder="stroke"
          stroke="#fffdf7"
          strokeWidth="5"
        >
          even
        </text>
        <text
          x={TARGET_X}
          y={(TARGET_Y + ODD_Y) / 2}
          textAnchor="middle"
          dominantBaseline="middle"
          fill={EMBER}
          fontSize="12"
          fontFamily="IBM Plex Mono, monospace"
          paintOrder="stroke"
          stroke="#fffdf7"
          strokeWidth="5"
        >
          odd
        </text>
      </svg>
      <div
        className="pointer-events-none absolute -translate-y-full"
        style={{
          left: `${(xOf(liveEven, evenLo, evenHi) / WIDTH) * 100}%`,
          top: `${((LINE_Y - 16) / VIEW_H) * 100}%`,
        }}
      >
        <FloorCut compact beadAnchor n={BigInt(liveEven)} />
      </div>
      {oddParent === null ? null : (
        <div
          className="pointer-events-none absolute"
          style={{
            left: `${(xOf(oddParent, oddLo, oddHi) / WIDTH) * 100}%`,
            top: `${((ODD_Y + 16) / VIEW_H) * 100}%`,
          }}
        >
          <FloorCut compact beadAnchor n={BigInt(oddParent)} />
        </div>
      )}
      </div>
    </div>
  );
}
