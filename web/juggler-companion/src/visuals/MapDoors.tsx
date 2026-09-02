import type { ReactNode } from "react";
import { NOTE_ORBIT_3 } from "../juggler/constants";
import { formatInt } from "../juggler/format";
import { bitLength, letterOf } from "../juggler/map";

type MapDoorsProps = {
  highlight?: "even" | "odd" | null;
  states?: readonly bigint[];
  active?: number;
  title?: string;
  controls?: ReactNode;
  axis?: ReactNode;
  player?: ReactNode;
  sparseScale?: boolean;
};

const PLOT_LEFT = 64;
const PLOT_RIGHT = 548;
const PLOT_WIDTH = 572;

function log10Of(state: bigint): number {
  if (state <= 1n) return 0;
  const bits = bitLength(state);
  if (bits <= 53) return Math.log10(Number(state));
  return (bits - 1) * Math.LOG10E * Math.LN2;
}

function plotYLog(log10v: number, lo: number, hi: number, top: number, height: number): number {
  const t = hi === lo ? 0.5 : (log10v - lo) / (hi - lo);
  return top + height - t * height;
}

function niceLogExpDomain(minExp: number, maxExp: number): { lo: number; hi: number } {
  const lo = Math.floor(Math.max(minExp, 0));
  let hi = Math.ceil(Math.max(maxExp, lo + 0.01));
  if (hi <= lo) hi = lo + 1;
  return { lo, hi };
}

function decadeStride(span: number): { stride: number; minors: boolean } {
  if (span <= 16) return { stride: 1, minors: true };
  if (span <= 40) return { stride: 2, minors: false };
  if (span <= 80) return { stride: 5, minors: false };
  if (span <= 200) return { stride: 10, minors: false };
  return { stride: Math.max(20, Math.ceil(span / 14)), minors: false };
}

function logTicks(lo: number, hi: number): { exp: number; major: boolean }[] {
  const { stride, minors } = decadeStride(hi - lo);
  const ticks: { exp: number; major: boolean }[] = [];
  for (let exp = lo; exp <= hi; exp += 1) {
    if (((exp - lo) % stride + stride) % stride === 0) {
      ticks.push({ exp, major: true });
    }
  }
  if (minors) {
    for (let exp = lo; exp < hi; exp += 1) {
      for (const factor of [2, 3, 4, 5, 6, 7, 8, 9]) {
        ticks.push({ exp: exp + Math.log10(factor), major: false });
      }
    }
  }
  return ticks;
}

function sparseExponents(lo: number, hi: number): number[] {
  const marks = [lo, lo + (hi - lo) / 3, lo + (2 * (hi - lo)) / 3, hi];
  return [...new Set(marks.map((exp) => Math.round(exp)))];
}

function TenPow({
  exp,
  prefix = "",
}: {
  exp: number;
  prefix?: string;
}) {
  return (
    <>
      {prefix}10
      <tspan dy="-4" fontSize="7">
        {Math.round(exp)}
      </tspan>
    </>
  );
}

function pointLabel(state: bigint): { kind: "plain"; text: string } | { kind: "pow"; exp: number } {
  const bits = bitLength(state);
  if (bits <= 53) return { kind: "plain", text: state.toString() };
  if (bits <= 64) return { kind: "plain", text: formatInt(state) };
  return { kind: "pow", exp: (bits - 1) * Math.LOG10E * Math.LN2 };
}

function BranchCard({
  kind,
  active,
}: {
  kind: "odd" | "even";
  active: boolean;
}) {
  const odd = kind === "odd";
  const color = odd ? "#c45c26" : "#1f6f6a";
  return (
    <div
      className={`flex flex-1 flex-col items-center justify-center gap-1.5 rounded-2xl border border-line bg-card px-2 py-3 text-center ${
        active ? "" : "opacity-45"
      }`}
    >
      <p className="font-serif text-lg leading-tight" style={{ color }}>
        {odd ? "Odd branch" : "Even branch"}
      </p>
      <p className="font-mono text-2xl leading-none" style={{ color }}>
        {odd ? "O" : "E"}
      </p>
      <p className="text-xs text-muted">
        {odd ? (
          <>
            n odd → ⌊n<sup>3/2</sup>⌋
          </>
        ) : (
          <>
            n even → ⌊n<sup>1/2</sup>⌋
          </>
        )}
      </p>
      <p className="text-4xl leading-none" style={{ color }} aria-hidden>
        {odd ? "⬆" : "⬇"}
      </p>
      <p className="text-xs" style={{ color }}>
        {odd ? "grows" : "shrinks"}
      </p>
    </div>
  );
}

function OrbitPlot({
  states,
  active,
  sparseScale = false,
}: {
  states: readonly bigint[];
  active?: number;
  sparseScale?: boolean;
}) {
  const logs = states.map((state) => log10Of(state));
  const dataMin = Math.min(...logs, 0);
  const dataMax = Math.max(...logs, 1);
  const { lo: min, hi: max } = niceLogExpDomain(dataMin, dataMax);
  const left = PLOT_LEFT;
  const right = PLOT_RIGHT;
  const top = 28;
  const height = 228;
  const ticks = sparseScale
    ? sparseExponents(min, max).map((exp) => ({ exp, major: true }))
    : logTicks(min, max);
  const points = logs.map((value, index) => {
    const x = left + (index * (right - left)) / Math.max(states.length - 1, 1);
    const y = plotYLog(value, min, max, top, height);
    return {
      x,
      y,
      state: states[index],
      letter: index < states.length - 1 ? letterOf(states[index]) : "",
    };
  });
  const shortOrbit = states.length <= 10;
  const showEveryLetter = !sparseScale && states.length <= 22;
  return (
    <svg viewBox={`0 0 ${PLOT_WIDTH} 272`} role="img" className="h-auto w-full">
      <title>Juggler orbit, logarithmic value scale</title>
      {ticks.map((tick) => {
        const y = plotYLog(tick.exp, min, max, top, height);
        return (
          <g key={tick.exp}>
            {sparseScale ? null : (
              <line
                x1={left}
                y1={y}
                x2={right}
                y2={y}
                stroke={tick.major ? "#cfc6b4" : "#e8e2d4"}
                strokeWidth={tick.major ? 1 : 0.75}
              />
            )}
            {tick.major ? (
              <text
                x={left - 8}
                y={y + 3}
                textAnchor="end"
                fill="#5e574c"
                fontFamily="IBM Plex Mono, monospace"
                fontSize="10"
              >
                <TenPow exp={tick.exp} />
              </text>
            ) : null}
          </g>
        );
      })}
      <line x1={left} y1={top} x2={left} y2={top + height} stroke="#d4cbb8" />
      <line x1={left} y1={top + height} x2={right} y2={top + height} stroke="#d4cbb8" />
      <text x={left - 8} y={top - 10} textAnchor="end" fill="#5e574c" fontSize="11">
        value
      </text>
      {points.slice(0, -1).map((point, index) => {
        const next = points[index + 1];
        const odd = point.letter === "O";
        return (
          <line
            key={`seg-${index}`}
            x1={point.x}
            y1={point.y}
            x2={next.x}
            y2={next.y}
            stroke={odd ? "#c45c26" : "#1f6f6a"}
            strokeWidth={active === index || active === index + 1 ? 4 : 2.5}
          />
        );
      })}
      {points.map((point, index) => {
        const odd = point.state % 2n === 1n;
        const isActive = active === index;
        const showLabel =
          active === undefined
            ? shortOrbit || index === 0 || index === points.length - 1
            : isActive;
        const next = points[index + 1];
        const showLetter =
          Boolean(point.letter) &&
          next !== undefined &&
          (showEveryLetter || isActive || index === 0 || index === points.length - 2);
        const letterOdd = point.letter === "O";
        const mx = next === undefined ? point.x : (point.x + next.x) / 2;
        const my = next === undefined ? point.y : (point.y + next.y) / 2;
        return (
          <g key={index}>
            <circle
              cx={point.x}
              cy={point.y}
              r={isActive ? 11 : 8}
              fill={odd ? "#c45c26" : "#1f6f6a"}
              stroke={isActive ? "#1d1914" : "none"}
              strokeWidth={isActive ? 2 : 0}
            />
            {showLabel ? (
              <text
                x={point.x}
                y={point.y - 14}
                textAnchor="middle"
                fill="#1d1914"
                fontFamily="IBM Plex Mono, monospace"
                fontSize="12"
              >
                {(() => {
                  if (!sparseScale) return formatInt(point.state);
                  const label = pointLabel(point.state);
                  return label.kind === "plain" ? (
                    label.text
                  ) : (
                    <TenPow exp={label.exp} prefix="~" />
                  );
                })()}
              </text>
            ) : null}
            {showLetter ? (
              <g>
                <rect
                  x={mx - 5}
                  y={my - 5}
                  width="10"
                  height="10"
                  rx="5"
                  fill={letterOdd ? "#c45c26" : "#1f6f6a"}
                />
                <text
                  x={mx}
                  y={my + 2.5}
                  textAnchor="middle"
                  fill="#fffdf7"
                  fontFamily="IBM Plex Mono, monospace"
                  fontSize="7"
                >
                  {point.letter}
                </text>
              </g>
            ) : null}
          </g>
        );
      })}
    </svg>
  );
}

export function MapDoors({
  highlight = null,
  states = NOTE_ORBIT_3,
  active,
  title,
  controls,
  axis,
  player,
  sparseScale = false,
}: MapDoorsProps) {
  const evenActive = highlight !== "odd";
  const oddActive = highlight !== "even";
  const start = states[0];
  const heading = title ?? (start === undefined ? "Orbit" : `Orbit of ${formatInt(start)}`);
  return (
    <div className="grid gap-3">
      {controls ? (
        <div className="rounded-2xl border border-line bg-paper px-4 py-2.5">{controls}</div>
      ) : null}
      <div className="grid gap-3 lg:grid-cols-[minmax(0,1fr)_9.5rem] lg:items-stretch">
        <div className="rounded-2xl border border-line bg-card px-3 py-3">
          <h3 className="px-1 text-center font-serif text-lg">{heading}</h3>
          <OrbitPlot states={states} active={active} sparseScale={sparseScale} />
          {axis ? (
            <div
              className="-mt-1"
              style={{
                paddingLeft: `${(PLOT_LEFT / PLOT_WIDTH) * 100}%`,
                paddingRight: `${((PLOT_WIDTH - PLOT_RIGHT) / PLOT_WIDTH) * 100}%`,
              }}
            >
              {axis}
            </div>
          ) : null}
          {player ? <div className="pt-2">{player}</div> : null}
        </div>
        <div className="flex flex-col gap-3">
          <BranchCard kind="odd" active={oddActive} />
          <BranchCard kind="even" active={evenActive} />
        </div>
      </div>
    </div>
  );
}
