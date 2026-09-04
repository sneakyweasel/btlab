import { useLayoutEffect, useRef, useState, type ReactNode } from "react";
import { NOTE_TRAJECTORY_3 } from "../juggler/constants";
import { formatInt, log10Of } from "../juggler/format";
import { bitLength, letterOf } from "../juggler/map";
import { EMBER } from "../juggler/palette";

type MapDoorsProps = {
  highlight?: "even" | "odd" | null;
  states?: readonly bigint[];
  active?: number;
  title?: string;
  controls?: ReactNode;
  axis?: ReactNode;
  player?: ReactNode;
  sparseScale?: boolean;
  stepComputation?: ReactNode;
  side?: ReactNode;
  fillPlot?: boolean;
  envelopeLogs?: readonly number[];
  onSelect?: (index: number) => void;
};

const PLOT_LEFT = 64;
const PLOT_RIGHT = 548;
const PLOT_WIDTH = 572;
const PLOT_HEIGHT = 272;
const PLOT_TOP = 28;
const PLOT_BOTTOM = 16;

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
  computation,
}: {
  kind: "odd" | "even";
  active: boolean;
  computation?: ReactNode;
}) {
  const odd = kind === "odd";
  const color = odd ? "#c45c26" : "#1f6f6a";
  const showWork = active && computation != null;
  return (
    <div
      className={`flex flex-1 flex-col items-center justify-center gap-1 rounded-2xl border border-line bg-card px-2 py-2 text-center ${
        active ? "" : "opacity-45"
      }`}
    >
      <p className="font-serif text-base leading-tight" style={{ color }}>
        {odd ? "Odd" : "Even"}
        <span className="ml-1 font-mono text-lg">{odd ? "O" : "E"}</span>
      </p>
      {showWork ? (
        computation
      ) : (
        <>
          <p className="text-xs text-muted">
            {odd ? (
              <>
                n odd → ⌊n√n⌋
              </>
            ) : (
              <>
                n even → ⌊√n⌋
              </>
            )}
          </p>
          <p className="text-3xl leading-none" style={{ color }} aria-hidden>
            {odd ? "⬆" : "⬇"}
          </p>
          <p className="text-xs" style={{ color }}>
            {odd ? "grows" : "shrinks"}
          </p>
        </>
      )}
    </div>
  );
}

function TrajectoryPlot({
  states,
  active,
  sparseScale = false,
  fill = false,
  envelopeLogs,
  onSelect,
}: {
  states: readonly bigint[];
  active?: number;
  sparseScale?: boolean;
  fill?: boolean;
  envelopeLogs?: readonly number[];
  onSelect?: (index: number) => void;
}) {
  const hostRef = useRef<HTMLDivElement>(null);
  const [viewH, setViewH] = useState(PLOT_HEIGHT);
  useLayoutEffect(() => {
    if (!fill) {
      setViewH(PLOT_HEIGHT);
      return;
    }
    const el = hostRef.current;
    if (!el) return;
    const sync = () => {
      const width = el.clientWidth;
      const height = el.clientHeight;
      if (width <= 0 || height <= 0) return;
      setViewH(Math.max(PLOT_HEIGHT, (height / width) * PLOT_WIDTH));
    };
    sync();
    const observer = new ResizeObserver(sync);
    observer.observe(el);
    return () => observer.disconnect();
  }, [fill]);
  const logs = states.map((state) => log10Of(state));
  const left = PLOT_LEFT;
  const right = PLOT_RIGHT;
  const top = PLOT_TOP;
  const height = viewH - PLOT_TOP - PLOT_BOTTOM;
  const ceilingLogs =
    envelopeLogs && envelopeLogs.length === logs.length
      ? envelopeLogs.map((ceiling, index) =>
          Number.isFinite(ceiling) ? Math.max(ceiling, logs[index]) : logs[index],
        )
      : null;
  const dataMin = Math.min(...logs, 0);
  const dataMax = Math.max(...logs, ...(ceilingLogs ?? []), 1);
  const { lo: min, hi: max } = niceLogExpDomain(dataMin, dataMax);
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
  const shortTrajectory = states.length <= 10;
  const [hover, setHover] = useState<number | null>(null);
  const hoverPoint = hover === null ? null : points[hover];
  const svg = (
    <svg
      viewBox={`0 0 ${PLOT_WIDTH} ${viewH}`}
      role="img"
      className={fill ? "h-full w-full" : "h-auto w-full"}
    >
      <title>Juggler trajectory, logarithmic value scale</title>
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
      {ceilingLogs
        ? (() => {
            const upper = ceilingLogs.map((ceiling, index) => ({
              x: points[index].x,
              y: plotYLog(ceiling, min, max, top, height),
            }));
            const band = [
              ...upper.map((point) => `${point.x},${point.y}`),
              ...points.toReversed().map((point) => `${point.x},${point.y}`),
            ].join(" ");
            const mark = active !== undefined && active >= 0 && active < upper.length ? active : upper.length - 1;
            const tag = upper[mark];
            return (
              <g aria-hidden>
                <polygon points={band} fill={EMBER} opacity="0.16" />
                <polyline
                  points={upper.map((point) => `${point.x},${point.y}`).join(" ")}
                  fill="none"
                  stroke={EMBER}
                  strokeDasharray="7 6"
                  strokeWidth="2"
                />
                {tag ? (
                  <text
                    x={tag.x}
                    y={Math.max(tag.y - 10, top + 10)}
                    textAnchor={tag.x > right - 50 ? "end" : "middle"}
                    fill={EMBER}
                    fontSize="11"
                  >
                    envelope
                  </text>
                ) : null}
              </g>
            );
          })()
        : null}
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
            ? shortTrajectory || index === 0 || index === points.length - 1
            : isActive;
        return (
          <g
            key={index}
            role={onSelect ? "button" : undefined}
            tabIndex={onSelect ? 0 : undefined}
            aria-current={isActive ? "step" : undefined}
            aria-label={`Step ${index}, value ${formatInt(point.state)}`}
            onPointerEnter={() => setHover(index)}
            onPointerLeave={() => setHover(null)}
            onClick={() => onSelect?.(index)}
            onKeyDown={(event) => {
              if (!onSelect) return;
              if (event.key === "Enter" || event.key === " ") {
                event.preventDefault();
                onSelect(index);
              }
            }}
            style={{ cursor: onSelect ? "pointer" : "default" }}
          >
            <title>{formatInt(point.state)}</title>
            <circle cx={point.x} cy={point.y} r={Math.max(isActive ? 11 : 8, 10)} fill="transparent" />
            <circle
              cx={point.x}
              cy={point.y}
              r={isActive ? 11 : 8}
              fill={odd ? "var(--color-odd)" : "var(--color-even)"}
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
          </g>
        );
      })}
      {hoverPoint ? (
        <text
          x={hoverPoint.x}
          y={hoverPoint.y - 16}
          textAnchor={hoverPoint.x > PLOT_RIGHT - 60 ? "end" : hoverPoint.x < PLOT_LEFT + 60 ? "start" : "middle"}
          fill="#1d1914"
          fontFamily="IBM Plex Mono, monospace"
          fontSize="12"
          paintOrder="stroke"
          stroke="#fffdf7"
          strokeWidth="4"
          pointerEvents="none"
        >
          {formatInt(hoverPoint.state)}
        </text>
      ) : null}
    </svg>
  );
  if (!fill) return svg;
  return (
    <div ref={hostRef} className="h-full min-h-0 w-full">
      {svg}
    </div>
  );
}

export function MapDoors({
  highlight = null,
  states = NOTE_TRAJECTORY_3,
  active,
  title,
  controls,
  axis,
  player,
  sparseScale = false,
  stepComputation,
  side,
  fillPlot = false,
  envelopeLogs,
  onSelect,
}: MapDoorsProps) {
  const evenActive = highlight !== "odd";
  const oddActive = highlight !== "even";
  const start = states[0];
  const heading = title ?? (start === undefined ? "Trajectory" : `Trajectory of ${formatInt(start)}`);
  return (
    <div className="grid gap-3">
      {controls ? (
        <div className="rounded-2xl border border-line bg-paper px-4 py-2.5">{controls}</div>
      ) : null}
      <div className="grid gap-3 sm:grid-cols-[minmax(0,1fr)_auto] sm:items-stretch">
        <div
          className={`rounded-2xl border border-line bg-card px-3 py-3 ${
            fillPlot ? "flex h-full min-h-[28rem] flex-col" : ""
          }`}
        >
          <h3 className="shrink-0 px-1 text-center font-serif text-lg">{heading}</h3>
          <div className={fillPlot ? "min-h-0 flex-1" : undefined}>
            <TrajectoryPlot
              states={states}
              active={active}
              sparseScale={sparseScale}
              fill={fillPlot}
              envelopeLogs={envelopeLogs}
              onSelect={onSelect}
            />
          </div>
          {axis ? (
            <div
              className="-mt-1 shrink-0"
              style={{
                paddingLeft: `${(PLOT_LEFT / PLOT_WIDTH) * 100}%`,
                paddingRight: `${((PLOT_WIDTH - PLOT_RIGHT) / PLOT_WIDTH) * 100}%`,
              }}
            >
              {axis}
            </div>
          ) : null}
          {player ? <div className="shrink-0 pt-2">{player}</div> : null}
        </div>
        <div
          className={`flex min-w-0 flex-col self-stretch ${
            fillPlot ? "h-full sm:w-[18rem]" : side ? "sm:w-[18rem]" : "justify-center gap-3 sm:w-[15rem]"
          }`}
        >
          {side ?? (
            <>
              <BranchCard
                kind="odd"
                active={oddActive}
                computation={highlight === "odd" ? stepComputation : undefined}
              />
              <BranchCard
                kind="even"
                active={evenActive}
                computation={highlight === "even" ? stepComputation : undefined}
              />
            </>
          )}
        </div>
      </div>
    </div>
  );
}
