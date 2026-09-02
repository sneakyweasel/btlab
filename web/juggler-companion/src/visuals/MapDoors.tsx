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
};

function plotValue(state: bigint): number {
  if (state <= 0n) return 1;
  if (bitLength(state) <= 53) return Number(state);
  return 2 ** (bitLength(state) - 1);
}

function plotY(value: number, min: number, max: number, top: number, height: number): number {
  const lo = Math.log(min);
  const hi = Math.log(Math.max(max, min + 1e-9));
  const t = hi === lo ? 0.5 : (Math.log(value) - lo) / (hi - lo);
  return top + height - t * height;
}

function DoorCard({
  kind,
  active,
}: {
  kind: "odd" | "even";
  active: boolean;
}) {
  const odd = kind === "odd";
  const color = odd ? "#c45c26" : "#1f6f6a";
  return (
    <svg viewBox="0 0 264 160" role="img" className="h-auto w-full">
      <title>{odd ? "Odd door grows upward" : "Even door shrinks downward"}</title>
      <rect
        x="1"
        y="1"
        width="262"
        height="158"
        rx="16"
        fill="#fffdf7"
        stroke="#d4cbb8"
        opacity={active ? 1 : 0.45}
      />
      <text x="132" y="32" textAnchor="middle" fill={color} fontFamily="Fraunces, serif" fontSize="20">
        {odd ? "Odd door" : "Even door"}
      </text>
      <text x="132" y="54" textAnchor="middle" fill="#5e574c" fontSize="13" fontFamily="Source Sans 3, sans-serif">
        {odd ? "n odd → floor(n" : "n even → floor(n"}
        <tspan baselineShift="super" fontSize="9">
          {odd ? "3/2" : "1/2"}
        </tspan>
        )
      </text>
      {odd ? (
        <>
          <path d="M132 124 V68" stroke={color} strokeWidth={active ? 6 : 3} opacity={active ? 1 : 0.4} />
          <path
            d="M120 84 L132 64 L144 84"
            fill="none"
            stroke={color}
            strokeWidth="3"
            opacity={active ? 1 : 0.4}
          />
          <text x="132" y="146" textAnchor="middle" fill={color} fontSize="13">
            grows above
          </text>
        </>
      ) : (
        <>
          <path d="M132 64 V120" stroke={color} strokeWidth={active ? 6 : 3} opacity={active ? 1 : 0.4} />
          <path
            d="M120 104 L132 124 L144 104"
            fill="none"
            stroke={color}
            strokeWidth="3"
            opacity={active ? 1 : 0.4}
          />
          <text x="132" y="146" textAnchor="middle" fill={color} fontSize="13">
            shrinks below
          </text>
        </>
      )}
    </svg>
  );
}

function OrbitPlot({
  states,
  active,
}: {
  states: readonly bigint[];
  active?: number;
}) {
  const numbers = states.map((state) => plotValue(state));
  const min = Math.max(1, Math.min(...numbers, 1));
  const max = Math.max(...numbers, 2);
  const left = 48;
  const right = 520;
  const top = 36;
  const height = 220;
  const points = numbers.map((value, index) => {
    const x = left + (index * (right - left)) / Math.max(states.length - 1, 1);
    const y = plotY(value, min, max, top, height);
    return {
      x,
      y,
      state: states[index],
      letter: index < states.length - 1 ? letterOf(states[index]) : "",
    };
  });
  const labelEvery = states.length > 12 ? Math.ceil(states.length / 8) : 1;
  return (
    <svg viewBox="0 0 560 300" role="img" className="h-auto w-full">
      <title>Juggler orbit</title>
      <line x1={left} y1={top} x2={left} y2={top + height} stroke="#d4cbb8" />
      <line x1={left} y1={top + height} x2={right} y2={top + height} stroke="#d4cbb8" />
      <text x={left - 8} y={top + 6} textAnchor="end" fill="#5e574c" fontSize="11">
        value
      </text>
      <text x={(left + right) / 2} y={top + height + 28} textAnchor="middle" fill="#5e574c" fontSize="11">
        step
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
          isActive ||
          index === 0 ||
          index === points.length - 1 ||
          index % labelEvery === 0;
        return (
          <g key={`${index}-${point.state.toString()}`}>
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
                fontSize="11"
              >
                {formatInt(point.state)}
              </text>
            ) : null}
            {point.letter && (states.length <= 12 || isActive) ? (
              <text
                x={(point.x + points[index + 1].x) / 2}
                y={(point.y + points[index + 1].y) / 2 - 8}
                textAnchor="middle"
                fill={point.letter === "O" ? "#c45c26" : "#1f6f6a"}
                fontFamily="IBM Plex Mono, monospace"
                fontSize="12"
              >
                {point.letter}
              </text>
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
}: MapDoorsProps) {
  const evenActive = highlight !== "odd";
  const oddActive = highlight !== "even";
  const start = states[0];
  const heading = title ?? (start === undefined ? "Orbit" : `Orbit of ${formatInt(start)}`);
  return (
    <div className="grid gap-3">
      {controls ? (
        <div className="rounded-2xl border border-line bg-paper px-4 py-3">{controls}</div>
      ) : null}
      <div className="grid gap-3 lg:grid-cols-[minmax(0,1fr)_16.5rem] lg:items-stretch">
        <div className="rounded-2xl border border-line bg-card px-3 py-3">
          <h3 className="px-1 font-serif text-lg">{heading}</h3>
          <OrbitPlot states={states} active={active} />
        </div>
        <div className="flex flex-col gap-3">
          <div className="rounded-2xl border border-line bg-card">
            <DoorCard kind="odd" active={oddActive} />
          </div>
          <div className="rounded-2xl border border-line bg-card">
            <DoorCard kind="even" active={evenActive} />
          </div>
        </div>
      </div>
    </div>
  );
}
