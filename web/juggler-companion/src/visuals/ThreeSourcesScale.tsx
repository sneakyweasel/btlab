import {
  coeffOf,
  type RecursionId,
  type SourceBand,
  type SourceId,
  type ThreeSourcesView,
} from "../juggler/contagion";
import { EVEN, mixHex, ODD } from "../juggler/palette";

const INK = "#1d1914";
const MUTED = "#5e574c";
const WASH = "#e8e2d4";
const WIDTH = 720;
const HEIGHT = 276;

export const SOURCE_COLORS: Record<SourceId, string> = {
  1: EVEN,
  2: mixHex(EVEN, ODD, 0.4),
  3: ODD,
};

const CUTS: { key: keyof ThreeSourcesView["cuts"]; tex: string }[] = [
  { key: "x316", tex: "3/16" },
  { key: "x14", tex: "1/4" },
  { key: "x38", tex: "3/8" },
  { key: "sqrt", tex: "√x" },
  { key: "x34", tex: "3/4" },
  { key: "x", tex: "x" },
];

type ScaleProps = {
  view: ThreeSourcesView;
  recursion: RecursionId;
  selected: SourceId;
  onSelect: (id: SourceId) => void;
};

function formatCut(value: number): string {
  if (value >= 1000) {
    return value.toLocaleString("en-US", { maximumFractionDigits: 0 });
  }
  const nearest = Math.round(value);
  if (Math.abs(value - nearest) < 1e-9 * Math.max(1, value)) {
    return String(nearest);
  }
  return value >= 10 ? value.toFixed(1) : value.toFixed(2);
}

function coeffLabel(value: number): string {
  if (value === 0) return "0";
  if (Math.abs(value - 1) < 1e-12) return "1";
  if (Math.abs(value - 1 / 3) < 1e-12) return "1/3";
  if (Math.abs(value - 1 / 9) < 1e-12) return "1/9";
  if (Math.abs(value - 2 / 9) < 1e-12) return "2/9";
  return value.toFixed(3);
}

function scaleLabel(value: number): string {
  if (Math.abs(value - 1 / 2) < 1e-12) return "t/2";
  if (Math.abs(value - 3 / 8) < 1e-12) return "3t/8";
  if (Math.abs(value - 3 / 4) < 1e-12) return "3t/4";
  return value.toFixed(3);
}

export function ThreeSourcesScale({
  view,
  recursion,
  selected,
  onSelect,
}: ScaleProps) {
  const logLo = Math.log(view.cuts.x316);
  const logHi = Math.log(view.cuts.x);
  const padL = 18;
  const padR = 18;
  const span = WIDTH - padL - padR;
  const xOf = (value: number) =>
    padL + ((Math.log(value) - logLo) / (logHi - logLo)) * span;
  const axisY = 242;
  const imageY = 196;
  const rows: { id: SourceId; labelY: number; barY: number }[] = [
    { id: 1, labelY: 18, barY: 26 },
    { id: 2, labelY: 70, barY: 78 },
    { id: 3, labelY: 122, barY: 130 },
  ];

  return (
    <figure className="space-y-2">
      <svg
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        className="h-auto w-full"
        role="img"
        aria-label="Log scale of the three contagion parent intervals and their common image wash"
      >
        <title>Section 5.1: three disjoint sources in (√x, x]</title>
        <rect
          x={xOf(view.cuts.sqrt)}
          y={imageY}
          width={xOf(view.cuts.x) - xOf(view.cuts.sqrt)}
          height="28"
          fill={WASH}
          rx="4"
        />
        <text
          x={(xOf(view.cuts.sqrt) + xOf(view.cuts.x)) / 2}
          y={imageY + 18}
          textAnchor="middle"
          fill={INK}
          fontSize="12"
          fontFamily="IBM Plex Mono, monospace"
        >
          images (√x, x]
        </text>
        {rows.map((row) => {
          const source = view.sources[row.id - 1];
          const coeff = coeffOf(source, recursion);
          const active = coeff > 0;
          const isSelected = selected === source.id;
          const color = SOURCE_COLORS[source.id];
          const x1 = xOf(source.parentLo);
          const x2 = xOf(source.parentHi);
          return (
            <g
              key={source.id}
              role="button"
              tabIndex={0}
              className="cursor-pointer"
              onClick={() => onSelect(source.id)}
              onKeyDown={(event) => {
                if (event.key === "Enter" || event.key === " ") {
                  event.preventDefault();
                  onSelect(source.id);
                }
              }}
            >
              <text
                x={padL}
                y={row.labelY}
                fill={active ? INK : MUTED}
                fontSize="11"
                fontFamily="IBM Plex Mono, monospace"
              >
                {source.id}. {source.label} · {coeffLabel(coeff)} at {scaleLabel(source.scale)}
              </text>
              <rect
                x={x1}
                y={row.barY}
                width={Math.max(2, x2 - x1)}
                height="22"
                fill={color}
                fillOpacity={active ? (isSelected ? 0.28 : 0.16) : 0.06}
                stroke={color}
                strokeWidth={isSelected ? 2.4 : 1.2}
                strokeDasharray={active ? undefined : "4 3"}
                rx="4"
              />
            </g>
          );
        })}
        <line
          x1={padL}
          x2={WIDTH - padR}
          y1={axisY}
          y2={axisY}
          stroke="#d4cbb8"
        />
        {CUTS.map((cut) => {
          const value = view.cuts[cut.key];
          const x = xOf(value);
          const atImage = cut.key === "sqrt" || cut.key === "x";
          const anchor =
            cut.key === "x316" ? "start" : cut.key === "x" ? "end" : "middle";
          return (
            <g key={cut.key}>
              <line
                x1={x}
                x2={x}
                y1={atImage ? imageY : 24}
                y2={axisY + 4}
                stroke="#d4cbb8"
                strokeDasharray={atImage ? undefined : "2 3"}
              />
              <text
                x={x}
                y={axisY + 16}
                textAnchor={anchor}
                fill={MUTED}
                fontSize="10"
                fontFamily="IBM Plex Mono, monospace"
              >
                {cut.tex}
              </text>
              <text
                x={x}
                y={axisY + 28}
                textAnchor={anchor}
                fill={INK}
                fontSize="10"
                fontFamily="IBM Plex Mono, monospace"
              >
                {formatCut(value)}
              </text>
            </g>
          );
        })}
      </svg>
      <figcaption className="text-xs text-muted">
        Log axis; ticks are exponents of x. Parent brackets sit at the paper
        cuts; every family lands in the same image wash. Schematic geometry —
        no finite g_A is computed.
      </figcaption>
    </figure>
  );
}

type StacksProps = {
  view: ThreeSourcesView;
  recursion: RecursionId;
  selected: SourceId;
  onSelect: (id: SourceId) => void;
};

export function ThreeSourcesStacks({
  view,
  recursion,
  selected,
  onSelect,
}: StacksProps) {
  return (
    <div className="grid gap-3 sm:grid-cols-3">
      {view.sources.map((source) => (
        <SourceStack
          key={source.id}
          source={source}
          coeff={coeffOf(source, recursion)}
          selected={selected === source.id}
          onSelect={() => onSelect(source.id)}
        />
      ))}
    </div>
  );
}

function SourceStack({
  source,
  coeff,
  selected,
  onSelect,
}: {
  source: SourceBand;
  coeff: number;
  selected: boolean;
  onSelect: () => void;
}) {
  const color = SOURCE_COLORS[source.id];
  const height = Math.max(2, 72 * coeff);
  return (
    <button
      type="button"
      onClick={onSelect}
      className={`rounded-xl border px-3 py-3 text-left ${
        selected ? "border-deep bg-card" : "border-line bg-card"
      }`}
    >
      <div className="text-xs uppercase tracking-wide text-muted">
        {source.id}. {source.label}
      </div>
      <div className="mt-3 flex h-20 items-end">
        <div
          className="w-10 rounded-t"
          style={{ height, background: color, opacity: coeff > 0 ? 0.85 : 0.2 }}
        />
        <div className="ml-3 font-mono text-lg text-ink">{coeffLabel(coeff)}</div>
      </div>
      <div className="mt-2 text-xs text-muted">{source.hint}</div>
    </button>
  );
}
