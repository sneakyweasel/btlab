import {
  LAMBDA_STAR_STAR_PRINTED,
  PAIR_RECURSION,
  STAR_RECURSION,
  zetaOf,
  type RecursionId,
  type RecursionSpec,
} from "../juggler/contagion";
import { EVEN, mixHex, ODD } from "../juggler/palette";

const INK = "#1d1914";
const MUTED = "#5e574c";
const WIDTH = 720;
const HEIGHT = 196;
const LAM_MAX = 0.55;
const Y_LO = -0.18;
const Y_HI = 0.4;

const STAR_COLOR = EVEN;
const PAIR_COLOR = mixHex(EVEN, ODD, 0.55);

type ZetaPlotProps = {
  recursion: RecursionId;
  onSelect: (id: RecursionId) => void;
};

function samples(spec: RecursionSpec): string {
  const points: string[] = [];
  for (let i = 0; i <= 80; i += 1) {
    const lam = (i / 80) * LAM_MAX;
    points.push(`${i ? "L" : "M"}${xOf(lam)},${yOf(zetaOf(spec.terms, lam))}`);
  }
  return points.join(" ");
}

function xOf(lam: number): number {
  const padL = 48;
  const inner = WIDTH - padL - 16;
  return padL + (lam / LAM_MAX) * inner;
}

function yOf(value: number): number {
  const padT = 14;
  const padB = 32;
  const inner = HEIGHT - padT - padB;
  return padT + (1 - (value - Y_LO) / (Y_HI - Y_LO)) * inner;
}

export function ZetaPlot({ recursion, onSelect }: ZetaPlotProps) {
  const selected = recursion === "star" ? STAR_RECURSION : PAIR_RECURSION;
  const other = recursion === "star" ? PAIR_RECURSION : STAR_RECURSION;
  const selectedColor = recursion === "star" ? STAR_COLOR : PAIR_COLOR;
  const otherColor = recursion === "star" ? PAIR_COLOR : STAR_COLOR;

  return (
    <figure className="space-y-2">
      <svg
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        className="h-auto w-full"
        role="img"
        aria-label="Zeta of lambda for the two three-source recursions"
      >
        <title>ζ(λ) = Σ c_i t_i^λ − 1. Roots are λ* and λ_pair</title>
        <line
          x1={xOf(0)}
          x2={xOf(LAM_MAX)}
          y1={yOf(0)}
          y2={yOf(0)}
          stroke="#d4cbb8"
        />
        <path d={samples(other)} fill="none" stroke={otherColor} strokeWidth="1.4" opacity="0.35" />
        <path d={samples(selected)} fill="none" stroke={selectedColor} strokeWidth="2.4" />
        <RootTick
          spec={STAR_RECURSION}
          color={STAR_COLOR}
          active={recursion === "star"}
          onSelect={() => onSelect("star")}
        />
        <RootTick
          spec={PAIR_RECURSION}
          color={PAIR_COLOR}
          active={recursion === "pair"}
          onSelect={() => onSelect("pair")}
        />
        <line
          x1={xOf(LAMBDA_STAR_STAR_PRINTED)}
          x2={xOf(LAMBDA_STAR_STAR_PRINTED)}
          y1={14}
          y2={HEIGHT - 32}
          stroke={MUTED}
          strokeDasharray="2 3"
          opacity="0.45"
        />
        <text
          x={xOf(LAMBDA_STAR_STAR_PRINTED) - 6}
          y={26}
          textAnchor="end"
          fill={MUTED}
          fontSize="10"
          fontFamily="IBM Plex Mono, monospace"
        >
          paper λ** later
        </text>
        <circle
          cx={xOf(selected.printed)}
          cy={yOf(0)}
          r="5"
          fill={selectedColor}
        />
        <text x={36} y={yOf(0) + 3} textAnchor="end" fill={MUTED} fontSize="10">
          0
        </text>
        <text x={WIDTH - 16} y={HEIGHT - 8} textAnchor="end" fill={MUTED} fontSize="10">
          λ
        </text>
        <text x={36} y={18} textAnchor="end" fill={INK} fontSize="10">
          ζ
        </text>
      </svg>
      <figcaption className="text-xs text-muted">
        {selected.name} is the root of {selected.equation}. Official λ** =
        0.4926 uses later V_k words, not these three sources.
      </figcaption>
    </figure>
  );
}

function RootTick({
  spec,
  color,
  active,
  onSelect,
}: {
  spec: RecursionSpec;
  color: string;
  active: boolean;
  onSelect: () => void;
}) {
  const x = xOf(spec.printed);
  return (
    <g
      role="button"
      tabIndex={0}
      className="cursor-pointer"
      onClick={onSelect}
      onKeyDown={(event) => {
        if (event.key === "Enter" || event.key === " ") {
          event.preventDefault();
          onSelect();
        }
      }}
    >
      <line
        x1={x}
        x2={x}
        y1={14}
        y2={HEIGHT - 32}
        stroke={color}
        strokeDasharray="4 3"
        strokeWidth={active ? 2 : 1}
        opacity={active ? 1 : 0.45}
      />
      <text
        x={spec.id === "star" ? x - 6 : x + 6}
        y={HEIGHT - 10}
        textAnchor={spec.id === "star" ? "end" : "start"}
        fill={active ? INK : MUTED}
        fontSize="10"
        fontFamily="IBM Plex Mono, monospace"
      >
        {spec.name} {spec.printed.toFixed(4)}
      </text>
    </g>
  );
}
