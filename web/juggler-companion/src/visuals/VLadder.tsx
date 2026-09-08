import {
  LADDER_RUNGS,
  type LadderId,
  type LadderRung,
} from "../juggler/contagion";
import { EVEN, mixHex, ODD } from "../juggler/palette";

const INK = "#1d1914";
const MUTED = "#5e574c";
const WIDTH = 720;
const HEIGHT = 200;
const LAM_LO = 0.36;
const LAM_HI = 0.51;
const SOLID = LADDER_RUNGS.filter((rung) => !rung.muted);
const OFFICIAL = EVEN;
const MUTED_COLOR = mixHex(EVEN, ODD, 0.55);

type VLadderProps = {
  selected: LadderId;
  onSelect: (id: LadderId) => void;
};

function xOf(index: number): number {
  const padL = 48;
  const inner = WIDTH - padL - 20;
  return padL + (index / (LADDER_RUNGS.length - 1)) * inner;
}

function yOf(lam: number): number {
  const padT = 16;
  const padB = 36;
  return padT + (1 - (lam - LAM_LO) / (LAM_HI - LAM_LO)) * (HEIGHT - padT - padB);
}

export function VLadder({ selected, onSelect }: VLadderProps) {
  const path = SOLID.map((rung, index) => {
    const x = xOf(LADDER_RUNGS.indexOf(rung));
    return `${index ? "L" : "M"}${x},${yOf(rung.printed)}`;
  }).join(" ");

  return (
    <figure className="space-y-2">
      <svg
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        className="h-auto w-full"
        role="img"
        aria-label="Printed contagion exponents from lambda-star to lambda-star-star and the ideal ceiling"
      >
        <title>Paper C Theorem 5.3: V-ladder of printed roots</title>
        <line
          x1={xOf(0)}
          x2={xOf(LADDER_RUNGS.length - 1)}
          y1={yOf(0.4926)}
          y2={yOf(0.4926)}
          stroke={OFFICIAL}
          strokeDasharray="3 3"
          opacity="0.35"
        />
        <path d={path} fill="none" stroke={OFFICIAL} strokeWidth="2.2" />
        {LADDER_RUNGS.map((rung, index) => (
          <RungMark
            key={rung.id}
            rung={rung}
            index={index}
            selected={selected === rung.id}
            onSelect={() => onSelect(rung.id)}
          />
        ))}
        <text x={36} y={yOf(0.3774) + 3} textAnchor="end" fill={MUTED} fontSize="10">
          0.38
        </text>
        <text x={36} y={yOf(0.4926) + 3} textAnchor="end" fill={MUTED} fontSize="10">
          0.49
        </text>
      </svg>
      <figcaption className="text-xs text-muted">
        Printed roots. The last solid rung is official λ** = 0.4926 (V6).
        The open mark is the depth-two ideal ceiling 0.4927, not a proved
        word list. Later V_k only nibble the last 0.0001.
      </figcaption>
    </figure>
  );
}

function RungMark({
  rung,
  index,
  selected,
  onSelect,
}: {
  rung: LadderRung;
  index: number;
  selected: boolean;
  onSelect: () => void;
}) {
  const x = xOf(index);
  const y = yOf(rung.printed);
  const color = rung.muted ? MUTED_COLOR : OFFICIAL;
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
      {rung.muted ? (
        <circle
          cx={x}
          cy={y}
          r={selected ? 6 : 5}
          fill="#fffdf7"
          stroke={color}
          strokeWidth={selected ? 2.4 : 1.6}
        />
      ) : (
        <circle cx={x} cy={y} r={selected ? 6 : 4.5} fill={color} />
      )}
      <text
        x={x}
        y={HEIGHT - 10}
        textAnchor="middle"
        fill={selected ? INK : MUTED}
        fontSize="10"
        fontFamily="IBM Plex Mono, monospace"
      >
        {rung.name}
      </text>
    </g>
  );
}
