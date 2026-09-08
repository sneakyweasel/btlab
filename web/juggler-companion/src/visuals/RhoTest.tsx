import {
  RHO_WORDS,
  rhoIdeal,
  rhoOfWord,
  type RhoWord,
} from "../juggler/contagion";
import { EVEN, ODD } from "../juggler/palette";

const INK = "#1d1914";
const MUTED = "#5e574c";
const WIDTH = 720;
const HEIGHT = 168;

type RhoTestProps = {
  selected: string;
  onSelect: (word: string) => void;
};

function xOf(rho: number): number {
  const padL = 36;
  const inner = WIDTH - padL - 24;
  return padL + rho * inner;
}

const STACK: Record<string, number> = {
  OEOEE: -16,
  OOEEE: 16,
};

export function RhoTest({ selected, onSelect }: RhoTestProps) {
  const half = xOf(0.5);
  const lo = xOf(0);
  const hi = xOf(1);
  return (
    <figure className="space-y-2">
      <svg
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        className="h-auto w-full"
        role="img"
        aria-label="Production words on the rho axis against the one-half fiber test"
      >
        <title>Proposition 5.13: ideal share exactly when ρ_w ≤ 1/2</title>
        <rect x={lo} y="58" width={half - lo} height="20" fill={EVEN} opacity="0.16" rx="4" />
        <rect x={half} y="58" width={hi - half} height="20" fill={ODD} opacity="0.16" rx="4" />
        <line x1={lo} x2={hi} y1="68" y2="68" stroke="#d4cbb8" />
        <line x1={half} x2={half} y1="44" y2="92" stroke={INK} strokeWidth="1.4" />
        <text
          x={half}
          y="38"
          textAnchor="middle"
          fill={INK}
          fontSize="11"
          fontFamily="IBM Plex Mono, monospace"
        >
          ρ = 1/2
        </text>
        <text x={lo} y="112" fill={MUTED} fontSize="10">
          0
        </text>
        <text x={hi} y="112" textAnchor="end" fill={MUTED} fontSize="10">
          1
        </text>
        <text x={(lo + half) / 2} y="154" textAnchor="middle" fill={EVEN} fontSize="11">
          ideal share available
        </text>
        <text x={(half + hi) / 2} y="154" textAnchor="middle" fill={ODD} fontSize="11">
          lossy
        </text>
        {RHO_WORDS.map((entry) => (
          <WordMark
            key={entry.word}
            entry={entry}
            selected={selected === entry.word}
            onSelect={() => onSelect(entry.word)}
          />
        ))}
      </svg>
      <figcaption className="text-xs text-muted">
        {"Formula (5.7): ρ_w = 2^{-a} (3/2)^b. Localized parity needs |I| ≥ P^{1/2}, which is ρ_w ≤ 1/2. OE is the one lossy production in the three sources. OOEE / OOEEE are the Proposition 5.13 examples, not Paper C Theorem 5.3 terms."}
      </figcaption>
    </figure>
  );
}

function WordMark({
  entry,
  selected,
  onSelect,
}: {
  entry: RhoWord;
  selected: boolean;
  onSelect: () => void;
}) {
  const rho = rhoOfWord(entry.word);
  const x = xOf(rho);
  const lift = STACK[entry.word] ?? 0;
  const color = rhoIdeal(rho) ? EVEN : ODD;
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
        y1={68}
        y2={68 + lift}
        stroke={color}
        opacity="0.45"
      />
      <circle
        cx={x}
        cy={68 + lift}
        r={selected ? 6 : 4.5}
        fill={entry.appendix ? "#fffdf7" : color}
        stroke={color}
        strokeWidth={entry.appendix || selected ? 2 : 0}
      />
      {selected ? (
        <text
          x={x}
          y={lift < 0 ? 24 : 132}
          textAnchor="middle"
          fill={INK}
          fontSize="10"
          fontFamily="IBM Plex Mono, monospace"
        >
          {entry.short}
        </text>
      ) : null}
    </g>
  );
}
