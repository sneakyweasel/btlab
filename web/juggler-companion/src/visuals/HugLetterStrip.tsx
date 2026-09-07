import { hugHeights } from "../juggler/walkCharge";

const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const INK = "#1d1914";
const MUTED = "#5e574c";
const DEEP = "#1f3d34";

const WIDTH = 640;
const HEIGHT = 168;
const LEFT = 36;
const RIGHT = 604;
const CHART_TOP = 18;
const CHART_BOTTOM = 92;
const TILE_Y = 108;
const TILE_H = 22;

type HugLetterStripProps = {
  word: string | null;
};

/**
 * Shipped hug word as a letter strip with height u after each letter.
 * A picture of Theorem 5.4, not a charge integral.
 */
export function HugLetterStrip({ word }: HugLetterStripProps) {
  if (word === null) {
    return (
      <div className="rounded-xl border border-dashed border-line bg-paper/50 px-4 py-8 text-center text-sm text-muted">
        Word not shipped. The site does not generate long hug words.
      </div>
    );
  }

  const heights = hugHeights(word);
  const letters = [...word] as Array<"O" | "E">;
  const hi = Math.max(1.7, ...heights);
  const lo = Math.min(-0.15, ...heights);
  const span = Math.max(hi - lo, 0.5);
  const step = (RIGHT - LEFT) / Math.max(letters.length, 1);

  const yOf = (u: number) => CHART_BOTTOM - ((u - lo) / span) * (CHART_BOTTOM - CHART_TOP);
  const xOf = (index: number) => LEFT + (index / letters.length) * (RIGHT - LEFT);
  const points = heights.map((u, index) => `${xOf(index)},${yOf(u)}`).join(" ");
  const yOne = yOf(1);

  return (
    <svg viewBox={`0 0 ${WIDTH} ${HEIGHT}`} role="img" className="h-auto w-full">
      <title>Hug word letters and height u after each letter</title>
      <line x1={LEFT} y1={CHART_TOP} x2={LEFT} y2={CHART_BOTTOM} stroke="#d4cbb8" />
      <line x1={LEFT} y1={CHART_BOTTOM} x2={RIGHT} y2={CHART_BOTTOM} stroke="#d4cbb8" />
      <line
        x1={LEFT}
        y1={yOne}
        x2={RIGHT}
        y2={yOne}
        stroke={DEEP}
        strokeDasharray="4 3"
        strokeWidth="1"
      />
      <text x={RIGHT} y={yOne - 4} textAnchor="end" fill={DEEP} fontSize="10">
        u = 1
      </text>
      <polyline fill="none" stroke={DEEP} strokeWidth="2" points={points} />
      {heights.map((u, index) => (
        <circle key={`h-${index}`} cx={xOf(index)} cy={yOf(u)} r="2.4" fill={DEEP} />
      ))}
      {letters.map((letter, index) => {
        const x = LEFT + index * step + 2;
        const width = Math.max(step - 4, 8);
        return (
          <g key={`t-${index}`}>
            <rect
              x={x}
              y={TILE_Y}
              width={width}
              height={TILE_H}
              rx="4"
              fill={letter === "O" ? ODD : EVEN}
            />
            <text
              x={x + width / 2}
              y={TILE_Y + 15}
              textAnchor="middle"
              fill="#fffdf7"
              fontSize="11"
              fontFamily="IBM Plex Mono, monospace"
            >
              {letter}
            </text>
          </g>
        );
      })}
      <text x={LEFT} y={HEIGHT - 6} fill={INK} fontSize="11">
        height u after each letter
      </text>
      <text x={RIGHT} y={HEIGHT - 6} textAnchor="end" fill={MUTED} fontSize="11">
        prefix-minimal · no charge
      </text>
    </svg>
  );
}
