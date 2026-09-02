type CycleNecklaceProps = {
  word: string;
  shift?: number;
  minIndex?: number;
  onSelectIndex?: (index: number) => void;
};

function originalIndex(minIndex: number, offset: number, length: number): number {
  return (((minIndex + offset) % length) + length) % length;
}

export function CycleNecklace({
  word,
  shift = 0,
  minIndex,
  onSelectIndex,
}: CycleNecklaceProps) {
  const n = Math.max(word.length, 1);
  const cx = 180;
  const cy = 158;
  const r = 92;
  const atMin =
    minIndex !== undefined && (((shift % n) + n) % n === minIndex);
  const firstEvenOffset =
    minIndex === undefined ? -1 : rotateFrom(word, minIndex).indexOf("E");
  const firstPeak =
    minIndex !== undefined && firstEvenOffset >= 0
      ? originalIndex(minIndex, firstEvenOffset, word.length)
      : -1;
  const lastPeak =
    minIndex !== undefined && word.length > 0
      ? originalIndex(minIndex, word.length - 1, word.length)
      : -1;
  const firstLaunch =
    minIndex !== undefined && word.length > 1
      ? originalIndex(minIndex, 1, word.length)
      : -1;

  function xy(index: number): { x: number; y: number } {
    const angle = beadAngle(index, shift, n);
    return { x: cx + r * Math.cos(angle), y: cy + r * Math.sin(angle) };
  }

  return (
    <svg viewBox="0 0 360 300" role="img" className="mx-auto h-auto w-full max-w-sm">
      <title>Cycle itinerary as a rotatable necklace</title>
      <circle cx={cx} cy={cy} r={r} fill="none" stroke="#d4cbb8" strokeWidth="2" />
      {word.length > 1
        ? Array.from(word).map((letter, index) => {
            const next = (index + 1) % word.length;
            const a0 = beadAngle(index, shift, n);
            const a1 = beadAngle(next, shift, n);
            const launchArc = minIndex !== undefined && index === minIndex;
            return (
              <path
                key={`arc-${index}`}
                d={arcPath(cx, cy, r, a0, a1)}
                fill="none"
                stroke={letter === "O" ? "#c45c26" : "#1f6f6a"}
                strokeWidth={launchArc ? 5 : 3}
                strokeLinecap="round"
                opacity={launchArc ? 0.85 : 0.35}
              />
            );
          })
        : null}
      {minIndex !== undefined && lastPeak >= 0 && firstLaunch >= 0 ? (
        <path
          d={`M ${xy(lastPeak).x} ${xy(lastPeak).y} L ${xy(minIndex).x} ${xy(minIndex).y} L ${xy(firstLaunch).x} ${xy(firstLaunch).y}`}
          fill="none"
          stroke="#1d1914"
          strokeWidth="2.2"
          strokeLinejoin="round"
          opacity={atMin ? 0.9 : 0.35}
        />
      ) : null}
      <polygon
        points={`${cx},${cy - r - 30} ${cx - 7},${cy - r - 16} ${cx + 7},${cy - r - 16}`}
        fill="#1f3d34"
      />
      <text
        x={cx}
        y={cy - r - 36}
        textAnchor="middle"
        fill="#1f3d34"
        fontFamily="Source Sans 3, sans-serif"
        fontSize="12"
      >
        {atMin ? "CycleMin cut" : "this spelling"}
      </text>
      {Array.from(word).map((letter, index) => {
        const angle = beadAngle(index, shift, n);
        const x = cx + r * Math.cos(angle);
        const y = cy + r * Math.sin(angle);
        const isMin = minIndex === index;
        const odd = letter === "O";
        const label = beadCaption(index, {
          minIndex,
          firstPeak,
          lastPeak,
          firstLaunch,
          atMin,
        });
        const labelR = r + 34;
        const lx = cx + labelR * Math.cos(angle);
        const ly = cy + labelR * Math.sin(angle);
        return (
          <g key={`${letter}-${index}`}>
            <circle
              cx={x}
              cy={y}
              r={isMin ? 20 : 16}
              fill={odd ? "#c45c26" : "#1f6f6a"}
              stroke={isMin ? "#1d1914" : "none"}
              strokeWidth={isMin ? 3 : 0}
              className={onSelectIndex ? "cursor-pointer" : undefined}
              onClick={onSelectIndex ? () => onSelectIndex(index) : undefined}
            />
            <text
              x={x}
              y={y + 5}
              textAnchor="middle"
              fill="#fffdf7"
              fontFamily="IBM Plex Mono, monospace"
              fontSize="14"
              className={onSelectIndex ? "cursor-pointer" : undefined}
              onClick={onSelectIndex ? () => onSelectIndex(index) : undefined}
            >
              {letter}
            </text>
            {label ? (
              <text
                x={lx}
                y={ly + 4}
                textAnchor="middle"
                fill="#5e574c"
                fontFamily="Source Sans 3, sans-serif"
                fontSize="11"
              >
                {label}
              </text>
            ) : null}
          </g>
        );
      })}
      <text
        x={cx}
        y={cy + 6}
        textAnchor="middle"
        fill="#5e574c"
        fontFamily="Source Sans 3, sans-serif"
        fontSize="13"
      >
        {word
          ? atMin
            ? "minimum at the top"
            : "click a bead to start there"
          : "type O and E"}
      </text>
    </svg>
  );
}

function rotateFrom(word: string, start: number): string {
  if (!word) return "";
  const k = ((start % word.length) + word.length) % word.length;
  return word.slice(k) + word.slice(0, k);
}

function beadAngle(index: number, shift: number, n: number): number {
  return ((index - shift) / n) * 2 * Math.PI - Math.PI / 2;
}

function arcPath(cx: number, cy: number, r: number, a0: number, a1: number): string {
  const x0 = cx + r * Math.cos(a0);
  const y0 = cy + r * Math.sin(a0);
  const x1 = cx + r * Math.cos(a1);
  const y1 = cy + r * Math.sin(a1);
  const sweep = (a1 - a0 + 2 * Math.PI) % (2 * Math.PI);
  const large = sweep > Math.PI ? 1 : 0;
  return `M ${x0} ${y0} A ${r} ${r} 0 ${large} 1 ${x1} ${y1}`;
}

function beadCaption(
  index: number,
  marks: {
    minIndex?: number;
    firstPeak: number;
    lastPeak: number;
    firstLaunch: number;
    atMin: boolean;
  },
): string | null {
  if (marks.minIndex === index && !marks.atMin) return "min";
  if (index === marks.firstLaunch && index !== marks.firstPeak) return "launch";
  if (index === marks.firstPeak && index === marks.lastPeak) return "the even";
  if (index === marks.firstPeak) return "1st peak";
  if (index === marks.lastPeak && marks.lastPeak >= 0) return "last peak";
  return null;
}
