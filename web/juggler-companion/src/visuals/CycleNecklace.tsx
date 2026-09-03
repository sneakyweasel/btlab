type CycleNecklaceProps = {
  word: string;
  shift?: number;
  minIndex?: number;
  onSelectIndex?: (index: number) => void;
  /** When false, draw letters only — a capture string is not a CycleMin cut. */
  showCut?: boolean;
};

function originalIndex(minIndex: number, offset: number, length: number): number {
  return (((minIndex + offset) % length) + length) % length;
}

export function CycleNecklace({
  word,
  shift = 0,
  minIndex,
  onSelectIndex,
  showCut = true,
}: CycleNecklaceProps) {
  const n = Math.max(word.length, 1);
  const cx = 180;
  const cy = 158;
  const r = n > 16 ? 108 : 92;
  const beadR = Math.min(16, Math.max(8, (Math.PI * r) / n - 1.5));
  const minBeadR = beadR + 3;
  const cut = showCut ? minIndex : undefined;
  const atMin =
    cut !== undefined && (((shift % n) + n) % n === cut);
  const firstEvenOffset =
    cut === undefined ? -1 : rotateFrom(word, cut).indexOf("E");
  const firstPeak =
    cut !== undefined && firstEvenOffset >= 0
      ? originalIndex(cut, firstEvenOffset, word.length)
      : -1;
  const lastPeak =
    cut !== undefined && word.length > 0
      ? originalIndex(cut, word.length - 1, word.length)
      : -1;
  const firstLaunch =
    cut !== undefined && word.length > 1
      ? originalIndex(cut, 1, word.length)
      : -1;

  function xy(index: number): { x: number; y: number } {
    const angle = beadAngle(index, shift, n);
    return { x: cx + r * Math.cos(angle), y: cy + r * Math.sin(angle) };
  }

  const centerCaption = !word
    ? "type O and E"
    : atMin
      ? null
      : showCut
        ? "click a bead to start there"
        : "letters of the string";

  return (
    <svg viewBox="0 0 360 300" role="img" className="mx-auto h-auto w-full max-w-sm">
      <title>
        {showCut
          ? "Cycle itinerary as a rotatable necklace. Walk clockwise."
          : "Capture string shown as letters, not a cycle"}
      </title>
      <circle cx={cx} cy={cy} r={r} fill="none" stroke="#d4cbb8" strokeWidth="2" />
      {word.length > 1
        ? Array.from(word).map((letter, index) => {
            const next = (index + 1) % word.length;
            const a0 = beadAngle(index, shift, n);
            const a1 = beadAngle(next, shift, n);
            const launchArc = cut !== undefined && index === cut;
            const pointed = pointedLink(cx, cy, r, a0, a1, beadR);
            if (!pointed) return null;
            const color = letter === "O" ? "#c45c26" : "#1f6f6a";
            return (
              <path
                key={`arc-${index}`}
                d={pointed}
                fill={color}
                stroke={color}
                strokeWidth="0.8"
                strokeLinejoin="round"
                opacity={launchArc ? 0.95 : 0.72}
              />
            );
          })
        : null}
      {cut !== undefined && lastPeak >= 0 && firstLaunch >= 0 ? (
        <path
          d={`M ${xy(lastPeak).x} ${xy(lastPeak).y} L ${xy(cut).x} ${xy(cut).y} L ${xy(firstLaunch).x} ${xy(firstLaunch).y}`}
          fill="none"
          stroke="#1d1914"
          strokeWidth="2.2"
          strokeLinejoin="round"
          opacity={atMin ? 0.9 : 0.35}
        />
      ) : null}
      <polygon
        points={`${cx},${cy - r - 16} ${cx - 7},${cy - r - 30} ${cx + 7},${cy - r - 30}`}
        fill="#1f3d34"
      />
      {atMin || !showCut ? (
        <text
          x={cx}
          y={cy - r - 36}
          textAnchor="middle"
          fill="#1f3d34"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="12"
        >
          {atMin ? "CycleMin cut" : "capture string"}
        </text>
      ) : null}
      {Array.from(word).map((letter, index) => {
        const angle = beadAngle(index, shift, n);
        const x = cx + r * Math.cos(angle);
        const y = cy + r * Math.sin(angle);
        const isMin = cut === index;
        const odd = letter === "O";
        const label = beadCaption(index, {
          minIndex: cut,
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
              r={isMin ? minBeadR : beadR}
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
              fontSize={beadR < 12 ? "10" : "14"}
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
      {centerCaption ? (
        <text
          x={cx}
          y={cy + 6}
          textAnchor="middle"
          fill="#5e574c"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="13"
        >
          {centerCaption}
        </text>
      ) : null}
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

function atRadius(
  cx: number,
  cy: number,
  r: number,
  ang: number,
): string {
  return `${cx + r * Math.cos(ang)} ${cy + r * Math.sin(ang)}`;
}

function pointedLink(
  cx: number,
  cy: number,
  r: number,
  a0: number,
  a1: number,
  beadR: number,
): string {
  const sweep = (a1 - a0 + 2 * Math.PI) % (2 * Math.PI);
  const pad = Math.asin(Math.min(1, (beadR + 1.4) / r));
  const start = a0 + pad;
  const span = sweep - 2 * pad;
  if (span < 0.07) return "";
  const halfW = 2.2;
  const head = Math.min(0.2, span * 0.42);
  const shaft = span - head;
  const outer: string[] = [];
  const inner: string[] = [];
  const steps = 5;
  for (let i = 0; i <= steps; i += 1) {
    const ang = start + (shaft * i) / steps;
    outer.push(atRadius(cx, cy, r + halfW, ang));
    inner.push(atRadius(cx, cy, r - halfW, ang));
  }
  const tip = atRadius(cx, cy, r, start + span);
  return `M ${outer.join(" L ")} L ${tip} L ${inner.reverse().join(" L ")} Z`;
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
