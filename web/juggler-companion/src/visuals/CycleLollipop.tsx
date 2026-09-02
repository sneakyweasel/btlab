type CycleLollipopProps = {
  word: string;
  shift?: number;
  minIndex?: number;
  onSelectIndex?: (index: number) => void;
};

function originalIndex(minIndex: number, offset: number, length: number): number {
  return (((minIndex + offset) % length) + length) % length;
}

function rotateFrom(word: string, start: number): string {
  if (!word) return "";
  const k = ((start % word.length) + word.length) % word.length;
  return word.slice(k) + word.slice(0, k);
}

type Point = { x: number; y: number };

export function CycleLollipop({
  word,
  shift = 0,
  minIndex = 0,
  onSelectIndex,
}: CycleLollipopProps) {
  if (!word) {
    return (
      <p className="text-sm text-muted">Type O and E to draw the lollipop.</p>
    );
  }

  const spelling = rotateFrom(word, minIndex);
  const firstEven = spelling.indexOf("E");
  const stemLen = firstEven >= 0 ? firstEven : spelling.length;
  const balloonLen = firstEven >= 0 ? spelling.length - firstEven : 0;
  const atMin = (((shift % word.length) + word.length) % word.length) === minIndex;
  const stemGap = stemLen <= 3 ? 28 : stemLen <= 5 ? 22 : 18;
  const cx = 180;
  const topPad = 28;
  const balloonR = balloonLen <= 1 ? 36 : balloonLen <= 4 ? 58 : 70;
  const balloonCy = topPad + balloonR;
  const lastStemY = balloonCy + balloonR + 28;
  const knotY = lastStemY + Math.max(stemLen - 1, 0) * stemGap;
  const height = knotY + 24;

  const positions: Point[] = Array.from(word, () => ({ x: cx, y: knotY }));
  for (let offset = 0; offset < stemLen; offset += 1) {
    positions[originalIndex(minIndex, offset, word.length)] = {
      x: cx,
      y: knotY - offset * stemGap,
    };
  }
  for (let j = 0; j < balloonLen; j += 1) {
    const theta = Math.PI / 2 - (j / Math.max(balloonLen, 1)) * 2 * Math.PI;
    positions[originalIndex(minIndex, stemLen + j, word.length)] = {
      x: cx + balloonR * Math.cos(theta),
      y: balloonCy + balloonR * Math.sin(theta),
    };
  }

  const minOrig = originalIndex(minIndex, 0, word.length);
  const launchOrig =
    word.length > 1 ? originalIndex(minIndex, 1, word.length) : -1;
  const lastOrig = originalIndex(minIndex, word.length - 1, word.length);
  const firstPeakOrig =
    firstEven >= 0 ? originalIndex(minIndex, firstEven, word.length) : -1;
  const knot = positions[minOrig];
  const launchPt = launchOrig >= 0 ? positions[launchOrig] : null;
  const lastPt = positions[lastOrig];

  return (
    <svg
      viewBox={`0 0 360 ${height}`}
      role="img"
      className="mx-auto h-auto w-full max-w-sm"
    >
      <title>
        CycleMin lollipop: launch stem into the balloon, seam at the knot
      </title>
      {balloonLen > 1 ? (
        <circle
          cx={cx}
          cy={balloonCy}
          r={balloonR}
          fill="none"
          stroke="#d4cbb8"
          strokeWidth="2"
        />
      ) : null}
      {balloonLen > 0 ? (
        <text
          x={cx}
          y={balloonCy + 4}
          textAnchor="middle"
          fill="#5e574c"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="12"
        >
          balloon
        </text>
      ) : null}
      <line
        x1={cx}
        y1={knotY}
        x2={cx}
        y2={lastStemY}
        stroke="#c45c26"
        strokeWidth="4"
        opacity={atMin ? 0.45 : 0.2}
      />
      {lastPt && knot ? (
        <path
          d={`M ${lastPt.x} ${lastPt.y} Q ${cx - 48} ${(lastPt.y + knot.y) / 2} ${knot.x} ${knot.y}`}
          fill="none"
          stroke="#1f6f6a"
          strokeWidth="2.2"
          markerEnd="url(#lollipop-return)"
        />
      ) : null}
      {lastPt && knot && launchPt ? (
        <path
          d={`M ${lastPt.x} ${lastPt.y} L ${knot.x} ${knot.y} L ${launchPt.x} ${launchPt.y}`}
          fill="none"
          stroke="#1d1914"
          strokeWidth="2.4"
          strokeLinejoin="round"
          opacity={atMin ? 1 : 0.35}
        />
      ) : null}
      <text
        x={cx + 28}
        y={(knotY + lastStemY) / 2}
        fill="#c45c26"
        fontFamily="Source Sans 3, sans-serif"
        fontSize="12"
        opacity={atMin ? 1 : 0.45}
      >
        ascent
      </text>
      {Array.from(word).map((letter, index) => {
        const point = positions[index];
        const odd = letter === "O";
        const isMin = index === minOrig;
        const label = beadCaption(index, {
          minOrig,
          launchOrig,
          firstPeakOrig,
          lastOrig,
          atMin,
        });
        return (
          <g key={`${letter}-${index}`}>
            <circle
              cx={point.x}
              cy={point.y}
              r={isMin ? 18 : 14}
              fill={odd ? "#c45c26" : "#1f6f6a"}
              stroke={isMin ? "#1d1914" : "none"}
              strokeWidth={isMin ? 3 : 0}
              opacity={atMin ? 1 : 0.55}
              className={onSelectIndex ? "cursor-pointer" : undefined}
              onClick={onSelectIndex ? () => onSelectIndex(index) : undefined}
            />
            <text
              x={point.x}
              y={point.y + 4}
              textAnchor="middle"
              fill="#fffdf7"
              fontFamily="IBM Plex Mono, monospace"
              fontSize="13"
              className={onSelectIndex ? "cursor-pointer" : undefined}
              onClick={onSelectIndex ? () => onSelectIndex(index) : undefined}
            >
              {letter}
            </text>
            {label ? (
              <text
                x={point.x + 20}
                y={point.y + 4}
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
      <defs>
        <marker id="lollipop-return" markerWidth="8" markerHeight="8" refX="6" refY="4" orient="auto">
          <path d="M0,0 L8,4 L0,8 Z" fill="#1f6f6a" />
        </marker>
      </defs>
    </svg>
  );
}

function beadCaption(
  index: number,
  marks: {
    minOrig: number;
    launchOrig: number;
    firstPeakOrig: number;
    lastOrig: number;
    atMin: boolean;
  },
): string | null {
  if (index === marks.minOrig) return marks.atMin ? "knot n" : "min";
  if (index === marks.launchOrig && index !== marks.firstPeakOrig) return "launch";
  if (index === marks.firstPeakOrig && index === marks.lastOrig) return "the even";
  if (index === marks.firstPeakOrig) return "1st peak";
  if (index === marks.lastOrig) return "last peak";
  return null;
}
