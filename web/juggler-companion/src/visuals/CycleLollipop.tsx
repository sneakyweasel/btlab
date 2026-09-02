import {
  IDEAL_BALLOON_BEADS,
  IDEAL_STRING_BEADS,
  type IdealBead,
} from "../juggler/constants";

const CX = 548;
const CY = 160;
const R = 104;
const ODD = "#c45c26";
const EVEN = "#1f6f6a";

function balloonXY(index: number, n: number): { x: number; y: number } {
  const angle = (index / Math.max(n, 1)) * 2 * Math.PI + Math.PI;
  return { x: CX + R * Math.cos(angle), y: CY + R * Math.sin(angle) };
}

function beadPaint(bead: IdealBead): {
  fill: string;
  stroke: string;
  dash?: string;
  text: string;
  opacity: number;
} {
  if (bead.tone === "unknown") {
    return {
      fill: "#fffdf7",
      stroke: "#8a8378",
      dash: "3 2",
      text: "#8a8378",
      opacity: 1,
    };
  }
  const fill = bead.letter === "O" ? ODD : EVEN;
  if (bead.tone === "count") {
    return { fill, stroke: "none", text: "#fffdf7", opacity: 0.38 };
  }
  return { fill, stroke: "none", text: "#fffdf7", opacity: 1 };
}

function balloonCaption(index: number, bead: IdealBead): string {
  const sureEvens = IDEAL_BALLOON_BEADS
    .map((item, itemIndex) =>
      item.letter === "E" && item.tone === "sure" ? itemIndex : -1,
    )
    .filter((itemIndex) => itemIndex >= 0);
  if (index === 0) return "min";
  if (index === 1) return "a₁≥2";
  if (bead.letter === "O" && bead.tone === "count" && index === 2) return "a₁";
  if (index === sureEvens[0]) return "E";
  if (bead.letter === "E" && bead.tone === "count" && index === sureEvens[0] + 1) {
    return "e>4";
  }
  if (index === IDEAL_BALLOON_BEADS.length - 2) return "aₑ≤1";
  if (index === IDEAL_BALLOON_BEADS.length - 1) return "last E";
  return "";
}

function Bead({
  x,
  y,
  bead,
  radius,
  marked,
  caption,
  captionX,
  captionY,
}: {
  x: number;
  y: number;
  bead: IdealBead;
  radius: number;
  marked?: boolean;
  caption?: string;
  captionX?: number;
  captionY?: number;
}) {
  const paint = beadPaint(bead);
  return (
    <g opacity={paint.opacity}>
      <circle
        cx={x}
        cy={y}
        r={radius}
        fill={paint.fill}
        stroke={marked ? "#1d1914" : paint.stroke}
        strokeWidth={marked ? 3 : paint.dash ? 1.6 : 0}
        strokeDasharray={paint.dash}
      />
      <text
        x={x}
        y={y + 4}
        textAnchor="middle"
        fill={paint.text}
        fontFamily="IBM Plex Mono, monospace"
        fontSize={radius >= 15 ? "13" : "11"}
      >
        {bead.letter === "O" && marked ? "n" : bead.letter}
      </text>
      {caption ? (
        <text
          x={captionX ?? x}
          y={captionY ?? y + radius + 16}
          textAnchor="middle"
          fill="#5e574c"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="11"
          opacity={1 / paint.opacity}
        >
          {caption}
        </text>
      ) : null}
    </g>
  );
}

const RUNS: { label: string; beads: IdealBead[] }[] = [
  {
    label: "a₁≥2",
    beads: [
      { letter: "O", tone: "sure" },
      { letter: "O", tone: "sure" },
      { letter: "O", tone: "count" },
      { letter: "O", tone: "count" },
      { letter: "O", tone: "count" },
    ],
  },
  { label: "E", beads: [{ letter: "E", tone: "sure" }] },
  {
    label: "e>4",
    beads: [
      { letter: "E", tone: "count" },
      { letter: "E", tone: "count" },
    ],
  },
  {
    label: "a₂",
    beads: [
      { letter: "O", tone: "count" },
      { letter: "O", tone: "count" },
    ],
  },
  { label: "E", beads: [{ letter: "E", tone: "sure" }] },
  {
    label: "a₃",
    beads: [
      { letter: "O", tone: "count" },
      { letter: "O", tone: "count" },
    ],
  },
  { label: "E", beads: [{ letter: "E", tone: "sure" }] },
  { label: "aₑ≤1", beads: [{ letter: "O", tone: "count" }] },
  { label: "E", beads: [{ letter: "E", tone: "sure" }] },
];

export function CycleLollipop() {
  const balloon = IDEAL_BALLOON_BEADS;
  const n = balloon.length;
  const lastPeak = balloonXY(n - 1, n);
  const knot = balloonXY(0, n);
  const launch = balloonXY(1, n);
  const stem = IDEAL_STRING_BEADS.map((bead, index) => ({
    x: 36 + index * 44,
    bead,
    label: index === 0 ? "start" : index === 1 ? "OO" : bead.letter === "E" ? "t" : "",
  }));
  const joinX = 300;
  const beadR = Math.min(14, Math.max(9, (Math.PI * R) / n - 1.2));

  return (
    <div className="rounded-xl border border-line bg-paper/70 px-3 py-3">
      <p className="text-xs uppercase tracking-wide text-muted">
        Idealized string and balloon
      </p>
      <p className="mt-1 text-sm text-muted">
        Solid beads are sure. Faded O and E are known parity with unknown
        count. Grey ??? are unknown color. The unique known balloon is 1.
      </p>
      <svg viewBox="0 0 720 340" role="img" className="mt-2 h-auto w-full">
        <title>
          Idealized string joining a CycleMin run-form balloon. Solid letters
          are sure; faded letters have known color and unknown count
        </title>
        <text
          x="36"
          y="36"
          fill="#5e574c"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="12"
        >
          string
        </text>
        <text
          x={CX}
          y="36"
          textAnchor="middle"
          fill="#5e574c"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="12"
        >
          balloon
        </text>
        <line
          x1={stem[0].x}
          y1={CY}
          x2={joinX}
          y2={CY}
          stroke="#d4cbb8"
          strokeWidth="2"
        />
        <path
          d={`M ${joinX} ${CY} L ${knot.x} ${knot.y}`}
          fill="none"
          stroke="#1d1914"
          strokeWidth="2.2"
          markerEnd="url(#string-join)"
        />
        {stem.map((item) => (
          <Bead
            key={`stem-${item.x}`}
            x={item.x}
            y={CY}
            bead={item.bead}
            radius={16}
            caption={item.label}
          />
        ))}
        <text
          x={(joinX + knot.x) / 2}
          y={CY - 14}
          textAnchor="middle"
          fill="#1d1914"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="11"
        >
          join
        </text>
        <circle cx={CX} cy={CY} r={R} fill="none" stroke="#d4cbb8" strokeWidth="2" />
        {balloon.map((bead, index) => {
          const next = (index + 1) % n;
          const a0 = (index / n) * 2 * Math.PI + Math.PI;
          const a1 = (next / n) * 2 * Math.PI + Math.PI;
          const launchArc = index === 0;
          const paint = beadPaint(bead);
          return (
            <path
              key={`arc-${index}`}
              d={arcPath(CX, CY, R, a0, a1)}
              fill="none"
              stroke={
                bead.tone === "unknown"
                  ? "#8a8378"
                  : bead.letter === "O"
                    ? ODD
                    : EVEN
              }
              strokeWidth={launchArc ? 5 : 3}
              strokeLinecap="round"
              strokeDasharray={bead.tone === "unknown" ? "4 3" : undefined}
              opacity={launchArc ? 0.85 : paint.opacity * 0.9}
            />
          );
        })}
        <path
          d={`M ${lastPeak.x} ${lastPeak.y} L ${knot.x} ${knot.y} L ${launch.x} ${launch.y}`}
          fill="none"
          stroke="#1d1914"
          strokeWidth="2.2"
          strokeLinejoin="round"
        />
        {balloon.map((bead, index) => {
          const { x, y } = balloonXY(index, n);
          const caption = balloonCaption(index, bead);
          const labelR = R + 26;
          const angle = (index / n) * 2 * Math.PI + Math.PI;
          return (
            <Bead
              key={`balloon-${index}`}
              x={x}
              y={y}
              bead={bead}
              radius={index === 0 ? beadR + 3 : beadR}
              marked={index === 0}
              caption={caption}
              captionX={CX + labelR * Math.cos(angle)}
              captionY={CY + labelR * Math.sin(angle) + 4}
            />
          );
        })}
        <text
          x={CX}
          y={CY - 4}
          textAnchor="middle"
          fill="#5e574c"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="12"
        >
          CycleMin
        </text>
        <text
          x={CX}
          y={CY + 14}
          textAnchor="middle"
          fill="#5e574c"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="11"
        >
          L≥11
        </text>
        <defs>
          <marker
            id="string-join"
            markerWidth="8"
            markerHeight="8"
            refX="6"
            refY="4"
            orient="auto"
          >
            <path d="M0,0 L8,4 L0,8 Z" fill="#1d1914" />
          </marker>
        </defs>
      </svg>
      <div
        className="mt-1 flex flex-wrap items-end justify-center gap-1.5"
        aria-label="CycleMin run form with sure and faded beads"
      >
        {RUNS.map((run, index) => (
          <span key={`${run.label}-${index}`} className="grid justify-items-center gap-0.5">
            <span className="flex gap-0.5">
              {run.beads.map((bead, letterIndex) => {
                const paint = beadPaint(bead);
                return (
                  <span
                    key={`${bead.letter}-${letterIndex}`}
                    className="inline-flex h-7 min-w-7 items-center justify-center rounded-md font-mono text-xs"
                    style={{
                      background: paint.fill,
                      color: paint.text,
                      opacity: paint.opacity,
                      border: paint.dash ? "1px dashed #8a8378" : "none",
                    }}
                  >
                    {bead.letter}
                  </span>
                );
              })}
            </span>
            <span className="text-[10px] uppercase tracking-wide text-muted">
              {run.label}
            </span>
          </span>
        ))}
      </div>
      <p className="mt-2 font-mono text-sm text-ink">
        OO???E
        <span className="mx-2 text-muted">→</span>
        O<sup>a₁</sup>E⋯O<sup>aₑ</sup>E
        <span className="ml-2 font-sans text-muted">
          · a₁≥2 · e≥4 · aₑ≤1 · period at least 11 · not a cycle
        </span>
      </p>
      <p className="mt-2 text-sm text-muted">
        Solid OO and the four E letters are forced. Faded O is more odd-run
        mass; faded E is more than four evens. Unused odd-runs may be empty.
        The last faded O is 0 or 1: EE or OE at the seam.
      </p>
    </div>
  );
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
