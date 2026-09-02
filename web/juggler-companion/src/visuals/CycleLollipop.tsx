import type { DecisionFocus } from "../content/idealDecisions";
import {
  IDEAL_BALLOON_BEADS,
  IDEAL_STRING_BEADS,
  packCountRuns,
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
  return { fill, stroke: "none", text: "#fffdf7", opacity: 1 };
}

function balloonCaption(index: number, beads: readonly IdealBead[]): string {
  const bead = beads[index];
  const sureEvens = beads
    .map((item, itemIndex) =>
      item.letter === "E" && item.tone === "sure" ? itemIndex : -1,
    )
    .filter((itemIndex) => itemIndex >= 0);
  if (index === 0) return "min";
  if (index === 1) return "a₁≥2";
  if (bead.letter === "O" && bead.tone === "count" && index === 2) return "a₁";
  if (index === sureEvens[0]) return "E";
  if (index === beads.length - 2) return "aₑ≤1";
  if (index === beads.length - 1) return "last E";
  return "";
}

const STACK_COPIES = 3;

function stackXY(
  copy: number,
  copies: number,
  x: number,
  y: number,
  step: number,
  orbit?: { cx: number; cy: number; r: number; angle: number },
): { x: number; y: number } {
  const k = copy - (copies - 1);
  if (orbit) {
    const angle = orbit.angle + (k * step) / orbit.r;
    return {
      x: orbit.cx + orbit.r * Math.cos(angle),
      y: orbit.cy + orbit.r * Math.sin(angle),
    };
  }
  return { x: x + k * step, y };
}

function regionLit(focus: DecisionFocus | undefined, region: DecisionFocus): boolean {
  if (!focus || focus === "figure") return true;
  if (focus === "none") return false;
  if (focus === region) return true;
  if (focus === "string" && region.startsWith("string")) return true;
  if (focus === "balloon" && region.startsWith("balloon")) return true;
  if (focus === "join" && (region === "join" || region === "string-e" || region === "balloon-oo")) {
    return true;
  }
  if (focus === "balloon-e" && region === "balloon-first-e") return true;
  return false;
}

function stemRegion(index: number, last: number): DecisionFocus {
  if (index <= 1) return "string-oo";
  if (index === last) return "string-e";
  return "string-grey";
}

function balloonRegion(
  index: number,
  bead: IdealBead,
  beads: readonly IdealBead[],
): DecisionFocus {
  const last = beads.length - 1;
  const firstSureEven = beads.findIndex(
    (item) => item.letter === "E" && item.tone === "sure",
  );
  if (index <= 1) return "balloon-oo";
  if (index >= last - 1) return "balloon-seam";
  if (index === firstSureEven) return "balloon-first-e";
  if (bead.letter === "E" && bead.tone === "sure") return "balloon-e";
  if (bead.tone === "count") return "balloon-fade";
  return "balloon";
}

function balloonDecision(region: DecisionFocus): string {
  if (region === "balloon-oo") return "balloon-oo";
  if (region === "balloon-first-e") return "balloon-overshoot";
  if (region === "balloon-e") return "balloon-evens";
  if (region === "balloon-seam") return "balloon-seam";
  if (region === "balloon-fade") return "balloon-fade";
  return "balloon-cut";
}

function stemDecision(region: DecisionFocus): string {
  if (region === "string-oo") return "string-oo";
  if (region === "string-e") return "string-e";
  return "string-grey";
}

function stemCaption(index: number, bead: IdealBead): string {
  if (index === 0) return "start";
  if (index === 1) return "cartoon";
  if (bead.tone === "unknown" && index === 2) return "min 0";
  if (bead.letter === "E") return "t";
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
  lit,
  onPick,
  orbit,
}: {
  x: number;
  y: number;
  bead: IdealBead;
  radius: number;
  marked?: boolean;
  caption?: string;
  captionX?: number;
  captionY?: number;
  lit?: boolean;
  onPick?: () => void;
  orbit?: { cx: number; cy: number; r: number; angle: number };
}) {
  const paint = beadPaint(bead);
  const copies = bead.tone === "count" ? STACK_COPIES : 1;
  const step = radius * 0.72;
  return (
    <g
      opacity={lit === false ? 0.18 : 1}
      role={onPick ? "button" : undefined}
      tabIndex={onPick ? 0 : undefined}
      style={onPick ? { cursor: "pointer" } : undefined}
      onClick={
        onPick
          ? (event) => {
              event.stopPropagation();
              onPick();
            }
          : undefined
      }
      onKeyDown={
        onPick
          ? (event) => {
              if (event.key === "Enter" || event.key === " ") {
                event.preventDefault();
                onPick();
              }
            }
          : undefined
      }
    >
      {Array.from({ length: copies }, (_, copy) => {
        const at = stackXY(copy, copies, x, y, step, orbit);
        const stacked = copies > 1;
        return (
          <circle
            key={`stack-${copy}`}
            cx={at.x}
            cy={at.y}
            r={radius}
            fill={paint.fill}
            stroke={marked ? "#1d1914" : stacked ? "#fffdf7" : paint.stroke}
            strokeWidth={marked ? 3 : stacked ? 1.4 : paint.dash ? 1.6 : 0}
            strokeDasharray={paint.dash}
            opacity={stacked ? 0.28 + copy * 0.14 : 1}
          />
        );
      })}
      <text
        x={x}
        y={y + 4}
        textAnchor="middle"
        fill={paint.text}
        fontFamily="IBM Plex Mono, monospace"
        fontSize={radius >= 15 ? "13" : "11"}
        opacity={copies > 1 ? 0.7 : 1}
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
        >
          {caption}
        </text>
      ) : null}
    </g>
  );
}

function RunTile({ bead }: { bead: IdealBead }) {
  const paint = beadPaint(bead);
  if (bead.tone !== "count") {
    return (
      <span
        className="inline-flex h-7 min-w-7 items-center justify-center rounded-full font-mono text-xs"
        style={{
          background: paint.fill,
          color: paint.text,
          border: paint.dash ? "1px dashed #8a8378" : "none",
        }}
      >
        {bead.letter}
      </span>
    );
  }
  return (
    <span className="relative inline-flex h-7 w-10 items-center justify-center">
      {[0, 1, 2].map((copy) => (
        <span
          key={copy}
          className="absolute top-0 h-7 w-7 rounded-full"
          style={{
            left: copy * 7,
            background: paint.fill,
            opacity: 0.28 + copy * 0.14,
            boxShadow: "0 0 0 1px #fffdf7",
          }}
        />
      ))}
      <span className="relative font-mono text-xs text-card">{bead.letter}</span>
    </span>
  );
}

const RUNS: { label: string; decision: string; focus: DecisionFocus; beads: IdealBead[] }[] = [
  {
    label: "a₁≥2",
    decision: "balloon-oo",
    focus: "balloon-oo",
    beads: [
      { letter: "O", tone: "sure" },
      { letter: "O", tone: "sure" },
      { letter: "O", tone: "count" },
      { letter: "O", tone: "count" },
      { letter: "O", tone: "count" },
    ],
  },
  { label: "E", decision: "balloon-overshoot", focus: "balloon-first-e", beads: [{ letter: "E", tone: "sure" }] },
  {
    label: "a₂",
    decision: "balloon-fade",
    focus: "balloon-fade",
    beads: [
      { letter: "O", tone: "count" },
      { letter: "O", tone: "count" },
    ],
  },
  { label: "E", decision: "balloon-evens", focus: "balloon-e", beads: [{ letter: "E", tone: "sure" }] },
  {
    label: "a₃",
    decision: "balloon-fade",
    focus: "balloon-fade",
    beads: [
      { letter: "O", tone: "count" },
      { letter: "O", tone: "count" },
    ],
  },
  { label: "E", decision: "balloon-evens", focus: "balloon-e", beads: [{ letter: "E", tone: "sure" }] },
  { label: "aₑ≤1", decision: "balloon-seam", focus: "balloon-seam", beads: [{ letter: "O", tone: "count" }] },
  { label: "E", decision: "balloon-seam", focus: "balloon-seam", beads: [{ letter: "E", tone: "sure" }] },
];

export function CycleLollipop({
  focus,
  onSelectDecision,
  onClearFocus,
}: {
  focus?: DecisionFocus;
  onSelectDecision?: (id: string) => void;
  onClearFocus?: () => void;
}) {
  const balloon = packCountRuns(IDEAL_BALLOON_BEADS);
  const n = balloon.length;
  const lastPeak = balloonXY(n - 1, n);
  const knot = balloonXY(0, n);
  const launch = balloonXY(1, n);
  const stem = IDEAL_STRING_BEADS.map((bead, index) => ({
    x: 36 + index * 44,
    bead,
    region: stemRegion(index, IDEAL_STRING_BEADS.length - 1),
    label: stemCaption(index, bead),
  }));
  const joinX = 300;
  const beadR = Math.min(14, Math.max(9, (Math.PI * R) / n - 1.2));
  const joinLit = regionLit(focus, "join");

  function pick(id: string, event?: { stopPropagation: () => void }) {
    event?.stopPropagation();
    onSelectDecision?.(id);
  }

  return (
    <div
      className="rounded-xl border border-line bg-paper/70 px-3 py-3"
      onClick={(event) => {
        if (event.target === event.currentTarget) onClearFocus?.();
      }}
    >
      <p className="text-xs uppercase tracking-wide text-muted">
        Idealized string and balloon
      </p>
      <p className="mt-1 text-sm text-muted">
        Solid beads exist. Overlapping circles are known parity with unknown
        count. Grey ??? are unknown color, minimum length 0. Stem OO and join
        E are cartoons. The unique known balloon is 1.
      </p>
      <svg
        viewBox="0 0 720 340"
        role="img"
        className="mt-2 h-auto w-full"
        onClick={(event) => {
          if ((event.target as Element).closest("[role='button']")) return;
          onClearFocus?.();
        }}
      >
        <title>
          Idealized string joining a CycleMin run-form balloon. Solid letters
          exist; overlapping circles have known color and unknown count
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
          opacity={joinLit ? 1 : 0.18}
          style={onSelectDecision ? { cursor: "pointer" } : undefined}
          role="button"
          onClick={(event) => pick("join-seam", event)}
        />
        {stem.map((item) => (
          <Bead
            key={`stem-${item.x}`}
            x={item.x}
            y={CY}
            bead={item.bead}
            radius={16}
            caption={item.label}
            lit={regionLit(focus, item.region)}
            onPick={
              onSelectDecision
                ? () => pick(stemDecision(item.region))
                : undefined
            }
          />
        ))}
        <text
          x={(joinX + knot.x) / 2}
          y={CY - 14}
          textAnchor="middle"
          fill="#1d1914"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="11"
          opacity={joinLit ? 1 : 0.18}
        >
          join · cartoon
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
              opacity={
                regionLit(focus, balloonRegion(index, bead, balloon))
                  ? launchArc
                    ? 0.85
                    : paint.opacity * 0.9
                  : 0.12
              }
            />
          );
        })}
        <path
          d={`M ${lastPeak.x} ${lastPeak.y} L ${knot.x} ${knot.y} L ${launch.x} ${launch.y}`}
          fill="none"
          stroke="#1d1914"
          strokeWidth="2.2"
          strokeLinejoin="round"
          opacity={
            regionLit(focus, "balloon-seam") || regionLit(focus, "join") ? 1 : 0.18
          }
        />
        {balloon.map((bead, index) => {
          const { x, y } = balloonXY(index, n);
          const caption = balloonCaption(index, balloon);
          const labelR = R + 26;
          const angle = (index / n) * 2 * Math.PI + Math.PI;
          const region = balloonRegion(index, bead, balloon);
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
              orbit={{ cx: CX, cy: CY, r: R, angle }}
              lit={regionLit(focus, region)}
              onPick={
                onSelectDecision
                  ? () => pick(balloonDecision(region))
                  : undefined
              }
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
        aria-label="CycleMin run form with sure beads and overlapping count stacks"
      >
        {RUNS.map((run, index) => {
          const lit = regionLit(focus, run.focus);
          return (
            <button
              key={`${run.label}-${index}`}
              type="button"
              className="grid justify-items-center gap-0.5"
              style={{ opacity: lit ? 1 : 0.28 }}
              onClick={(event) => pick(run.decision, event)}
            >
              <span className="flex items-center gap-0.5">
                {packCountRuns(run.beads).map((bead, letterIndex) => (
                  <RunTile key={`${bead.letter}-${bead.tone}-${letterIndex}`} bead={bead} />
                ))}
              </span>
              <span className="text-[10px] uppercase tracking-wide text-muted">
                {run.label}
              </span>
            </button>
          );
        })}
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
        On the balloon, solid OO and the four E letters are forced.
        Overlapping O is more odd-run mass. Extra evens past those four are
        empty at length 11, so they are not a fifth E. Unused odd-runs may
        be empty. The last overlapping O is 0 or 1: EE or OE at the seam.
        Stem OO???E is a first-visit cartoon.
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
