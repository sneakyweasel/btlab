import type { DecisionFocus } from "../content/idealDecisions";
import {
  IDEAL_BALLOON_BEADS,
  IDEAL_BALLOON_INTERVALS,
  IDEAL_STRING_BEADS,
  idealJoinLabel,
  idealJoinSpots,
  intervalBoundLabel,
  stepIdealJoin,
  type BalloonInterval,
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
  const sureEvens = beads
    .map((item, itemIndex) =>
      item.letter === "E" && item.tone === "sure" ? itemIndex : -1,
    )
    .filter((itemIndex) => itemIndex >= 0);
  if (index === 0) return "min";
  if (index === 1) return "a₁≥2";
  if (index === sureEvens[0]) return "first E";
  if (index === sureEvens[sureEvens.length - 1]) return "last E";
  if (sureEvens.includes(index)) return "E";
  return "";
}

function regionLit(focus: DecisionFocus | undefined, region: DecisionFocus): boolean {
  if (!focus || focus === "figure") return true;
  if (focus === "none") return false;
  if (focus === region) return true;
  if (focus === "string" && region.startsWith("string")) return true;
  if (focus === "balloon" && region.startsWith("balloon")) return true;
  if (focus === "join" && (region === "join" || region === "string-e")) {
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
  if (index === last) return "balloon-seam";
  if (index === firstSureEven) return "balloon-first-e";
  if (bead.letter === "E" && bead.tone === "sure") return "balloon-e";
  return "balloon";
}

function intervalRegion(interval: BalloonInterval): DecisionFocus {
  if (interval.kind === "lastZeroOrOne") return "balloon-seam";
  if (interval.kind === "extraEven") return "balloon-e";
  return "balloon-fade";
}

function intervalDecision(interval: BalloonInterval): string {
  if (interval.kind === "lastZeroOrOne") return "balloon-seam";
  if (interval.kind === "extraEven") return "balloon-evens";
  return "balloon-fade";
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
  if (index === 1) return "optional";
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
  joined,
  caption,
  captionX,
  captionY,
  lit,
  onPick,
}: {
  x: number;
  y: number;
  bead: IdealBead;
  radius: number;
  marked?: boolean;
  joined?: boolean;
  caption?: string;
  captionX?: number;
  captionY?: number;
  lit?: boolean;
  onPick?: () => void;
}) {
  const paint = beadPaint(bead);
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
      <circle
        cx={x}
        cy={y}
        r={radius}
        fill={paint.fill}
        stroke={joined || marked ? "#1d1914" : paint.stroke}
        strokeWidth={joined ? 3.4 : marked ? 3 : paint.dash ? 1.6 : 0}
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
        >
          {caption}
        </text>
      ) : null}
    </g>
  );
}

function RunTile({
  bead,
  glyph,
  ring,
  size = 28,
}: {
  bead: IdealBead;
  glyph?: string;
  ring?: boolean;
  size?: number;
}) {
  const paint = beadPaint(bead);
  return (
    <span
      className="inline-flex items-center justify-center rounded-full font-mono text-xs"
      style={{
        height: size,
        minWidth: size,
        background: paint.fill,
        color: paint.text,
        border: ring
          ? "2px solid #1d1914"
          : paint.dash
            ? "1px dashed #8a8378"
            : "none",
        boxSizing: "border-box",
      }}
    >
      {glyph ?? bead.letter}
    </span>
  );
}

const LEGEND: {
  decision: string;
  focus: DecisionFocus;
  label: string;
  kind?: "optional" | "name" | "interval";
  beads: { bead: IdealBead; glyph?: string; ring?: boolean }[];
}[] = [
  {
    decision: "balloon-oo",
    focus: "balloon-oo",
    label: "exist · 6 sure letters",
    beads: [
      { bead: { letter: "O", tone: "sure" } },
      { bead: { letter: "E", tone: "sure" } },
    ],
  },
  {
    decision: "balloon-fade",
    focus: "balloon-fade",
    label: "interval · bound, not a letter",
    kind: "interval",
    beads: [],
  },
  {
    decision: "string-oo",
    focus: "string-oo",
    label: "stem",
    kind: "optional",
    beads: [
      { bead: { letter: "O", tone: "sure" } },
      { bead: { letter: "O", tone: "sure" } },
    ],
  },
  {
    decision: "string-e",
    focus: "string-e",
    label: "join t",
    kind: "optional",
    beads: [{ bead: { letter: "E", tone: "sure" } }],
  },
  {
    decision: "join-seam",
    focus: "join",
    label: "sure join · 1 of 6",
    beads: [{ bead: { letter: "O", tone: "sure" }, glyph: "n", ring: true }],
  },
  {
    decision: "string-capture",
    focus: "string",
    label: "only known cycle",
    kind: "name",
    beads: [],
  },
];

const RUNS: {
  label: string;
  decision: string;
  focus: DecisionFocus;
  beads?: IdealBead[];
  interval?: boolean;
}[] = [
  {
    label: "a₁≥2",
    decision: "balloon-oo",
    focus: "balloon-oo",
    beads: [
      { letter: "O", tone: "sure" },
      { letter: "O", tone: "sure" },
    ],
  },
  { label: "0+", decision: "balloon-fade", focus: "balloon-fade", interval: true },
  { label: "first E", decision: "balloon-overshoot", focus: "balloon-first-e", beads: [{ letter: "E", tone: "sure" }] },
  { label: "0+", decision: "balloon-fade", focus: "balloon-fade", interval: true },
  { label: "E", decision: "balloon-evens", focus: "balloon-e", beads: [{ letter: "E", tone: "sure" }] },
  { label: "0+", decision: "balloon-evens", focus: "balloon-e", interval: true },
  { label: "E", decision: "balloon-evens", focus: "balloon-e", beads: [{ letter: "E", tone: "sure" }] },
  { label: "0 or 1", decision: "balloon-seam", focus: "balloon-seam", interval: true },
  { label: "last E", decision: "balloon-seam", focus: "balloon-seam", beads: [{ letter: "E", tone: "sure" }] },
];

function displayOf(trueIndex: number, joinIndex: number, n: number): number {
  return (trueIndex - joinIndex + n) % n;
}

function displayXY(
  trueIndex: number,
  joinIndex: number,
  n: number,
): { x: number; y: number } {
  return balloonXY(displayOf(trueIndex, joinIndex, n), n);
}

function intervalAngle(
  afterBead: number,
  joinIndex: number,
  n: number,
): number {
  const d0 = displayOf(afterBead, joinIndex, n);
  const d1 = displayOf((afterBead + 1) % n, joinIndex, n);
  const a0 = (d0 / n) * 2 * Math.PI + Math.PI;
  let a1 = (d1 / n) * 2 * Math.PI + Math.PI;
  if (a1 <= a0) a1 += 2 * Math.PI;
  return (a0 + a1) / 2;
}

export function CycleLollipop({
  focus,
  joinIndex = 0,
  onJoinIndex,
  onSelectDecision,
  onClearFocus,
}: {
  focus?: DecisionFocus;
  joinIndex?: number;
  onJoinIndex?: (index: number) => void;
  onSelectDecision?: (id: string) => void;
  onClearFocus?: () => void;
}) {
  const balloon = IDEAL_BALLOON_BEADS;
  const n = balloon.length;
  const spots = idealJoinSpots(balloon);
  const joinAt = spots.includes(joinIndex) ? joinIndex : 0;
  const lastPeak = displayXY(n - 1, joinAt, n);
  const cycleMin = displayXY(0, joinAt, n);
  const launch = displayXY(1, joinAt, n);
  const joinPoint = balloonXY(0, n);
  const stem = IDEAL_STRING_BEADS.map((bead, index) => ({
    x: 36 + index * 44,
    bead,
    region: stemRegion(index, IDEAL_STRING_BEADS.length - 1),
    label: stemCaption(index, bead),
  }));
  const joinX = 300;
  const beadR = Math.min(14, Math.max(9, (Math.PI * R) / n - 1.2));
  const joinLit = regionLit(focus, "join");
  const joinName = idealJoinLabel(joinAt, balloon);
  const atCycleMin = joinAt === 0;

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
        Optional stem and cycle
      </p>
      <ul
        className="mt-2 flex flex-wrap items-center gap-x-3 gap-y-2"
        aria-label="Figure legend"
      >
        {LEGEND.map((item) => {
          const lit =
            item.focus === "balloon-fade"
              ? regionLit(focus, "balloon-fade") || regionLit(focus, "string-grey")
              : item.focus === "balloon-oo"
                ? regionLit(focus, "balloon-oo") ||
                  regionLit(focus, "balloon-e") ||
                  regionLit(focus, "balloon-first-e")
                : regionLit(focus, item.focus);
          return (
            <li key={item.decision}>
              <button
                type="button"
                className="flex items-center gap-1.5 text-left"
                style={{ opacity: lit ? 1 : 0.28 }}
                onClick={(event) => pick(item.decision, event)}
              >
                <span className="flex items-center gap-0.5">
                  {item.kind === "name" ? (
                    <span className="inline-flex h-[22px] min-w-[22px] items-center justify-center rounded-full border border-ink bg-card font-serif text-sm leading-none">
                      1
                    </span>
                  ) : item.kind === "interval" ? (
                    <span
                      aria-hidden
                      className="inline-block h-[18px] w-[18px] border-l-2 border-dashed border-[#8a8378]"
                    />
                  ) : (
                    item.beads.map((entry, index) => (
                      <RunTile
                        key={`${item.decision}-${index}`}
                        bead={entry.bead}
                        glyph={entry.glyph}
                        ring={entry.ring}
                        size={22}
                      />
                    ))
                  )}
                </span>
                {item.kind === "optional" ? (
                  <span className="rounded-full bg-warn/15 px-1.5 py-0.5 text-[10px] uppercase tracking-wide text-warn">
                    optional
                  </span>
                ) : null}
                <span className="text-xs text-muted">{item.label}</span>
              </button>
            </li>
          );
        })}
      </ul>
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
          Optional stem joining a CycleMin cycle at a sure letter.
          Six sure letters; interval marks are bounds, not letter beads
        </title>
        <text
          x="36"
          y="36"
          fill="#5e574c"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="12"
        >
          stem
        </text>
        <text
          x={CX}
          y="36"
          textAnchor="middle"
          fill="#5e574c"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="12"
        >
          cycle
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
          d={`M ${joinX} ${CY} L ${joinPoint.x} ${joinPoint.y}`}
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
          x={(joinX + joinPoint.x) / 2}
          y={CY - 14}
          textAnchor="middle"
          fill="#1d1914"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="11"
          opacity={joinLit ? 1 : 0.18}
        >
          {atCycleMin ? "join · CycleMin" : `join · ${joinName}`}
        </text>
        <circle cx={CX} cy={CY} r={R} fill="none" stroke="#d4cbb8" strokeWidth="2" />
        {balloon.map((bead, trueIndex) => {
          const display = displayOf(trueIndex, joinAt, n);
          const a0 = (display / n) * 2 * Math.PI + Math.PI;
          const a1 = ((display + 1) / n) * 2 * Math.PI + Math.PI;
          const launchArc = trueIndex === 0;
          const interval = IDEAL_BALLOON_INTERVALS.find(
            (item) => item.afterBead === trueIndex,
          );
          const region = interval
            ? intervalRegion(interval)
            : balloonRegion(trueIndex, bead, balloon);
          return (
            <path
              key={`arc-${trueIndex}`}
              d={arcPath(CX, CY, R, a0, a1)}
              fill="none"
              stroke={
                interval
                  ? "#8a8378"
                  : bead.letter === "O"
                    ? ODD
                    : EVEN
              }
              strokeWidth={launchArc ? 5 : 3}
              strokeLinecap="round"
              strokeDasharray={interval ? "4 3" : undefined}
              opacity={
                regionLit(focus, region)
                  ? launchArc
                    ? 0.85
                    : 0.9
                  : 0.12
              }
            />
          );
        })}
        {IDEAL_BALLOON_INTERVALS.map((interval) => {
          const angle = intervalAngle(interval.afterBead, joinAt, n);
          const x = CX + R * Math.cos(angle);
          const y = CY + R * Math.sin(angle);
          const nx = Math.cos(angle);
          const ny = Math.sin(angle);
          const region = intervalRegion(interval);
          return (
            <g
              key={`interval-${interval.kind}-${interval.afterBead}`}
              opacity={regionLit(focus, region) ? 1 : 0.18}
              role="button"
              tabIndex={0}
              style={onSelectDecision ? { cursor: "pointer" } : undefined}
              onClick={(event) => pick(intervalDecision(interval), event)}
              onKeyDown={
                onSelectDecision
                  ? (event) => {
                      if (event.key === "Enter" || event.key === " ") {
                        event.preventDefault();
                        pick(intervalDecision(interval));
                      }
                    }
                  : undefined
              }
            >
              <line
                x1={x - 9 * nx}
                y1={y - 9 * ny}
                x2={x + 11 * nx}
                y2={y + 11 * ny}
                stroke="#8a8378"
                strokeWidth="2.2"
                strokeDasharray="2 2"
              />
              <text
                x={CX + (R + 28) * nx}
                y={CY + (R + 28) * ny + 4}
                textAnchor="middle"
                fill="#5e574c"
                fontFamily="Source Sans 3, sans-serif"
                fontSize="11"
              >
                {intervalBoundLabel(interval)}
              </text>
            </g>
          );
        })}
        <path
          d={`M ${lastPeak.x} ${lastPeak.y} L ${cycleMin.x} ${cycleMin.y} L ${launch.x} ${launch.y}`}
          fill="none"
          stroke="#1d1914"
          strokeWidth="2.2"
          strokeLinejoin="round"
          opacity={
            regionLit(focus, "balloon-seam") || (joinLit && atCycleMin) ? 1 : 0.18
          }
        />
        {balloon.map((bead, trueIndex) => {
          const display = displayOf(trueIndex, joinAt, n);
          const { x, y } = balloonXY(display, n);
          const caption = balloonCaption(trueIndex, balloon);
          const labelR = R + 26;
          const angle = (display / n) * 2 * Math.PI + Math.PI;
          const region = balloonRegion(trueIndex, bead, balloon);
          const isJoin = trueIndex === joinAt;
          const joinFocus = focus === "join";
          return (
            <Bead
              key={`balloon-${trueIndex}`}
              x={x}
              y={y}
              bead={bead}
              radius={trueIndex === 0 ? beadR + 3 : beadR}
              marked={trueIndex === 0}
              joined={isJoin}
              caption={caption}
              captionX={CX + labelR * Math.cos(angle)}
              captionY={CY + labelR * Math.sin(angle) + 4}
              lit={joinFocus ? isJoin : regionLit(focus, region)}
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
      <div className="mt-2 flex flex-wrap items-center justify-center gap-2">
        <button
          type="button"
          className="rounded-full border border-line px-3 py-1 text-sm"
          onClick={(event) => {
            event.stopPropagation();
            onJoinIndex?.(stepIdealJoin(joinAt, -1, spots));
          }}
        >
          Join left
        </button>
        <button
          type="button"
          className="rounded-full bg-deep px-3 py-1 text-sm text-card disabled:opacity-40"
          disabled={atCycleMin}
          onClick={(event) => {
            event.stopPropagation();
            onJoinIndex?.(0);
          }}
        >
          Snap join to CycleMin
        </button>
        <button
          type="button"
          className="rounded-full border border-line px-3 py-1 text-sm"
          onClick={(event) => {
            event.stopPropagation();
            onJoinIndex?.(stepIdealJoin(joinAt, 1, spots));
          }}
        >
          Join right
        </button>
      </div>
      <p className="mt-1 text-center text-sm text-muted" aria-live="polite">
        Join at {joinName}
        {atCycleMin ? " — the CycleMin placement" : " — not the CycleMin cut"}
        . Six sure letters; interval slots are not stops.
      </p>
      <div
        className="mt-1 flex flex-wrap items-end justify-center gap-1.5"
        aria-label="CycleMin run form with six sure letters and interval bounds"
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
                {run.interval ? (
                  <span className="inline-flex h-7 min-w-7 items-center justify-center border-l-2 border-dashed border-[#8a8378] font-mono text-[11px] text-muted">
                    {run.label}
                  </span>
                ) : (
                  run.beads?.map((bead, letterIndex) => (
                    <RunTile key={`${bead.letter}-${bead.tone}-${letterIndex}`} bead={bead} />
                  ))
                )}
              </span>
              {run.interval ? null : (
                <span className="text-[10px] uppercase tracking-wide text-muted">
                  {run.label}
                </span>
              )}
            </button>
          );
        })}
      </div>
      <p className="mt-2 font-mono text-sm text-ink">
        OOEEEE
        <span className="mx-2 text-muted">+</span>
        intervals
        <span className="mx-2 text-muted">→</span>
        O<sup>a₁</sup>E⋯O<sup>aₑ</sup>E
        <span className="ml-2 font-sans text-muted">
          · a₁≥2 · e≥4 · aₑ∈{"{0,1}"} · period at least 11 · not a cycle
        </span>
      </p>
      <p className="mt-2 text-sm text-muted">
        The cycle is the Lean station list: six sure letters and
        interval slots between them. Extra odds past launch OO have
        minimum 5 and stay unplaced. Extra E past the four forced evens
        have minimum 0. Last odd-run is 0 or 1, not a grey letter.
        Stem OO???E is an optional first visit. Left and right rotate a
        sure letter onto that join.
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
