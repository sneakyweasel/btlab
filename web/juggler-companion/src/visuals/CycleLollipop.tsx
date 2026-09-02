import type { DecisionFocus } from "../content/idealDecisions";
import {
  IDEAL_BALLOON_BEADS,
  IDEAL_BALLOON_INTERVALS,
  IDEAL_STRING_BEADS,
  idealJoinLabel,
  idealJoinSpots,
  intervalBoundLabel,
  intervalCountBead,
  stepIdealJoin,
  type BalloonInterval,
  type IdealBead,
} from "../juggler/constants";

const CX = 548;
const CY = 160;
const R = 104;
const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const GREY = "#8a8378";

function letterColor(letter: IdealBead["letter"]): string {
  if (letter === "O") return ODD;
  if (letter === "E") return EVEN;
  return GREY;
}

function beadAngle(index: number, n: number): number {
  return (index / Math.max(n, 1)) * 2 * Math.PI + Math.PI;
}

function balloonXY(index: number, n: number): { x: number; y: number } {
  const angle = beadAngle(index, n);
  return { x: CX + R * Math.cos(angle), y: CY + R * Math.sin(angle) };
}

function minorArcDelta(from: number, to: number): number {
  const tau = 2 * Math.PI;
  const a0 = ((from % tau) + tau) % tau;
  const a1 = ((to % tau) + tau) % tau;
  let delta = a1 - a0;
  if (delta > Math.PI) delta -= tau;
  if (delta < -Math.PI) delta += tau;
  return delta;
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
    return {
      fill: "#fffdf7",
      stroke: fill,
      dash: "3 2",
      text: fill,
      opacity: 1,
    };
  }
  return { fill, stroke: "none", text: "#fffdf7", opacity: 1 };
}

function balloonRole(index: number, beads: readonly IdealBead[]): string {
  const sureEvens = beads
    .map((item, itemIndex) =>
      item.letter === "E" && item.tone === "sure" ? itemIndex : -1,
    )
    .filter((itemIndex) => itemIndex >= 0);
  if (index === 0) return "min";
  if (index === sureEvens[0]) return "first E";
  if (index === sureEvens[sureEvens.length - 1]) return "last E";
  if (sureEvens.includes(index)) return "E";
  return "";
}

function balloonCount(index: number): string {
  if (index === 1) return "a₁≥2";
  return "";
}

function alongRay(angle: number, radius: number): { x: number; y: number } {
  return { x: CX + radius * Math.cos(angle), y: CY + radius * Math.sin(angle) + 4 };
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
  innerCaption,
  innerX,
  innerY,
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
  innerCaption?: string;
  innerX?: number;
  innerY?: number;
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
      {innerCaption ? (
        <text
          x={innerX ?? x}
          y={innerY ?? y}
          textAnchor="middle"
          fill="#5e574c"
          stroke="#fffdf7"
          strokeWidth="4"
          paintOrder="stroke"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="11"
        >
          {innerCaption}
        </text>
      ) : null}
      {caption ? (
        <text
          x={captionX ?? x}
          y={captionY ?? y + radius + 16}
          textAnchor="middle"
          fill="#5e574c"
          stroke="#fffdf7"
          strokeWidth="4"
          paintOrder="stroke"
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
            ? `1px dashed ${paint.stroke}`
            : "none",
        boxSizing: "border-box",
      }}
    >
      {glyph ?? bead.letter}
    </span>
  );
}

const LEGEND_GROUPS: {
  title: string;
  items: {
    id: string;
    decision: string;
    focus: DecisionFocus;
    label: string;
    mark: "o" | "e" | "unknown" | "dotted" | "plain" | "text";
  }[];
}[] = [
  {
    title: "Parity",
    items: [
      { id: "parity-o", decision: "balloon-oo", focus: "balloon-oo", label: "O", mark: "o" },
      { id: "parity-e", decision: "balloon-evens", focus: "balloon-e", label: "E", mark: "e" },
      { id: "parity-q", decision: "string-grey", focus: "string-grey", label: "?", mark: "unknown" },
    ],
  },
  {
    title: "Certainty",
    items: [
      { id: "cert-dotted", decision: "balloon-fade", focus: "balloon-fade", label: "dotted", mark: "dotted" },
      { id: "cert-plain", decision: "balloon-oo", focus: "balloon-oo", label: "plain", mark: "plain" },
    ],
  },
  {
    title: "Count",
    items: [
      { id: "count-0p", decision: "balloon-fade", focus: "balloon-fade", label: "0+", mark: "text" },
      { id: "count-01", decision: "balloon-seam", focus: "balloon-seam", label: "{0,1}", mark: "text" },
      { id: "count-ge2", decision: "balloon-oo", focus: "balloon-oo", label: "≥ 2", mark: "text" },
    ],
  },
];

function legendMark(mark: (typeof LEGEND_GROUPS)[number]["items"][number]["mark"]) {
  if (mark === "o") return <RunTile bead={{ letter: "O", tone: "sure" }} size={22} />;
  if (mark === "e") return <RunTile bead={{ letter: "E", tone: "sure" }} size={22} />;
  if (mark === "unknown") return <RunTile bead={{ letter: "?", tone: "unknown" }} size={22} />;
  if (mark === "dotted") {
    return <RunTile bead={{ letter: "?", tone: "unknown" }} glyph="" size={22} />;
  }
  if (mark === "plain") {
    return (
      <span
        aria-hidden
        className="inline-block rounded-full"
        style={{ height: 22, width: 22, background: "#1d1914" }}
      />
    );
  }
  return null;
}

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
  { label: "0+", decision: "balloon-fade", focus: "balloon-fade", beads: [{ letter: "O", tone: "count" }] },
  { label: "first E", decision: "balloon-overshoot", focus: "balloon-first-e", beads: [{ letter: "E", tone: "sure" }] },
  { label: "0+", decision: "balloon-fade", focus: "balloon-fade", beads: [{ letter: "O", tone: "count" }] },
  { label: "E", decision: "balloon-evens", focus: "balloon-e", beads: [{ letter: "E", tone: "sure" }] },
  { label: "0+", decision: "balloon-evens", focus: "balloon-e", beads: [{ letter: "E", tone: "count" }] },
  { label: "E", decision: "balloon-evens", focus: "balloon-e", beads: [{ letter: "E", tone: "sure" }] },
  { label: "0 or 1", decision: "balloon-seam", focus: "balloon-seam", beads: [{ letter: "O", tone: "count" }] },
  { label: "last E", decision: "balloon-seam", focus: "balloon-seam", beads: [{ letter: "E", tone: "sure" }] },
];

function intervalAngle(afterBead: number, n: number): number {
  const a0 = beadAngle(afterBead, n);
  let a1 = beadAngle((afterBead + 1) % n, n);
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
  const stemLastX = 36 + (IDEAL_STRING_BEADS.length - 1) * 44;
  const entry = balloonXY(0, n);
  const joinPoint = balloonXY(joinAt, n);
  const entryAngle = beadAngle(0, n);
  const destAngle = beadAngle(joinAt, n);
  const joinDelta = minorArcDelta(entryAngle, destAngle);
  const joinSweep = joinDelta >= 0 ? 1 : 0;
  const joinMid = entryAngle + joinDelta / 2;
  const joinPath =
    joinAt === 0
      ? `M ${stemLastX} ${CY} L ${joinPoint.x} ${joinPoint.y}`
      : `M ${stemLastX} ${CY} L ${entry.x} ${entry.y} A ${R} ${R} 0 0 ${joinSweep} ${joinPoint.x} ${joinPoint.y}`;
  const joinLabel =
    joinAt === 0
      ? { x: (stemLastX + entry.x) / 2, y: CY - 22 }
      : {
          x: CX + (R + 38) * Math.cos(joinMid),
          y: CY + (R + 38) * Math.sin(joinMid) + 4,
        };
  const stem = IDEAL_STRING_BEADS.map((bead, index) => ({
    x: 36 + index * 44,
    bead,
    region: stemRegion(index, IDEAL_STRING_BEADS.length - 1),
    label: stemCaption(index, bead),
  }));
  const beadR = Math.min(14, Math.max(9, (Math.PI * R) / n - 1.2));
  const joinLit = regionLit(focus, "join");
  const joinName = idealJoinLabel(joinAt, balloon);
  const atCycleMin = joinAt === 0;
  const joinColor = letterColor(balloon[joinAt]?.letter ?? "?");

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
      <ul
        className="flex flex-wrap items-center gap-x-6 gap-y-2"
        aria-label="Figure legend"
      >
        {LEGEND_GROUPS.map((group) => (
          <li key={group.title} className="flex flex-wrap items-center gap-2">
            <span className="text-[10px] uppercase tracking-wide text-muted">
              {group.title}
            </span>
            <ul className="flex flex-wrap items-center gap-2">
              {group.items.map((item) => {
                const lit =
                  item.focus === "balloon-oo"
                    ? regionLit(focus, "balloon-oo") ||
                      regionLit(focus, "balloon-e") ||
                      regionLit(focus, "balloon-first-e")
                    : regionLit(focus, item.focus);
                const named = item.mark === "dotted" || item.mark === "plain" || item.mark === "text";
                return (
                  <li key={item.id}>
                    <button
                      type="button"
                      className="flex items-center gap-1.5 text-left"
                      style={{ opacity: lit ? 1 : 0.28 }}
                      onClick={(event) => pick(item.decision, event)}
                    >
                      {legendMark(item.mark)}
                      {named ? (
                        <span className="font-mono text-xs text-muted">{item.label}</span>
                      ) : null}
                    </button>
                  </li>
                );
              })}
            </ul>
          </li>
        ))}
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
          x={(stem[0].x + stem[Math.max(stem.length - 2, 0)].x) / 2}
          y={CY - 44}
          textAnchor="middle"
          fill="#1d1914"
          fontFamily="Fraunces, ui-serif, Georgia, serif"
          fontSize="20"
        >
          Stem
        </text>
        {stem.slice(0, -1).map((item, index) => {
          const next = stem[index + 1];
          const unsure =
            item.bead.tone !== "sure" || next.bead.tone !== "sure";
          return (
            <line
              key={`stem-link-${index}`}
              x1={item.x}
              y1={CY}
              x2={next.x}
              y2={CY}
              stroke={unsure ? GREY : letterColor(item.bead.letter)}
              strokeWidth="2.2"
              strokeLinecap="round"
              strokeDasharray={unsure ? "3 3" : undefined}
            />
          );
        })}
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
        {balloon.map((bead, trueIndex) => {
          const a0 = beadAngle(trueIndex, n);
          const a1 = beadAngle(trueIndex + 1, n);
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
              stroke={interval ? GREY : letterColor(bead.letter)}
              strokeWidth={launchArc ? 5 : 3}
              strokeLinecap="round"
              strokeDasharray={interval ? "3 3" : undefined}
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
          const angle = intervalAngle(interval.afterBead, n);
          const x = CX + R * Math.cos(angle);
          const y = CY + R * Math.sin(angle);
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
              <Bead
                x={x}
                y={y}
                bead={intervalCountBead(interval)}
                radius={beadR - 1}
                caption={intervalBoundLabel(interval)}
                captionX={alongRay(angle, R + (beadR - 1) + 16).x}
                captionY={alongRay(angle, R + (beadR - 1) + 16).y}
              />
            </g>
          );
        })}
        <path
          d={arcPath(CX, CY, R, beadAngle(n - 1, n), beadAngle(n, n))}
          fill="none"
          stroke={EVEN}
          strokeWidth="2.2"
          strokeLinecap="round"
          opacity={
            regionLit(focus, "balloon-seam") || (joinLit && atCycleMin) ? 1 : 0.18
          }
        />
        <path
          d={arcPath(CX, CY, R, beadAngle(0, n), beadAngle(1, n))}
          fill="none"
          stroke={ODD}
          strokeWidth="2.2"
          strokeLinecap="round"
          opacity={
            regionLit(focus, "balloon-seam") || (joinLit && atCycleMin) ? 1 : 0.18
          }
        />
        <path
          d={joinPath}
          fill="none"
          stroke={joinColor}
          strokeWidth="2.2"
          strokeLinecap="round"
          opacity={joinLit ? 1 : 0.18}
          style={onSelectDecision ? { cursor: "pointer" } : undefined}
          role="button"
          onClick={(event) => pick("join-seam", event)}
        />
        <text
          x={joinLabel.x}
          y={joinLabel.y}
          textAnchor="middle"
          fill="#1d1914"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="11"
          opacity={joinLit ? 1 : 0.18}
          style={onSelectDecision ? { cursor: "pointer" } : undefined}
          role="button"
          onClick={(event) => pick("join-seam", event)}
        >
          {atCycleMin ? "join · CycleMin" : `join · ${joinName}`}
        </text>
        {balloon.map((bead, trueIndex) => {
          const { x, y } = balloonXY(trueIndex, n);
          const angle = beadAngle(trueIndex, n);
          const role = balloonRole(trueIndex, balloon);
          const count = balloonCount(trueIndex);
          const radius = trueIndex === 0 ? beadR + 3 : beadR;
          const inner = alongRay(angle, R - radius - 16);
          const outer = alongRay(angle, R + radius + 16);
          const region = balloonRegion(trueIndex, bead, balloon);
          const isJoin = trueIndex === joinAt;
          const joinFocus = focus === "join";
          return (
            <Bead
              key={`balloon-${trueIndex}`}
              x={x}
              y={y}
              bead={bead}
              radius={radius}
              marked={trueIndex === 0}
              joined={isJoin}
              caption={count}
              captionX={outer.x}
              captionY={outer.y}
              innerCaption={role}
              innerX={inner.x}
              innerY={inner.y}
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
          y={CY - 2}
          textAnchor="middle"
          fill="#1d1914"
          fontFamily="Fraunces, ui-serif, Georgia, serif"
          fontSize="20"
        >
          Cycle
        </text>
        <text
          x={CX}
          y={CY + 16}
          textAnchor="middle"
          fill="#5e574c"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="11"
        >
          L≥11
        </text>
        <defs />
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
              {run.label ? (
                <span className="text-[10px] uppercase tracking-wide text-muted">
                  {run.label}
                </span>
              ) : null}
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
        Stem OO???E is an optional first visit. Left and right walk the
        join around the six sure letters.
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
