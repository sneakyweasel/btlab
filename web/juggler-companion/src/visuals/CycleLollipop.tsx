import type { DecisionFocus } from "../content/idealDecisions";
import {
  IDEAL_BALLOON_BEADS,
  IDEAL_BALLOON_INTERVALS,
  idealJoinSpots,
  intervalCountBead,
  stepIdealJoin,
  type BalloonInterval,
  type IdealBead,
} from "../juggler/constants";
import {
  formatNecklaceFill,
  formatOddEvenRuns,
  formatRunWord,
  necklaceFillToRuns,
  oddEvenRuns,
  runsEqual,
  type NecklaceFill,
} from "../juggler/itinerary";
import {
  JOIN_INTERVALS_NOT_STOPS,
  JOIN_VS_WORD_ROTATION,
  idealJoinConfig,
  stemBeadsForJoin,
} from "../juggler/joinConfig";

const CX = 548;
const CY = 160;
const R = 104;
const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const GREY = "#8a8378";
/** Unselected graph stays readable; old 0.12–0.18 erased the ring. */
const FADE = 0.62;
const FADE_UI = 0.68;
const STEM_STEP = 54;

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

function balloonNote(index: number, beads: readonly IdealBead[]): string {
  const sureEvens = beads
    .map((item, itemIndex) =>
      item.letter === "E" && item.tone === "sure" ? itemIndex : -1,
    )
    .filter((itemIndex) => itemIndex >= 0);
  if (index === 0) return "CycleMin";
  if (index === 1) return "launch";
  if (index === sureEvens[0]) return "overshoots";
  if (index === sureEvens[sureEvens.length - 1]) return "lands";
  const evenRank = sureEvens.indexOf(index);
  if (evenRank > 0) return `E ${evenRank + 1}`;
  return "";
}

function balloonCount(index: number): string {
  if (index === 1) return "a₁≥2";
  return "";
}

function intervalNote(interval: BalloonInterval): string {
  if (interval.kind === "a1Extras") return "a₁ extras";
  if (interval.kind === "middle") return "middle odds";
  if (interval.kind === "extraEven") return "extra E";
  return "last odd";
}

function intervalCountGlyph(interval: BalloonInterval): string {
  return interval.max === null
    ? `${interval.min}+`
    : `{${interval.min},${interval.max}}`;
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

function stemCaption(index: number, bead: IdealBead, last: number): string {
  if (index === 0) return "first visit";
  if (index === 1) return "optional";
  if (index === last && bead.letter === "E") return "t even";
  if (index === last) return "t = E|O";
  if (bead.tone === "unknown") return "unknown";
  return "";
}

function stemGlyph(
  index: number,
  bead: IdealBead,
  last: number,
): string | undefined {
  if (index !== last && bead.tone === "unknown") return "0+";
  return undefined;
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
  glyph,
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
  glyph?: string;
  lit?: boolean;
  onPick?: () => void;
}) {
  const paint = beadPaint(bead);
  const shown =
    glyph ?? (bead.letter === "O" && marked ? "n" : bead.letter);
  const glyphSize =
    shown.length >= 5 ? "8" : shown.length >= 3 ? "10" : radius >= 15 ? "13" : "11";
  return (
    <g
      opacity={lit === false ? FADE : 1}
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
        fontSize={glyphSize}
      >
        {shown}
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
  const shown = glyph ?? bead.letter;
  const wide = shown.length > 1;
  return (
    <span
      className="inline-flex items-center justify-center rounded-full font-mono text-xs"
      style={{
        height: size,
        minWidth: wide ? size + 10 : size,
        paddingLeft: wide ? 5 : 0,
        paddingRight: wide ? 5 : 0,
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
      {shown}
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

const CYCLE_TILES: {
  note: string;
  glyph: string;
  decision: string;
  focus: DecisionFocus;
  bead: IdealBead;
}[] = [
  {
    note: "CycleMin",
    glyph: "n",
    decision: "balloon-cut",
    focus: "balloon",
    bead: { letter: "O", tone: "sure" },
  },
  {
    note: "launch",
    glyph: "a₁≥2",
    decision: "balloon-oo",
    focus: "balloon-oo",
    bead: { letter: "O", tone: "sure" },
  },
  {
    note: "a₁ extras",
    glyph: "0+",
    decision: "balloon-fade",
    focus: "balloon-fade",
    bead: { letter: "O", tone: "count" },
  },
  {
    note: "overshoots",
    glyph: "E",
    decision: "balloon-overshoot",
    focus: "balloon-first-e",
    bead: { letter: "E", tone: "sure" },
  },
  {
    note: "middle odds",
    glyph: "0+",
    decision: "balloon-fade",
    focus: "balloon-fade",
    bead: { letter: "O", tone: "count" },
  },
  {
    note: "E 2",
    glyph: "E",
    decision: "balloon-evens",
    focus: "balloon-e",
    bead: { letter: "E", tone: "sure" },
  },
  {
    note: "extra E",
    glyph: "0+",
    decision: "balloon-evens",
    focus: "balloon-e",
    bead: { letter: "E", tone: "count" },
  },
  {
    note: "E 3",
    glyph: "E",
    decision: "balloon-evens",
    focus: "balloon-e",
    bead: { letter: "E", tone: "sure" },
  },
  {
    note: "last odd",
    glyph: "{0,1}",
    decision: "balloon-seam",
    focus: "balloon-seam",
    bead: { letter: "O", tone: "count" },
  },
  {
    note: "lands",
    glyph: "E",
    decision: "balloon-seam",
    focus: "balloon-seam",
    bead: { letter: "E", tone: "sure" },
  },
];

function intervalAngle(afterBead: number, n: number): number {
  const a0 = beadAngle(afterBead, n);
  let a1 = beadAngle((afterBead + 1) % n, n);
  if (a1 <= a0) a1 += 2 * Math.PI;
  return (a0 + a1) / 2;
}

function CycleLeanPanel({
  word,
  fill,
  lit,
  onPick,
}: {
  word?: string;
  fill?: NecklaceFill | null;
  lit: boolean;
  onPick: (id: string) => void;
}) {
  const runs = word ? oddEvenRuns(word) : null;
  const projected = fill ? necklaceFillToRuns(fill) : null;
  const matchesFill = Boolean(runs && projected && runsEqual(runs, projected));
  return (
    <button
      type="button"
      data-keep-focus
      className="mt-2 block w-full rounded-lg border border-line bg-card px-3 py-2 text-left"
      style={{ opacity: lit ? 1 : 0.72 }}
      onClick={() => onPick("balloon-run")}
    >
      <p className="text-xs uppercase tracking-wide text-muted">
        On the cycle, not the stem — cycleMin_has_full_odd_even_run_form
      </p>
      <p className="mt-1 font-mono text-sm text-ink">
        {runs
          ? `w = ${formatRunWord(runs)}   ${formatOddEvenRuns(runs)}`
          : "w = O^a1 E ... O^ae E   with a1 >= 2, ae <= 1, e = #E"}
      </p>
      <p className="mt-1 text-xs text-muted">
        {runs && projected && matchesFill
          ? `This leftover equals toRuns of assembleFill ${formatNecklaceFill(fill!)}. The ring above is that bunched projection (OO+EEEE), not a reconstruction.`
          : runs
            ? "This leftover has interior runs the four-slot ring forgets. The bead schema is a projection of the Lean list, not assembleFill."
            : "The ring and the OOEEEE strip are a projection of this Lean list onto six sure letters. Sure links are only launch OO and wrap EO."}
      </p>
    </button>
  );
}

export function CycleLollipop({
  focus,
  joinIndex = 0,
  word,
  fill = null,
  onJoinIndex,
  onSelectDecision,
  onClearFocus,
}: {
  focus?: DecisionFocus;
  joinIndex?: number;
  word?: string;
  fill?: NecklaceFill | null;
  onJoinIndex?: (index: number) => void;
  onSelectDecision?: (id: string) => void;
  onClearFocus?: () => void;
}) {
  const balloon = IDEAL_BALLOON_BEADS;
  const n = balloon.length;
  const spots = idealJoinSpots(balloon);
  const joinAt = spots.includes(joinIndex) ? joinIndex : 0;
  const stemBeads = stemBeadsForJoin(joinAt);
  const stemLastX = 36 + (stemBeads.length - 1) * STEM_STEP;
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
  const stem = stemBeads.map((bead, index) => ({
    x: 36 + index * STEM_STEP,
    bead,
    region: stemRegion(index, stemBeads.length - 1),
    label: stemCaption(index, bead, stemBeads.length - 1),
    glyph: stemGlyph(index, bead, stemBeads.length - 1),
  }));
  const joinCfg = idealJoinConfig(joinAt, balloon);
  const beadR = Math.min(14, Math.max(9, (Math.PI * R) / n - 1.2));
  const joinLit = regionLit(focus, "join");
  const joinName = joinCfg.name;
  const atCycleMin = joinAt === 0;
  const joinColor = letterColor(
    stemBeads[stemBeads.length - 1]?.letter ?? "?",
  );

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
                      style={{ opacity: lit ? 1 : FADE_UI }}
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
          The cycle is a projection of the Lean run list
          O^a1 E ... O^ae E onto six sure letters. Not an assembleFill
          reconstruction.
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
              stroke={letterColor(item.bead.letter)}
              strokeWidth="2.2"
              strokeLinecap="round"
              strokeDasharray={unsure ? "3 3" : undefined}
              opacity={regionLit(focus, item.region) ? 1 : FADE}
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
            glyph={item.glyph}
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
          const mid = interval
            ? intervalAngle(interval.afterBead, n)
            : null;
          const opacity = regionLit(focus, region)
            ? launchArc
              ? 0.85
              : 0.9
            : FADE;
          const segments =
            interval && mid !== null
              ? [
                  { from: a0, to: mid, color: letterColor(bead.letter) },
                  {
                    from: mid,
                    to: a1,
                    color: letterColor(intervalCountBead(interval).letter),
                  },
                ]
              : [{ from: a0, to: a1, color: letterColor(bead.letter) }];
          return segments.map((segment, segmentIndex) => (
            <path
              key={`arc-${trueIndex}-${segmentIndex}`}
              d={arcPath(CX, CY, R, segment.from, segment.to)}
              fill="none"
              stroke={segment.color}
              strokeWidth={launchArc ? 5 : 3}
              strokeLinecap="round"
              strokeDasharray={interval ? "3 3" : undefined}
              opacity={opacity}
            />
          ));
        })}
        {IDEAL_BALLOON_INTERVALS.map((interval) => {
          const angle = intervalAngle(interval.afterBead, n);
          const x = CX + R * Math.cos(angle);
          const y = CY + R * Math.sin(angle);
          const region = intervalRegion(interval);
          return (
            <g
              key={`interval-${interval.kind}-${interval.afterBead}`}
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
                radius={beadR + 1}
                glyph={intervalCountGlyph(interval)}
                caption={intervalNote(interval)}
                captionX={alongRay(angle, R + beadR + 16).x}
                captionY={alongRay(angle, R + beadR + 16).y}
                lit={regionLit(focus, region)}
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
            regionLit(focus, "balloon-seam") || (joinLit && atCycleMin)
              ? 1
              : FADE
          }
        />
        <path
          d={arcPath(CX, CY, R, beadAngle(0, n), beadAngle(1, n))}
          fill="none"
          stroke={ODD}
          strokeWidth="2.2"
          strokeLinecap="round"
          opacity={
            regionLit(focus, "balloon-seam") || (joinLit && atCycleMin)
              ? 1
              : FADE
          }
        />
        <path
          d={joinPath}
          fill="none"
          stroke={joinColor}
          strokeWidth="2.2"
          strokeLinecap="round"
          opacity={joinLit ? 1 : FADE}
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
          opacity={joinLit ? 1 : FADE}
          style={onSelectDecision ? { cursor: "pointer" } : undefined}
          role="button"
          onClick={(event) => pick("join-seam", event)}
        >
          {atCycleMin ? "join · CycleMin" : `join · ${joinName}`}
      </text>
        {balloon.map((bead, trueIndex) => {
          const { x, y } = balloonXY(trueIndex, n);
          const angle = beadAngle(trueIndex, n);
          const note = balloonNote(trueIndex, balloon);
          const count = balloonCount(trueIndex);
          const radius = trueIndex === 0 || count ? beadR + 4 : beadR;
          const outer =
            trueIndex === 0
              ? { x, y: y - radius - 14 }
              : alongRay(angle, R + radius + 16);
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
              glyph={count || undefined}
              caption={note}
              captionX={outer.x}
              captionY={outer.y}
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
          y={CY - 8}
              textAnchor="middle"
          fill="#1d1914"
          fontFamily="Fraunces, ui-serif, Georgia, serif"
          fontSize="20"
          style={onSelectDecision ? { cursor: "pointer" } : undefined}
          role="button"
          onClick={(event) => pick("balloon-run", event)}
        >
          Cycle
            </text>
              <text
          x={CX}
          y={CY + 10}
          textAnchor="middle"
                fill="#5e574c"
                fontFamily="Source Sans 3, sans-serif"
                fontSize="11"
          style={onSelectDecision ? { cursor: "pointer" } : undefined}
          role="button"
          onClick={(event) => pick("balloon-run", event)}
        >
          Lean run projection
        </text>
        <text
          x={CX}
          y={CY + 24}
          textAnchor="middle"
          fill="#5e574c"
          fontFamily="Source Sans 3, sans-serif"
          fontSize="10"
          style={onSelectDecision ? { cursor: "pointer" } : undefined}
          role="button"
          onClick={(event) => pick("balloon-run", event)}
        >
          O^a1 E ... O^ae E
        </text>
        <text
          x={alongRay((beadAngle(0, n) + beadAngle(1, n)) / 2, R - 34).x}
          y={alongRay((beadAngle(0, n) + beadAngle(1, n)) / 2, R - 34).y}
          textAnchor="middle"
          fill={ODD}
          fontFamily="Source Sans 3, sans-serif"
          fontSize="10"
          opacity={
            regionLit(focus, "balloon-oo") ||
            regionLit(focus, "balloon-seam") ||
            regionLit(focus, "balloon")
              ? 1
              : FADE
          }
          style={onSelectDecision ? { cursor: "pointer" } : undefined}
          role="button"
          onClick={(event) => pick("balloon-links", event)}
        >
          sure OO
        </text>
        <text
          x={alongRay(intervalAngle(n - 1, n), R + 28).x}
          y={alongRay(intervalAngle(n - 1, n), R + 28).y}
          textAnchor="middle"
          fill={EVEN}
          fontFamily="Source Sans 3, sans-serif"
          fontSize="10"
          opacity={
            regionLit(focus, "balloon-oo") ||
            regionLit(focus, "balloon-seam") ||
            regionLit(focus, "balloon")
              ? 1
              : FADE
          }
          style={onSelectDecision ? { cursor: "pointer" } : undefined}
          role="button"
          onClick={(event) => pick("balloon-links", event)}
        >
          sure EO
              </text>
        <defs />
      </svg>
      <div className="mt-3 grid gap-3">
        <div>
          <p className="text-[10px] uppercase tracking-wide text-muted">
            Stem
          </p>
          <div
            className="mt-1.5 flex flex-wrap items-end justify-center gap-2"
            aria-label="Stem tiles"
          >
            {stem.map((item, index) => (
              <button
                key={`stem-tile-${index}`}
                type="button"
                className="grid justify-items-center gap-0.5"
                style={{
                  opacity: regionLit(focus, item.region) ? 1 : FADE_UI,
                }}
                onClick={(event) => pick(stemDecision(item.region), event)}
              >
                <RunTile
                  bead={item.bead}
                  glyph={item.glyph ?? item.bead.letter}
                />
                <span className="text-[10px] text-muted">{item.label}</span>
              </button>
            ))}
          </div>
        </div>
        <div>
          <p className="text-[10px] uppercase tracking-wide text-muted">
            Idealized cycle
          </p>
          <div
            className="mt-1.5 flex flex-wrap items-end justify-center gap-1.5"
            aria-label="Idealized cycle tiles: Lean schema projection onto six sure letters"
          >
            {CYCLE_TILES.map((tile, index) => (
              <button
                key={`${tile.note}-${index}`}
                type="button"
                className="grid justify-items-center gap-0.5"
                style={{
                  opacity: regionLit(focus, tile.focus) ? 1 : FADE_UI,
                }}
                onClick={(event) => pick(tile.decision, event)}
              >
                <RunTile bead={tile.bead} glyph={tile.glyph} />
                <span className="text-[10px] text-muted">{tile.note}</span>
              </button>
            ))}
          </div>
        </div>
      </div>
      <CycleLeanPanel
        word={word}
        fill={fill}
        lit={!focus || focus === "figure" || focus.startsWith("balloon")}
        onPick={(id) => pick(id)}
      />
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
      <button
        type="button"
        data-keep-focus
        className="mt-2 block w-full rounded-lg border border-line bg-card px-3 py-2 text-left"
        style={{ opacity: joinLit || !focus ? 1 : 0.72 }}
        onClick={() => pick("join-seam")}
      >
        <p className="text-xs uppercase tracking-wide text-muted">
          Join at {joinCfg.name}
          {atCycleMin ? " — CycleMin cut" : " — same loop, not the CycleMin cut"}
        </p>
        <p className="mt-1 font-mono text-sm text-ink">
          vertex {joinCfg.vertex} · cycle arrives {joinCfg.arrival} · stem t is{" "}
          {joinCfg.stemTerminal === "E" ? "even" : "E or O"}
        </p>
        <p className="mt-1 text-sm text-ink">
          Cyclic parent: {joinCfg.cycleParent}
        </p>
        <p className="mt-1 text-sm text-ink">Stem parent: {joinCfg.stem}</p>
        <p className="mt-1 text-xs text-muted">{joinCfg.arrivalWhy}</p>
        <ul className="mt-1 list-disc pl-4 text-xs text-muted">
          {joinCfg.forbidden.map((item) => (
            <li key={item}>{item}</li>
          ))}
        </ul>
        <p className="mt-1 text-xs text-muted">{joinCfg.lean}</p>
        <p className="mt-1 text-xs text-muted">{JOIN_INTERVALS_NOT_STOPS}</p>
        <p className="mt-1 text-xs text-muted">{JOIN_VS_WORD_ROTATION}</p>
      </button>
      <p className="mt-2 font-mono text-sm text-ink">
        OOEEEE
        <span className="mx-2 text-muted">+</span>
        intervals
        <span className="mx-2 text-muted">→</span>
        bead projection of the Lean run list
        <span className="ml-2 font-sans text-muted">
          · a₁≥2 · e≥4 · o≥7 · aₑ∈{"{0,1}"} · not a cycle
        </span>
      </p>
      <p className="mt-2 text-sm text-muted">
        The cycle is a Lean candidate schema: six sure letters and
        interval slots between them. The full e-run is Lean; the schema
        is a projection of that run list, not an assembleFill
        reconstruction. Extra odds
        past launch OO have minimum 5 and stay unplaced. Extra E past
        the four forced evens have minimum 0. Last odd-run is 0 or 1.
        Counts sit in the beads; notes sit outside. The stem middle
        is one 0+ slot, same convention as the cycle intervals. The
        last bead follows the join:
        even-only when the cycle arrives O, E or O at the valley or
        an E-arrival. Links keep the previous bead’s color. Left and
        right walk the join around the six sure letters. Necklace
        rotate is not this walker.
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
