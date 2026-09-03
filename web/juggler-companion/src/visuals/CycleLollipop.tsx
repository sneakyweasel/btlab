import { memo, useCallback, type KeyboardEvent, type MouseEvent, type ReactNode } from "react";
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
import { Tex } from "../components/Tex";
import {
  formatNecklaceFill,
  formatOddEvenRuns,
  formatRunWordTex,
  necklaceFillToRuns,
  oddEvenRuns,
  runsEqual,
  type NecklaceFill,
} from "../juggler/itinerary";
import {
  JOIN_INTERVALS_NOT_STOPS,
  JOIN_VS_WORD_ROTATION,
  idealJoinConfig,
} from "../juggler/joinConfig";
import {
  joinFigure,
  paintStem,
  siteAtIndex,
  type FigureMark,
  type PaintedBead,
  type StemDisplayMode,
} from "../juggler/lollipop";

const STATIONS = 10;
const BEAD_R = 13;
const STEP = 42;
const R = STEP / (2 * Math.sin(Math.PI / STATIONS));
const STEM_STEP = STEP;
const STEM_MAX = 4;
const JOIN_ANGLE = Math.PI / 2;
const TITLE_ABOVE = BEAD_R + 22;
const CX = 180;
const CY = TITLE_ABOVE + R + 12;
const JOIN_Y = CY + R;
const VIEW_W = 360;
const VIEW_H = Math.ceil(JOIN_Y + STEM_MAX * STEP + BEAD_R + 36);
const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const GREY = "#8a8378";
const BALLOON = IDEAL_BALLOON_BEADS;
const N = BALLOON.length;
const JOIN_SPOTS = idealJoinSpots(BALLOON);

function letterColor(letter: IdealBead["letter"]): string {
  if (letter === "O") return ODD;
  if (letter === "E") return EVEN;
  return GREY;
}

function sureSlot(sureIndex: number): number {
  return sureIndex <= 1 ? sureIndex : 2 * sureIndex - 1;
}

function stationAngle(slot: number, joinAt = 0): number {
  return ((slot - sureSlot(joinAt)) / STATIONS) * 2 * Math.PI + JOIN_ANGLE;
}

function beadAngle(index: number, joinAt = 0): number {
  return stationAngle(sureSlot(index), joinAt);
}

function atAngle(angle: number, radius: number, dy = 0): { x: number; y: number } {
  return { x: CX + radius * Math.cos(angle), y: CY + radius * Math.sin(angle) + dy };
}

function arcSweep(a0: number, a1: number): number {
  return (a1 - a0 + 2 * Math.PI) % (2 * Math.PI);
}

function arcPath(a0: number, a1: number): string {
  const x0 = CX + R * Math.cos(a0);
  const y0 = CY + R * Math.sin(a0);
  const x1 = CX + R * Math.cos(a1);
  const y1 = CY + R * Math.sin(a1);
  const sweep = arcSweep(a0, a1);
  return `M ${x0} ${y0} A ${R} ${R} 0 ${sweep > Math.PI ? 1 : 0} 1 ${x1} ${y1}`;
}

function cwArrow(a0: number, a1: number): { x: number; y: number; deg: number } {
  const tip = a0 + arcSweep(a0, a1) / 2;
  const { x, y } = atAngle(tip, R);
  return {
    x,
    y,
    deg: (Math.atan2(Math.cos(tip), -Math.sin(tip)) * 180) / Math.PI,
  };
}

function pointedArcPath(a0: number, a1: number): string {
  const sweep = arcSweep(a0, a1);
  const rim = Math.asin(Math.min(1, (BEAD_R + 0.4) / R));
  const start = a0 + rim;
  const span = sweep - 2 * rim;
  const steps = 10;
  const halfW = 2.7;
  const outer: string[] = [];
  const inner: string[] = [];
  for (let i = 0; i <= steps; i += 1) {
    const t = i / steps;
    const ang = start + span * t;
    const w = halfW * (1 - t);
    const o = atAngle(ang, R + w);
    const n = atAngle(ang, R - w);
    outer.push(`${o.x} ${o.y}`);
    inner.push(`${n.x} ${n.y}`);
  }
  return `M ${outer.join(" L ")} L ${inner.reverse().join(" L ")} Z`;
}

function intervalAngle(afterBead: number, joinAt = 0): number {
  return stationAngle(sureSlot(afterBead) + 1, joinAt);
}

function beadMark(bead: IdealBead | PaintedBead): FigureMark | undefined {
  return "mark" in bead ? bead.mark : undefined;
}

function beadPaint(bead: IdealBead | PaintedBead): {
  fill: string;
  stroke: string;
  dash?: string;
  text: string;
} {
  const mark = beadMark(bead);
  if (mark === "optional" || mark === "offFigure") {
    const fill = letterColor(bead.letter);
    return { fill: "#fffdf7", stroke: fill, dash: "4 3", text: fill };
  }
  if (bead.tone === "unknown" || mark === "unknown") {
    return { fill: "#fffdf7", stroke: GREY, dash: "3 2", text: GREY };
  }
  const fill = bead.letter === "O" ? ODD : EVEN;
  if (bead.tone === "count" || mark === "leftover") {
    return { fill: "#fffdf7", stroke: fill, dash: "3 2", text: fill };
  }
  return { fill, stroke: "none", text: "#fffdf7" };
}

function intervalBoundCaption(interval: BalloonInterval): string {
  return interval.max === null ? "≥0" : `{${interval.min},${interval.max}}`;
}

function regionLit(focus: DecisionFocus | undefined, region: DecisionFocus): boolean {
  if (!focus || focus === "figure") return true;
  if (focus === "none") return false;
  if (focus === region) return true;
  if (focus === "string" && region.startsWith("string")) return true;
  if (focus === "balloon" && region.startsWith("balloon")) return true;
  if (focus === "join" && (region === "join" || region === "string-e")) return true;
  if (focus === "balloon-e" && region === "balloon-first-e") return true;
  return false;
}

function fadeClass(lit: boolean): string | undefined {
  return lit ? undefined : "stem-cycle-dim";
}

function stemRegion(index: number, last: number): DecisionFocus {
  if (index <= 1) return "string-oo";
  if (index === last) return "string-e";
  return "string-grey";
}

function balloonRegion(index: number, bead: IdealBead): DecisionFocus {
  const firstSureEven = BALLOON.findIndex(
    (item) => item.letter === "E" && item.tone === "sure",
  );
  if (index <= 1) return "balloon-oo";
  if (index === N - 1) return "balloon-seam";
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

type StemItem = {
  x: number;
  y: number;
  bead: IdealBead | PaintedBead;
  region: DecisionFocus;
  caption?: string;
};

function stemBoundCaption(bead: PaintedBead): string | undefined {
  return bead.caption === "≥0" ? "≥0" : undefined;
}

function stemItemsFromPainted(beads: readonly PaintedBead[]): StemItem[] {
  const last = beads.length - 1;
  return beads.map((bead, index) => ({
    x: CX,
    y: JOIN_Y + (beads.length - index) * STEM_STEP,
    bead,
    region:
      bead.mark === "optional"
        ? "string-oo"
        : index === last
          ? "string-e"
          : stemRegion(index, last),
    caption: stemBoundCaption(bead),
  }));
}

function stemForJoin(joinAt: number, mode: StemDisplayMode): StemItem[] {
  return stemItemsFromPainted(paintStem(mode, joinFigure(siteAtIndex(joinAt), joinAt)));
}

type ArcSeg = {
  key: string;
  d: string;
  color: string;
  dashed: boolean;
  region: DecisionFocus;
  arrow?: { x: number; y: number; deg: number };
  pointed?: string;
};

function stationLetter(slot: number): IdealBead["letter"] {
  if (slot === 0 || slot === 1) return "O";
  const interval = IDEAL_BALLOON_INTERVALS.find(
    (item) => sureSlot(item.afterBead) + 1 === slot,
  );
  if (interval) return intervalCountBead(interval).letter;
  return "E";
}

function intervalAtSlot(slot: number): BalloonInterval | undefined {
  return IDEAL_BALLOON_INTERVALS.find(
    (item) => sureSlot(item.afterBead) + 1 === slot,
  );
}

function arcRegion(slot: number): DecisionFocus {
  const here = intervalAtSlot(slot);
  if (here) return intervalRegion(here);
  const next = intervalAtSlot((slot + 1) % STATIONS);
  if (next) return intervalRegion(next);
  if (slot === 0) return "balloon-oo";
  return "balloon-seam";
}

function balloonArcs(joinAt: number): ArcSeg[] {
  return Array.from({ length: STATIONS }, (_, slot) => {
    const next = (slot + 1) % STATIONS;
    const a0 = stationAngle(slot, joinAt);
    const a1 = stationAngle(next, joinAt);
    const dashed = Boolean(intervalAtSlot(slot) || intervalAtSlot(next));
    return {
      key: `arc-${slot}`,
      d: arcPath(a0, a1),
      color: letterColor(stationLetter(slot)),
      dashed,
      region: arcRegion(slot),
      arrow: dashed ? undefined : cwArrow(a0, a1),
      pointed: dashed ? pointedArcPath(a0, a1) : undefined,
    };
  });
}

type FigureNode = {
  key: string;
  x: number;
  y: number;
  bead: IdealBead;
  radius: number;
  glyph?: string;
  caption?: string;
  captionX?: number;
  captionY?: number;
  region: DecisionFocus;
  decision: string;
  marked?: boolean;
  index?: number;
};

function balloonNodes(joinAt: number): FigureNode[] {
  return BALLOON.map((bead, index) => {
    const angle = beadAngle(index, joinAt);
    const { x, y } = atAngle(angle, R);
    const region = balloonRegion(index, bead);
    return {
      key: `balloon-${index}`,
      x,
      y,
      bead,
      radius: BEAD_R,
      region,
      decision: index === 0 ? "balloon-cut" : balloonDecision(region),
      marked: index === 0,
      index,
    };
  });
}

function intervalNodes(joinAt: number): FigureNode[] {
  return IDEAL_BALLOON_INTERVALS.map((interval) => {
    const { x, y } = atAngle(intervalAngle(interval.afterBead, joinAt), R);
    const region = intervalRegion(interval);
    return {
      key: `interval-${interval.kind}`,
      x,
      y,
      bead: intervalCountBead(interval),
      radius: BEAD_R,
      caption: intervalBoundCaption(interval),
      region,
      decision: intervalDecision(interval),
    };
  });
}

type CycleFigure = {
  arcs: ArcSeg[];
  nodes: FigureNode[];
  intervals: FigureNode[];
};

function cycleFigure(joinAt: number): CycleFigure {
  return {
    arcs: balloonArcs(joinAt),
    nodes: balloonNodes(joinAt),
    intervals: intervalNodes(joinAt),
  };
}

const CYCLE_FIGURES = new Map(JOIN_SPOTS.map((spot) => [spot, cycleFigure(spot)]));

function figureAt(joinAt: number): CycleFigure {
  return CYCLE_FIGURES.get(joinAt) ?? CYCLE_FIGURES.get(0) ?? cycleFigure(0);
}

type JoinGeom = {
  path: string;
  labelX: number;
  labelY: number;
  color: string;
};

function joinGeom(stem: StemItem[]): JoinGeom {
  const stemLastY = stem.at(-1)?.y ?? JOIN_Y + STEP;
  return {
    path: `M ${CX} ${stemLastY} L ${CX} ${JOIN_Y}`,
    labelX: CX + 36,
    labelY: (stemLastY + JOIN_Y) / 2 + 4,
    color: letterColor(stem.at(-1)?.bead.letter ?? "?"),
  };
}

function RotateCcwIcon() {
  return (
    <svg viewBox="0 0 24 24" className="h-4 w-4" aria-hidden="true">
      <path
        d="M3 12a9 9 0 1 0 3-6.7M3 4v5h5"
        fill="none"
        stroke="currentColor"
        strokeWidth="2"
        strokeLinecap="round"
        strokeLinejoin="round"
      />
    </svg>
  );
}

function RotateCwIcon() {
  return (
    <svg viewBox="0 0 24 24" className="h-4 w-4" aria-hidden="true">
      <path
        d="M21 12a9 9 0 1 1-3-6.7M21 4v5h-5"
        fill="none"
        stroke="currentColor"
        strokeWidth="2"
        strokeLinecap="round"
        strokeLinejoin="round"
      />
    </svg>
  );
}

function SnapIcon() {
  return (
    <svg viewBox="0 0 24 24" className="h-4 w-4" aria-hidden="true">
      <circle
        cx="12"
        cy="12"
        r="3"
        fill="currentColor"
      />
      <path
        d="M12 3v3M12 18v3M3 12h3M18 12h3"
        fill="none"
        stroke="currentColor"
        strokeWidth="2"
        strokeLinecap="round"
      />
    </svg>
  );
}

function LegendBead({
  letter,
  kind,
  label,
}: {
  letter: "O" | "E" | "?";
  kind: "sure" | "count" | "unknown" | "min";
  label?: string;
}) {
  const color = letterColor(letter);
  const filled = kind === "sure" || kind === "min";
  const shown =
    label ??
    (kind === "unknown" ? "?" : kind === "count" ? "≥0" : kind === "sure" || kind === "min" ? "1" : "");
  return (
    <svg viewBox="0 0 22 22" width="22" height="22" className="stem-cycle-legend-swatch" aria-hidden>
      <circle
        cx="11"
        cy="11"
        r="8"
        fill={filled ? color : "#fffdf7"}
        stroke={kind === "min" ? "#1d1914" : filled ? "none" : color}
        strokeWidth={kind === "min" || !filled ? 1.6 : 0}
        strokeDasharray={kind === "count" || kind === "unknown" ? "3 2" : undefined}
      />
      {shown ? (
        <text
          x="11"
          y="15"
          textAnchor="middle"
          fill={filled ? "#fffdf7" : color}
          className="stem-cycle-mono"
          fontSize={shown.length >= 3 ? "7" : "9"}
        >
          {shown}
        </text>
      ) : null}
    </svg>
  );
}

function LegendLink({ pointed }: { pointed?: boolean }) {
  return (
    <svg viewBox="0 0 28 10" width="28" height="10" className="stem-cycle-legend-swatch" aria-hidden>
      {pointed ? (
        <path d="M 2 1.4 L 25 5 L 2 8.6 Z" fill="#1d1914" />
      ) : (
        <line
          x1="2"
          y1="5"
          x2="26"
          y2="5"
          stroke="#1d1914"
          strokeWidth="2.2"
          strokeLinecap="round"
        />
      )}
    </svg>
  );
}

function LegendItem({
  label,
  decision,
  onPick,
  children,
}: {
  label: string;
  decision: string;
  onPick: (id: string) => void;
  children: ReactNode;
}) {
  return (
    <button
      type="button"
      className="stem-cycle-legend-item"
      onClick={() => onPick(decision)}
    >
      {children}
      <span>{label}</span>
    </button>
  );
}

const FigureLegend = memo(function FigureLegend({
  onPick,
}: {
  onPick: (id: string) => void;
}) {
  return (
    <div className="stem-cycle-legend" data-keep-focus>
      <span className="stem-cycle-legend-k">Parity</span>
      <div className="stem-cycle-legend-row">
        <LegendItem label="odd" decision="balloon-parity" onPick={onPick}>
          <LegendBead letter="O" kind="sure" label="" />
        </LegendItem>
        <LegendItem label="even" decision="balloon-parity" onPick={onPick}>
          <LegendBead letter="E" kind="sure" label="" />
        </LegendItem>
      </div>
      <span className="stem-cycle-legend-k">Certainty</span>
      <div className="stem-cycle-legend-row">
        <LegendItem label="plain — sure link (OO, wrap EO)" decision="balloon-links" onPick={onPick}>
          <LegendLink />
        </LegendItem>
        <LegendItem label="pointed — interval, may be empty" decision="balloon-links" onPick={onPick}>
          <LegendLink pointed />
        </LegendItem>
      </div>
      <span className="stem-cycle-legend-k">CycleMin</span>
      <div className="stem-cycle-legend-row">
        <LegendItem label="black ring — CycleMin only" decision="balloon-cut" onPick={onPick}>
          <LegendBead letter="O" kind="min" />
        </LegendItem>
      </div>
      <span className="stem-cycle-legend-k">Beads</span>
      <div className="stem-cycle-legend-row">
        <LegendItem label="filled — sure letter" decision="balloon-fade" onPick={onPick}>
          <LegendBead letter="E" kind="sure" />
        </LegendItem>
        <LegendItem label="hollow — count bound" decision="balloon-fade" onPick={onPick}>
          <LegendBead letter="O" kind="count" />
        </LegendItem>
        <LegendItem label="grey ? — unknown stem" decision="string-grey" onPick={onPick}>
          <LegendBead letter="?" kind="unknown" />
        </LegendItem>
      </div>
    </div>
  );
});

function JoinIconButton({
  label,
  disabled,
  active,
  onClick,
  children,
}: {
  label: string;
  disabled?: boolean;
  active?: boolean;
  onClick: () => void;
  children: ReactNode;
}) {
  return (
    <button
      type="button"
      title={label}
      aria-label={label}
      disabled={disabled}
      className={`grid h-8 w-8 place-items-center rounded-full border ${
        active
          ? "border-deep bg-deep text-card"
          : "border-line bg-card text-ink"
      } disabled:opacity-40`}
      onClick={onClick}
    >
      {children}
    </button>
  );
}

function activate(
  onPick: (() => void) | undefined,
  event: MouseEvent | KeyboardEvent,
) {
  if ("key" in event && event.key !== "Enter" && event.key !== " ") return;
  if ("key" in event) event.preventDefault();
  event.stopPropagation();
  onPick?.();
}

const Bead = memo(function Bead({
  x,
  y,
  bead,
  radius,
  marked,
  caption,
  captionX,
  captionY,
  glyph,
  lit,
  onPick,
}: {
  x: number;
  y: number;
  bead: IdealBead | PaintedBead;
  radius: number;
  marked?: boolean;
  caption?: string;
  captionX?: number;
  captionY?: number;
  glyph?: string;
  lit: boolean;
  onPick?: () => void;
}) {
  const paint = beadPaint(bead);
  const bound = caption === "≥0" || caption?.startsWith("{") ? caption : undefined;
  const shown =
    glyph ?? (bound ?? (bead.letter === "O" || bead.letter === "E" ? "" : bead.letter));
  const note = bound ? undefined : caption;
  const glyphSize = shown.length >= 5 ? "8" : shown.length >= 3 ? "9" : "11";
  const aria =
    bead.letter === "O"
      ? shown
        ? `odd ${shown}`
        : "odd"
      : bead.letter === "E"
        ? shown
          ? `even ${shown}`
          : "even"
        : shown === "?" || !shown
          ? "unknown"
          : `unknown ${shown}`;
  return (
    <g
      className={fadeClass(lit)}
      role={onPick ? "button" : undefined}
      tabIndex={onPick ? 0 : undefined}
      aria-label={onPick ? aria : undefined}
      onClick={onPick ? (event) => activate(onPick, event) : undefined}
      onKeyDown={onPick ? (event) => activate(onPick, event) : undefined}
    >
        <circle
        cx={x}
        cy={y}
        r={radius}
        fill={paint.fill}
        stroke={marked ? "#1d1914" : paint.stroke}
        strokeWidth={paint.dash || marked ? 1.6 : 0}
        strokeDasharray={paint.dash}
      />
      {shown ? (
        <text
          x={x}
          y={y + 4}
          textAnchor="middle"
          fill={paint.text}
          className="stem-cycle-mono"
          fontSize={glyphSize}
        >
          {shown}
        </text>
      ) : null}
      {note ? (
        <text
          x={captionX ?? x}
          y={captionY ?? y + radius + 16}
          textAnchor="middle"
          className="stem-cycle-note"
        >
          {note}
        </text>
      ) : null}
    </g>
  );
});

const CycleLeanPanel = memo(function CycleLeanPanel({
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
      className={`stem-cycle-card ${fadeClass(lit) ?? ""}`}
      onClick={() => onPick("balloon-run")}
    >
      <p className="text-xs uppercase tracking-wide text-muted">
        On the cycle — cycleMin_has_full_odd_even_run_form
      </p>
      <p className="mt-1 font-mono text-sm text-ink">
        {runs ? (
          <>
            w = <Tex>{formatRunWordTex(runs)}</Tex>
            {"  "}
            {formatOddEvenRuns(runs)}
          </>
        ) : (
          <>
            w = <Tex>{String.raw`O^{a_1}E\cdots O^{a_e}E`}</Tex>
            {"  "}
            <Tex>{String.raw`a_1\ge 2,\; a_e\le 1`}</Tex>
          </>
        )}
      </p>
      <p className="mt-1 text-xs text-muted">
        {runs && projected && matchesFill
          ? `Equals toRuns of assembleFill ${formatNecklaceFill(fill!)}. The ring is that bunched projection.`
          : runs
            ? "Interior runs the four-slot ring forgets. The beads are a projection, not assembleFill."
            : "The ring is a projection of this Lean list onto six sure letters. Sure links are launch OO and wrap EO."}
      </p>
    </button>
  );
});

const JoinCard = memo(function JoinCard({
  joinAt,
  lit,
  onPick,
}: {
  joinAt: number;
  lit: boolean;
  onPick: (id: string) => void;
}) {
  const join = idealJoinConfig(joinAt);
  const atCycleMin = join.isValley;
  return (
    <button
      type="button"
      data-keep-focus
      className={`stem-cycle-card ${fadeClass(lit) ?? ""}`}
      onClick={() => onPick("join-seam")}
    >
      <p className="text-xs uppercase tracking-wide text-muted">
        Join at {join.name}
        {atCycleMin ? " — CycleMin cut" : " — same loop, not the CycleMin cut"}
        {join.fillDependent ? " — fill-dependent arrival" : ""}
      </p>
      <p className="mt-1 font-mono text-sm text-ink">
        vertex {join.vertex} · arrives {join.arrival}
        {join.fillDependent ? " (fill-dependent)" : ""} · stem t is{" "}
        {join.stemTerminal === "E" ? "even (forced)" : "unknown"}
      </p>
      <p className="mt-1 text-sm text-ink">
        Cyclic parent: {join.cycleParent}. Stem: {join.stem}.
      </p>
      <ul className="mt-1 list-disc pl-4 text-xs text-muted">
        {join.forbidden.map((item) => (
          <li key={item}>{item}</li>
        ))}
      </ul>
      <p className="mt-1 text-xs text-muted">
        {join.arrivalWhy} {join.lean}. {JOIN_INTERVALS_NOT_STOPS} {JOIN_VS_WORD_ROTATION}
      </p>
    </button>
  );
});

const FigureSvg = memo(function FigureSvg({
  focus,
  joinAt,
  stemMode,
  onPick,
  onClear,
}: {
  focus?: DecisionFocus;
  joinAt: number;
  stemMode: StemDisplayMode;
  onPick: (id: string) => void;
  onClear?: () => void;
}) {
  const stem = stemForJoin(joinAt, stemMode);
  const emptyStem = stem.length === 0;
  const join = joinGeom(stem);
  const cycle = figureAt(joinAt);
  const joinLit = regionLit(focus, "join");
  const joinFocus = focus === "join";
  const atCycleMin = joinAt === 0;
  const joinCfg = idealJoinConfig(joinAt);
  const viewH = emptyStem ? Math.ceil(JOIN_Y + BEAD_R + 16) : VIEW_H;
  const stemTitleY = (stem[0]?.y ?? JOIN_Y) + BEAD_R + 22;

  return (
    <svg
      viewBox={`0 0 ${VIEW_W} ${viewH}`}
      role="img"
      className="stem-cycle-svg mt-1 h-auto w-full"
      onClick={(event) => {
        if ((event.target as Element).closest("[role='button']")) return;
        onClear?.();
      }}
    >
      <title>
        Schematic CycleMin geometry with an optional stem. No nontrivial cycle
        is known. The cycle is a projection of the Lean run list onto six sure
        letters. Plain links are sure (OO, wrap EO). Pointed links are
        interval slots and may be empty.
      </title>
      {emptyStem ? null : (
        <text x={CX} y={stemTitleY} className="stem-cycle-title">
          Stem
        </text>
      )}
      {stem.slice(0, -1).map((item, index) => {
        const next = stem[index + 1];
        const unsure = item.bead.tone !== "sure" || next.bead.tone !== "sure";
        return (
      <line
            key={`stem-link-${index}`}
            x1={item.x}
            y1={item.y}
            x2={next.x}
            y2={next.y}
            stroke={letterColor(item.bead.letter)}
            strokeWidth="2.2"
            strokeLinecap="round"
            strokeDasharray={unsure ? "3 3" : undefined}
            className={fadeClass(regionLit(focus, item.region))}
          />
        );
      })}
      {stem.map((item, index) => (
        <Bead
          key={`stem-${item.region}-${index}`}
          x={item.x}
          y={item.y}
          bead={item.bead}
          radius={BEAD_R}
          caption={item.caption}
          captionX={item.x + BEAD_R + 20}
          captionY={item.y + 4}
          lit={regionLit(focus, item.region)}
          onPick={() => onPick(stemDecision(item.region))}
        />
      ))}
      {cycle.arcs.map((arc) => (
        <g key={arc.key} className={fadeClass(regionLit(focus, arc.region))}>
          {arc.pointed ? (
            <path className="stem-cycle-flow" d={arc.pointed} fill={arc.color} />
          ) : (
            <path
              d={arc.d}
              fill="none"
              stroke={arc.color}
              strokeWidth="2.2"
              strokeLinecap="round"
            />
          )}
          {arc.arrow ? (
            <path
              className="stem-cycle-flow"
              transform={`translate(${arc.arrow.x} ${arc.arrow.y}) rotate(${arc.arrow.deg})`}
              d="M -2.4 -4.2 L 4.9 0 L -2.4 4.2 Z"
              fill={arc.color}
            />
          ) : null}
        </g>
      ))}
      {cycle.intervals.map((node) => (
        <Bead
          key={node.key}
          x={node.x}
          y={node.y}
          bead={node.bead}
          radius={node.radius}
          glyph={node.glyph}
          caption={node.caption}
          captionX={node.captionX}
          captionY={node.captionY}
          lit={regionLit(focus, node.region)}
          onPick={() => onPick(node.decision)}
        />
      ))}
      {emptyStem ? null : (
        <>
          <path
            d={join.path}
            fill="none"
            stroke={join.color}
            strokeWidth="2.2"
            strokeLinecap="round"
            className={fadeClass(joinLit)}
            role="button"
            onClick={(event) => activate(() => onPick("join-seam"), event)}
          />
      <text
            x={join.labelX}
            y={join.labelY}
            textAnchor="start"
            className={`stem-cycle-note stem-cycle-ink ${fadeClass(joinLit) ?? ""}`}
            role="button"
            onClick={(event) => activate(() => onPick("join-seam"), event)}
          >
            {atCycleMin ? "join · CycleMin" : `join · ${joinCfg.name}`}
      </text>
        </>
      )}
      {cycle.nodes.map((node) => {
        const isJoin = node.index === joinAt;
        return (
          <Bead
            key={node.key}
            x={node.x}
            y={node.y}
            bead={node.bead}
            radius={node.radius}
            marked={node.marked}
            glyph={node.glyph}
            caption={node.caption}
            captionX={node.captionX}
            captionY={node.captionY}
            lit={joinFocus ? isJoin : regionLit(focus, node.region)}
            onPick={() => onPick(node.decision)}
          />
        );
      })}
      <text
        x={CX}
        y={CY - R - BEAD_R - 18}
        className="stem-cycle-title"
        role="button"
        onClick={(event) => activate(() => onPick("balloon-run"), event)}
      >
        Idealized cycle
      </text>
    </svg>
  );
});

export const CycleLollipop = memo(function CycleLollipop({
  focus,
  joinIndex = 0,
  word,
  fill = null,
  stemMode = "empty",
  onJoinIndex,
  onSelectDecision,
  onClearFocus,
}: {
  focus?: DecisionFocus;
  joinIndex?: number;
  word?: string;
  fill?: NecklaceFill | null;
  stemMode?: StemDisplayMode;
  onJoinIndex?: (index: number) => void;
  onSelectDecision?: (id: string) => void;
  onClearFocus?: () => void;
}) {
  const joinAt = JOIN_SPOTS.includes(joinIndex) ? joinIndex : 0;
  const pick = useCallback(
    (id: string) => {
      onSelectDecision?.(id);
    },
    [onSelectDecision],
  );

  return (
    <div
      className="stem-cycle rounded-xl border border-line bg-paper/70 px-3 py-3"
      onClick={(event) => {
        if (event.target === event.currentTarget) onClearFocus?.();
      }}
    >
      <div>
        <FigureSvg
          focus={focus}
          joinAt={joinAt}
          stemMode={stemMode}
          onPick={pick}
          onClear={onClearFocus}
        />
        <div
          className="flex items-center gap-1.5"
          style={{
            marginLeft: `${(CX / VIEW_W) * 100}%`,
            transform: "translateX(-50%)",
            width: "max-content",
          }}
        >
          <JoinIconButton
            label="Join left"
            onClick={() => onJoinIndex?.(stepIdealJoin(joinAt, -1, JOIN_SPOTS))}
          >
            <RotateCcwIcon />
          </JoinIconButton>
          <JoinIconButton
            label="Snap join to CycleMin"
            disabled={joinAt === 0}
            active={joinAt === 0}
            onClick={() => onJoinIndex?.(0)}
          >
            <SnapIcon />
          </JoinIconButton>
          <JoinIconButton
            label="Join right"
            onClick={() => onJoinIndex?.(stepIdealJoin(joinAt, 1, JOIN_SPOTS))}
          >
            <RotateCwIcon />
          </JoinIconButton>
        </div>
        <FigureLegend onPick={pick} />
      </div>
      <CycleLeanPanel
        word={word}
        fill={fill}
        lit={!focus || focus === "figure" || focus.startsWith("balloon")}
        onPick={pick}
      />
      {stemMode === "empty" ? null : (
        <JoinCard
          joinAt={joinAt}
          lit={regionLit(focus, "join") || !focus}
          onPick={pick}
        />
      )}
    </div>
  );
});
